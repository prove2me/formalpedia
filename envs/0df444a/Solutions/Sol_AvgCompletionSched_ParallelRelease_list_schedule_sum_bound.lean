-- Prove2me | solution 1 for AvgCompletionSched.ParallelRelease.list_schedule_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:48:52.065656+00:00
-- url     : https://prove2.me/submissions/47651b84-d8a1-4aa7-8822-b7c14fb56782

import Mathlib
import Definitions.Def_AvgCompletionSched_ParallelRelease_Model

namespace AvgCompletionSched.ParallelRelease

open MeasureTheory

theorem aux_lsb_step {n m : ℕ} (I : Instance n m) (π : Fin n ≃ Fin n) (k : ℕ) (h : k < n) :
    ∃ μ : Fin m, (∀ ν, (listRun I π k).1 μ ≤ (listRun I π k).1 ν) ∧
      listRun I π (k+1) =
        (Function.update (listRun I π k).1 μ
          (max (max (I.r (π ⟨k, h⟩)) (listRun I π k).2) ((listRun I π k).1 μ) + I.p (π ⟨k, h⟩)),
         max (max (I.r (π ⟨k, h⟩)) (listRun I π k).2) ((listRun I π k).1 μ)) := by
  refine ⟨Classical.choose
        (Finset.exists_min_image Finset.univ (listRun I π k).1 ⟨⟨0, I.m_pos⟩, Finset.mem_univ _⟩),
    ?_, ?_⟩
  · intro ν
    exact (Classical.choose_spec (Finset.exists_min_image Finset.univ (listRun I π k).1
      ⟨⟨0, I.m_pos⟩, Finset.mem_univ _⟩)).2 ν (Finset.mem_univ _)
  · conv_lhs => rw [listRun]
    rw [dif_pos h]

noncomputable def aux_lsb_P {n m : ℕ} (I : Instance n m) (π : Fin n ≃ Fin n) (k : ℕ) : ℝ :=
  ∑ i : Fin n, if (i : ℕ) < k then I.p (π i) else 0

theorem aux_lsb_P_succ {n m : ℕ} (I : Instance n m) (π : Fin n ≃ Fin n) (k : ℕ) (h : k < n) :
    aux_lsb_P I π (k+1) = aux_lsb_P I π k + I.p (π ⟨k, h⟩) := by
  unfold aux_lsb_P
  have : ∀ i : Fin n, (if (i : ℕ) < k + 1 then I.p (π i) else 0) =
      (if (i : ℕ) < k then I.p (π i) else 0) + (if i = ⟨k, h⟩ then I.p (π i) else 0) := by
    intro i
    by_cases h1 : (i : ℕ) < k
    · have h2 : i ≠ ⟨k, h⟩ := by
        intro e; subst e; simp at h1
      have h3 : (i : ℕ) < k + 1 := by omega
      simp [h1, h2, h3]
    · by_cases h3 : (i : ℕ) = k
      · have h2 : i = ⟨k, h⟩ := Fin.ext h3
        subst h2; simp
      · have h4 : ¬ (i : ℕ) < k + 1 := by omega
        have h2 : i ≠ ⟨k, h⟩ := fun e => h3 (by rw [e])
        simp [h1, h2, h4]
  rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

theorem aux_lsb_r0 (a b A : ℝ) (h : a ≤ max b A) : max (a - A) 0 ≤ max (b - A) 0 := by
  rcases le_total b A with hb | hb
  · rw [max_eq_right hb] at h
    apply max_le
    · linarith [le_max_right (b - A) 0]
    · exact le_max_right _ _
  · rw [max_eq_left hb] at h
    apply max_le
    · linarith [le_max_left (b - A) 0]
    · exact le_max_right _ _

theorem aux_lsb_r1 (a b A p : ℝ) (h : a ≤ max b A) (hp : 0 ≤ p) :
    max (a + p - A) 0 ≤ max (b - A) 0 + p := by
  rcases le_total b A with hb | hb
  · rw [max_eq_right hb] at h
    apply max_le
    · linarith [le_max_right (b - A) 0]
    · linarith [le_max_right (b - A) 0]
  · rw [max_eq_left hb] at h
    apply max_le
    · linarith [le_max_left (b - A) 0]
    · linarith [le_max_right (b - A) 0]

theorem aux_lsb_inv {n m : ℕ} (I : Instance n m) (π : Fin n ≃ Fin n) :
    ∀ k, k ≤ n → ∀ A : ℝ, 0 ≤ A → (∀ i : Fin n, (i : ℕ) < k → I.r (π i) ≤ A) →
      ∑ ν, max (max ((listRun I π k).1 ν) (listRun I π k).2 - A) 0 ≤ aux_lsb_P I π k := by
  intro k
  induction k with
  | zero =>
    intro _ A hA _
    have h0 : listRun I π 0 = (fun _ => 0, 0) := by rw [listRun]
    rw [h0]
    unfold aux_lsb_P
    simp only [max_self, zero_sub, Nat.not_lt_zero, if_false, Finset.sum_const_zero]
    apply Finset.sum_nonpos
    intro ν _
    apply le_of_eq
    exact max_eq_right (by linarith)
  | succ k ih =>
    intro hk A hA hr
    have h : k < n := hk
    obtain ⟨μ, hμ, heq⟩ := aux_lsb_step I π k h
    rw [heq, aux_lsb_P_succ I π k h]
    have ih' := ih (le_of_lt h) A hA (fun i hi => hr i (by omega))
    set f := (listRun I π k).1 with hf
    set L := (listRun I π k).2 with hL
    set j := π ⟨k, h⟩ with hj
    set s := max (max (I.r j) L) (f μ) with hs
    have hrj : I.r j ≤ A := hr ⟨k, h⟩ (by simp)
    have hp := I.p_pos j
    have hsb : ∀ ν, s ≤ max (max (f ν) L) A := fun ν =>
      max_le (max_le (le_max_of_le_right hrj) (le_max_of_le_left (le_max_right _ _)))
        (le_max_of_le_left (le_max_of_le_left (hμ ν)))
    have key : ∀ ν, max (max (Function.update f μ (s + I.p j) ν) s - A) 0 ≤
        max (max (f ν) L - A) 0 + (if ν = μ then I.p j else 0) := by
      intro ν
      by_cases hν : ν = μ
      · subst hν
        simp only [Function.update_self, if_true]
        have : max (s + I.p j) s = s + I.p j := max_eq_left (by linarith)
        rw [this]
        exact aux_lsb_r1 _ _ _ _ (hsb ν) hp.le
      · rw [Function.update_of_ne hν, if_neg hν, add_zero]
        apply aux_lsb_r0
        exact max_le (le_max_of_le_left (le_max_left _ _)) (hsb ν)
    calc ∑ ν, max (max (Function.update f μ (s + I.p j) ν) s - A) 0
        ≤ ∑ ν, (max (max (f ν) L - A) 0 + (if ν = μ then I.p j else 0)) :=
          Finset.sum_le_sum (fun ν _ => key ν)
      _ = ∑ ν, max (max (f ν) L - A) 0 + I.p j := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
          simp
      _ ≤ aux_lsb_P I π k + I.p j := by linarith

theorem aux_lsb_start {n m : ℕ} (I : Instance n m) (π : Fin n ≃ Fin n) (k : ℕ) (h : k < n)
    (A : ℝ) (hA : 0 ≤ A) (hr : ∀ i : Fin n, (i : ℕ) ≤ k → I.r (π i) ≤ A) :
    (listRun I π (k+1)).2 ≤ A + aux_lsb_P I π k / m := by
  obtain ⟨μ, hμ, heq⟩ := aux_lsb_step I π k h
  have ih := aux_lsb_inv I π k h.le A hA (fun i hi => hr i hi.le)
  rw [heq]
  set f := (listRun I π k).1 with hf
  set L := (listRun I π k).2 with hL
  set j := π ⟨k, h⟩ with hj
  set s := max (max (I.r j) L) (f μ) with hs
  show s ≤ A + aux_lsb_P I π k / m
  have hrj : I.r j ≤ A := hr ⟨k, h⟩ le_rfl
  have hm : (0:ℝ) < m := Nat.cast_pos.mpr I.m_pos
  have hsb : ∀ ν, s ≤ max (max (f ν) L) A := fun ν =>
    max_le (max_le (le_max_of_le_right hrj) (le_max_of_le_left (le_max_right _ _)))
      (le_max_of_le_left (le_max_of_le_left (hμ ν)))
  have key : ∀ ν, max (s - A) 0 ≤ max (max (f ν) L - A) 0 := fun ν => aux_lsb_r0 _ _ _ (hsb ν)
  have hsum : (m:ℝ) * max (s - A) 0 ≤ aux_lsb_P I π k := by
    calc (m:ℝ) * max (s - A) 0 = ∑ _ν : Fin m, max (s - A) 0 := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∑ ν, max (max (f ν) L - A) 0 := Finset.sum_le_sum (fun ν _ => key ν)
      _ ≤ _ := ih
  have h2 : s - A ≤ aux_lsb_P I π k / m := by
    rw [le_div_iff₀ hm]
    have := mul_le_mul_of_nonneg_left (le_max_left (s - A) 0) hm.le
    linarith
  linarith

theorem aux_lsb_done_mono {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) (j : Fin n)
    {s t : ℝ} (hst : s ≤ t) : P.done j s ≤ P.done j t := by
  unfold RelaxSchedule.done
  apply setIntegral_mono_set
  · exact (P.integrable j).integrableOn
  · exact ae_of_all _ (fun x => P.nonneg j x)
  · exact (Set.Iio_subset_Iio hst).eventuallyLE

theorem aux_lsb_done_nonneg {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) (j : Fin n)
    (t : ℝ) : 0 ≤ P.done j t := by
  unfold RelaxSchedule.done
  exact integral_nonneg (fun x => P.nonneg j x)

theorem aux_lsb_done_zero {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) (j : Fin n)
    {t : ℝ} (ht : t ≤ I.r j) : P.done j t = 0 := by
  unfold RelaxSchedule.done
  exact setIntegral_eq_zero_of_forall_eq_zero
    (fun x hx => P.released j x (lt_of_lt_of_le hx ht))

theorem aux_lsb_done_large {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) (j : Fin n)
    {T : ℝ} (hT : ∀ t, T ≤ t → P.ρ j t = 0) {t : ℝ} (ht : T ≤ t) :
    P.done j t = I.p j / m := by
  unfold RelaxSchedule.done
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero, P.total j]
  intro x hx
  simp only [Set.mem_Iio, not_lt] at hx
  exact hT x (le_trans ht hx)

theorem aux_lsb_CP_nonempty {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) (j : Fin n) :
    ({t | I.p j / m ≤ P.done j t} : Set ℝ).Nonempty := by
  obtain ⟨T, hT⟩ := P.bounded j
  refine ⟨T, ?_⟩
  simp only [Set.mem_ofPred_eq]
  rw [aux_lsb_done_large P j hT le_rfl]

theorem aux_lsb_r_le_CP {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) (j : Fin n) :
    I.r j ≤ P.CP j := by
  unfold RelaxSchedule.CP
  apply le_csInf (aux_lsb_CP_nonempty P j)
  intro t ht
  by_contra hlt
  push Not at hlt
  have h0 := aux_lsb_done_zero P j hlt.le
  have hpos : 0 < I.p j / m := div_pos (I.p_pos j) (Nat.cast_pos.mpr I.m_pos)
  simp only [Set.mem_ofPred_eq] at ht
  linarith

theorem aux_lsb_done_after_CP {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) (j : Fin n)
    {ε : ℝ} (hε : 0 < ε) : I.p j / m ≤ P.done j (P.CP j + ε) := by
  obtain ⟨t, ht, htlt⟩ := exists_lt_of_csInf_lt (aux_lsb_CP_nonempty P j)
    (lt_add_of_pos_right (P.CP j) hε)
  exact le_trans ht (aux_lsb_done_mono P j htlt.le)

theorem aux_lsb_sum_done_le {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) {x : ℝ}
    (hx : 0 ≤ x) : ∑ j, P.done j x ≤ x := by
  unfold RelaxSchedule.done
  rw [← integral_finsetSum _ (fun j _ => (P.integrable j).integrableOn)]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := Set.Ico 0 x) measurableSet_Iio
    Set.Ico_subset_Iio_self]
  · calc ∫ t in Set.Ico 0 x, ∑ j, P.ρ j t ≤ ∫ t in Set.Ico 0 x, (1:ℝ) := by
          apply setIntegral_mono_on
          · exact (integrable_finsetSum _ (fun j _ => P.integrable j)).integrableOn
          · exact integrableOn_const (by simp [Real.volume_Ico])
          · exact measurableSet_Ico
          · intro t _; exact P.capacity t
      _ = x := by simp [hx]
  · intro t ht
    simp only [Set.mem_sdiff, Set.mem_Iio, Set.mem_Ico, not_and, not_lt] at ht
    have ht0 : t < 0 := by
      by_contra h0
      push Not at h0
      have := ht.2 h0
      linarith [ht.1]
    apply Finset.sum_eq_zero
    intro j _
    exact P.released j t (lt_of_lt_of_le ht0 (I.r_nonneg j))

theorem aux_lsb_Q_le {n m : ℕ} {I : Instance n m} (P1 : RelaxSchedule I) (π : Fin n ≃ Fin n)
    (hπ : IsCompletionOrder P1 π) (k : Fin n) :
    aux_lsb_P I π ((k : ℕ) + 1) / m ≤ P1.CP (π k) := by
  have hm : (0:ℝ) < m := Nat.cast_pos.mpr I.m_pos
  have hCP0 : 0 ≤ P1.CP (π k) := le_trans (I.r_nonneg _) (aux_lsb_r_le_CP P1 _)
  apply le_of_forall_pos_le_add
  intro ε hε
  have hx : 0 ≤ P1.CP (π k) + ε := by linarith
  calc aux_lsb_P I π ((k : ℕ) + 1) / m
        = ∑ i : Fin n, (if (i : ℕ) < (k : ℕ) + 1 then I.p (π i) / m else 0) := by
          unfold aux_lsb_P
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i _
          split_ifs <;> simp
    _ ≤ ∑ i : Fin n, P1.done (π i) (P1.CP (π k) + ε) := by
          apply Finset.sum_le_sum
          intro i _
          split_ifs with hi
          · have hik : i ≤ k := Fin.le_def.mpr (by omega)
            calc I.p (π i) / m ≤ P1.done (π i) (P1.CP (π i) + ε) :=
                  aux_lsb_done_after_CP P1 _ hε
              _ ≤ _ := aux_lsb_done_mono P1 _ (by linarith [hπ i k hik])
          · exact aux_lsb_done_nonneg P1 _ _
    _ = ∑ j, P1.done j (P1.CP (π k) + ε) :=
          Equiv.sum_comp π (fun j => P1.done j (P1.CP (π k) + ε))
    _ ≤ P1.CP (π k) + ε := aux_lsb_sum_done_le P1 hx

theorem aux_lsb_pointwise {n m : ℕ} (I : Instance n m) (P1 : RelaxSchedule I)
    (π : Fin n ≃ Fin n) (hπ : IsCompletionOrder P1 π) (k : Fin n) :
    listCompletion I π (π k) ≤ 2 * P1.CP (π k) + (1 - (1:ℝ) / m) * I.p (π k) := by
  have hm : (0:ℝ) < m := Nat.cast_pos.mpr I.m_pos
  have hS : listStart I π (π k) = (listRun I π ((k : ℕ) + 1)).2 := by
    simp [listStart]
  have hCP0 : 0 ≤ P1.CP (π k) := le_trans (I.r_nonneg _) (aux_lsb_r_le_CP P1 _)
  have hr : ∀ i : Fin n, (i : ℕ) ≤ k → I.r (π i) ≤ P1.CP (π k) := fun i hi =>
    le_trans (aux_lsb_r_le_CP P1 _) (hπ i k (Fin.le_def.mpr hi))
  have h1 := aux_lsb_start I π k k.isLt (P1.CP (π k)) hCP0 hr
  have hQ := aux_lsb_P_succ I π k k.isLt
  simp only [Fin.eta] at hQ
  have hQle := aux_lsb_Q_le P1 π hπ k
  unfold listCompletion
  rw [hS]
  have e1 : (1 - (1:ℝ) / m) * I.p (π k) = I.p (π k) - I.p (π k) / m := by
    field_simp
  have e2 : aux_lsb_P I π ((k : ℕ) + 1) / m = aux_lsb_P I π k / m + I.p (π k) / m := by
    rw [hQ, add_div]
  rw [e1]
  linarith

end AvgCompletionSched.ParallelRelease

open AvgCompletionSched.ParallelRelease

theorem solution {n m : ℕ} (I : Instance n m) (P1 : RelaxSchedule I)
    (π : Fin n ≃ Fin n) (hπ : IsCompletionOrder P1 π) :
    ∑ j, listCompletion I π j ≤
      2 * ∑ j, P1.CP j + (1 - (1 : ℝ) / m) * ∑ j, I.p j := by
  calc ∑ j, listCompletion I π j = ∑ k, listCompletion I π (π k) :=
        (Equiv.sum_comp π (listCompletion I π)).symm
    _ ≤ ∑ k, (2 * P1.CP (π k) + (1 - (1:ℝ) / m) * I.p (π k)) :=
        Finset.sum_le_sum (fun k _ => aux_lsb_pointwise I P1 π hπ k)
    _ = 2 * ∑ k, P1.CP (π k) + (1 - (1:ℝ) / m) * ∑ k, I.p (π k) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = 2 * ∑ j, P1.CP j + (1 - (1 : ℝ) / m) * ∑ j, I.p j := by
        rw [Equiv.sum_comp π (fun j => P1.CP j), Equiv.sum_comp π (fun j => I.p j)]
