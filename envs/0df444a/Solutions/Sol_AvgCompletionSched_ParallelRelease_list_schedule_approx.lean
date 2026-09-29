-- Prove2me | solution 1 for AvgCompletionSched.ParallelRelease.list_schedule_approx
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:15:34.258642+00:00
-- url     : https://prove2.me/submissions/5b8e7717-87ce-4ca3-9c20-0f12052252e8

import Mathlib
import Definitions.Def_AvgCompletionSched_ParallelRelease_Model

namespace AvgCompletionSched.ParallelRelease

open MeasureTheory

/-- One step of the list scheduling recursion, with the chosen machine made explicit. -/
lemma aux_lsa_step {n m : ℕ} (I : Instance n m) (π : Fin n ≃ Fin n) (k : ℕ) (h : k < n) :
    ∃ μ : Fin m, (∀ ν, (listRun I π k).1 μ ≤ (listRun I π k).1 ν) ∧
      listRun I π (k + 1) =
        (Function.update (listRun I π k).1 μ
          (max (max (I.r (π ⟨k, h⟩)) (listRun I π k).2) ((listRun I π k).1 μ) + I.p (π ⟨k, h⟩)),
         max (max (I.r (π ⟨k, h⟩)) (listRun I π k).2) ((listRun I π k).1 μ)) := by
  refine ⟨Classical.choose (Finset.exists_min_image Finset.univ (listRun I π k).1
    ⟨⟨0, I.m_pos⟩, Finset.mem_univ _⟩), fun ν => (Classical.choose_spec
      (Finset.exists_min_image Finset.univ (listRun I π k).1
    ⟨⟨0, I.m_pos⟩, Finset.mem_univ _⟩)).2 ν (Finset.mem_univ _), ?_⟩
  rw [listRun.eq_2, dif_pos h]

/-- Invariant of list scheduling with respect to a threshold `T` that dominates the release
dates of the jobs scheduled so far. -/
lemma aux_lsa_inv {n m : ℕ} (I : Instance n m) (π : Fin n ≃ Fin n) (T : ℝ) (hT0 : 0 ≤ T) :
    ∀ k : ℕ, (∀ i : Fin n, (i : ℕ) < k → I.r (π i) ≤ T) →
      (∀ ν, (listRun I π k).2 ≤ max T ((listRun I π k).1 ν)) ∧
      ∑ ν, max ((listRun I π k).1 ν) T ≤
        m * T + ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), I.p (π i) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun ν => ?_, ?_⟩
    · simp [listRun, hT0]
    · simp [listRun, hT0]
  | succ k ih =>
    intro hr
    obtain ⟨ha, hb⟩ := ih (fun i hi => hr i (by omega))
    by_cases h : k < n
    · obtain ⟨μ, hμ, he⟩ := aux_lsa_step I π k h
      rw [he]
      set f := (listRun I π k).1 with hf
      set L := (listRun I π k).2 with hL
      set j := π ⟨k, h⟩ with hj
      have hrj : I.r j ≤ T := hr ⟨k, h⟩ (by simp)
      have hpj : 0 < I.p j := I.p_pos j
      set s := max (max (I.r j) L) (f μ) with hs_def
      have hs : s ≤ max T (f μ) := by
        have := ha μ
        refine max_le (max_le ?_ this) (le_max_right _ _)
        exact hrj.trans (le_max_left _ _)
      refine ⟨fun ν => ?_, ?_⟩
      · dsimp only
        by_cases hν : ν = μ
        · subst hν
          rw [Function.update_self]
          exact le_max_of_le_right (by linarith)
        · rw [Function.update_of_ne hν]
          exact hs.trans (max_le_max le_rfl (hμ ν))
      · dsimp only
        have e1 : ∑ ν, max (Function.update f μ (s + I.p j) ν) T
            = max (s + I.p j) T + ∑ ν ∈ Finset.univ.erase μ, max (f ν) T := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ μ), Function.update_self]
          congr 1
          apply Finset.sum_congr rfl
          intro ν hν
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hν)]
        have e2 : ∑ ν, max (f ν) T = max (f μ) T + ∑ ν ∈ Finset.univ.erase μ, max (f ν) T :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ μ)).symm
        have hfil : Finset.univ.filter (fun i : Fin n => (i : ℕ) < k + 1)
            = insert ⟨k, h⟩ (Finset.univ.filter (fun i : Fin n => (i : ℕ) < k)) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
          omega
        have hnot : (⟨k, h⟩ : Fin n) ∉ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k) := by
          simp
        rw [hfil, Finset.sum_insert hnot, e1]
        rw [e2] at hb
        have hmx : max (s + I.p j) T ≤ max (f μ) T + I.p j := by
          refine max_le ?_ ?_
          · have : max T (f μ) = max (f μ) T := max_comm _ _
            linarith
          · linarith [le_max_right (f μ) T]
        linarith
    · have he : listRun I π (k + 1) = listRun I π k := by
        rw [listRun.eq_2, dif_neg h]
      rw [he]
      refine ⟨ha, hb.trans ?_⟩
      have : ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), I.p (π i)
          ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k + 1), I.p (π i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        · intro i _ _
          exact (I.p_pos _).le
      linarith

/-- Bound on the start time of the `k`-th job of the list. -/
lemma aux_lsa_start {n m : ℕ} (I : Instance n m) (π : Fin n ≃ Fin n) (k : Fin n) (T : ℝ)
    (hT0 : 0 ≤ T) (hr : ∀ i : Fin n, i ≤ k → I.r (π i) ≤ T) :
    listStart I π (π k) ≤
      T + (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), I.p (π i)) / m := by
  have hm : (0 : ℝ) < m := by exact_mod_cast I.m_pos
  unfold listStart
  rw [Equiv.symm_apply_apply]
  obtain ⟨μ, hμ, he⟩ := aux_lsa_step I π k k.isLt
  obtain ⟨ha, hb⟩ := aux_lsa_inv I π T hT0 k
    (fun i hi => hr i (Fin.le_iff_val_le_val.mpr hi.le))
  rw [he]
  simp only [Fin.eta]
  set f := (listRun I π k).1 with hf
  set L := (listRun I π k).2 with hL
  have hrk : I.r (π k) ≤ T := hr k le_rfl
  have hs : max (max (I.r (π k)) L) (f μ) ≤ max T (f μ) := by
    have := ha μ
    refine max_le (max_le ?_ this) (le_max_right _ _)
    exact hrk.trans (le_max_left _ _)
  have hmin : (m : ℝ) * max (f μ) T ≤ ∑ ν, max (f ν) T := by
    calc (m : ℝ) * max (f μ) T = ∑ _ν : Fin m, max (f μ) T := by simp
    _ ≤ _ := Finset.sum_le_sum (fun ν _ => max_le_max (hμ ν) le_rfl)
  have h2 : max (f μ) T ≤ T +
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), I.p (π i)) / m := by
    rw [← sub_nonneg]
    have h3 : (m : ℝ) * (max (f μ) T) ≤ m * T +
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), I.p (π i) := hmin.trans hb
    have h4 : T + (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), I.p (π i)) / m
        - max (f μ) T = (m * T +
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), I.p (π i)
          - m * max (f μ) T) / m := by
      field_simp
    rw [h4]
    apply div_nonneg _ hm.le
    linarith
  have : max T (f μ) = max (f μ) T := max_comm _ _
  linarith

lemma aux_lsa_done_zero {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) (j : Fin n) (t : ℝ)
    (ht : t ≤ I.r j) : P.done j t = 0 := by
  unfold RelaxSchedule.done
  exact setIntegral_eq_zero_of_forall_eq_zero
    (fun s hs => P.released j s (lt_of_lt_of_le (Set.mem_Iio.mp hs) ht))

lemma aux_lsa_done_total {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) (j : Fin n) (T : ℝ)
    (hT : ∀ t, T ≤ t → P.ρ j t = 0) : P.done j T = I.p j / m := by
  unfold RelaxSchedule.done
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun t ht => hT t (not_lt.mp (by simpa using ht))), P.total j]

lemma aux_lsa_done_mono {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) (j : Fin n)
    {a b : ℝ} (hab : a ≤ b) : P.done j a ≤ P.done j b := by
  unfold RelaxSchedule.done
  exact setIntegral_mono_set (P.integrable j).integrableOn
    (Filter.Eventually.of_forall (fun t => P.nonneg j t))
    (Set.Iio_subset_Iio hab).eventuallyLE

lemma aux_lsa_mem_gt {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) (j : Fin n) (t : ℝ)
    (h : I.p j / m ≤ P.done j t) : I.r j < t := by
  by_contra hc
  push Not at hc
  rw [aux_lsa_done_zero P j t hc] at h
  have : 0 < I.p j / m := div_pos (I.p_pos j) (by exact_mod_cast I.m_pos)
  linarith

lemma aux_lsa_nonempty {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) (j : Fin n) :
    Set.Nonempty {t | I.p j / m ≤ P.done j t} := by
  obtain ⟨T, hT⟩ := P.bounded j
  exact ⟨T, (aux_lsa_done_total P j T hT).ge⟩

lemma aux_lsa_bdd {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) (j : Fin n) :
    BddBelow {t | I.p j / m ≤ P.done j t} :=
  ⟨I.r j, fun t ht => (aux_lsa_mem_gt P j t ht).le⟩

lemma aux_lsa_CP_ge {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) (j : Fin n) :
    I.r j ≤ P.CP j := by
  unfold RelaxSchedule.CP
  exact le_csInf (aux_lsa_nonempty P j) (fun t ht => (aux_lsa_mem_gt P j t ht).le)

lemma aux_lsa_CP_le {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) (j : Fin n) (t : ℝ)
    (ht : I.p j / m ≤ P.done j t) : P.CP j ≤ t :=
  csInf_le (aux_lsa_bdd P j) ht

lemma aux_lsa_exists_lt {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) (j : Fin n) (ε : ℝ)
    (hε : 0 < ε) : ∃ t, t < P.CP j + ε ∧ I.p j / m ≤ P.done j t := by
  have h1 : sInf {t | I.p j / m ≤ P.done j t} < P.CP j + ε := by
    show P.CP j < P.CP j + ε
    linarith
  obtain ⟨t, ht, hlt⟩ := exists_lt_of_csInf_lt (aux_lsa_nonempty P j) h1
  exact ⟨t, hlt, ht⟩

/-- In a relaxation schedule, the jobs of `S` (all completed by time `c`) have total
processing `∑ p_j / m` at most `c`. -/
lemma aux_lsa_sum_le {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) (π : Fin n ≃ Fin n)
    (S : Finset (Fin n)) (c : ℝ) (hc0 : 0 ≤ c) (hc : ∀ i ∈ S, P.CP (π i) ≤ c) :
    ∑ i ∈ S, I.p (π i) / m ≤ c := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hsum : ∑ i ∈ S, I.p (π i) / m ≤ ∑ i ∈ S, P.done (π i) (c + ε) := by
    apply Finset.sum_le_sum
    intro i hi
    obtain ⟨t, ht1, ht2⟩ := aux_lsa_exists_lt P (π i) ε hε
    exact ht2.trans (aux_lsa_done_mono P (π i) (by linarith [hc i hi]))
  refine hsum.trans ?_
  unfold RelaxSchedule.done
  rw [← integral_finsetSum S (fun i _ => (P.integrable (π i)).integrableOn)]
  have hg0 : ∀ s, 0 ≤ ∑ i ∈ S, P.ρ (π i) s :=
    fun s => Finset.sum_nonneg (fun i _ => P.nonneg _ s)
  have hg1 : ∀ s, ∑ i ∈ S, P.ρ (π i) s ≤ 1 := by
    intro s
    calc ∑ i ∈ S, P.ρ (π i) s ≤ ∑ i, P.ρ (π i) s :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
            (fun i _ _ => P.nonneg _ s)
      _ = ∑ j, P.ρ j s := Equiv.sum_comp π (fun j => P.ρ j s)
      _ ≤ 1 := P.capacity s
  have hgz : ∀ s, s < 0 → ∑ i ∈ S, P.ρ (π i) s = 0 :=
    fun s hs => Finset.sum_eq_zero
      (fun i _ => P.released _ s (lt_of_lt_of_le hs (I.r_nonneg _)))
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := Set.Ico 0 (c + ε)) measurableSet_Iio
    (fun s hs => hs.2) (fun s hs => hgz s (by
      rcases hs with ⟨h1, h2⟩
      simp only [Set.mem_Iio, Set.mem_Ico, not_and, not_lt] at h1 h2
      by_contra hc'
      push Not at hc'
      linarith [h2 hc']))]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ico (0 : ℝ) (c + ε))
    (f := fun s => ∑ i ∈ S, P.ρ (π i) s) (C := 1) measure_Ico_lt_top
    (fun s _ => by rw [Real.norm_eq_abs, abs_of_nonneg (hg0 s)]; exact hg1 s)
  rw [Real.volume_real_Ico_of_le (by linarith), one_mul, Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (by linarith)

/-- The preemptive one-machine schedule obtained from a nonpreemptive schedule by processing each
job at rate `1/m` during its execution interval. -/
noncomputable def aux_lsa_Q {n m : ℕ} (I : Instance n m) (N : Schedule I) : RelaxSchedule I where
  ρ j := Set.indicator (Set.Ico (N.S j) (N.C j)) (fun _ => (1 : ℝ) / m)
  measurable j := measurable_const.indicator measurableSet_Ico
  integrable j := by
    rw [integrable_indicator_iff measurableSet_Ico]
    exact integrableOn_const measure_Ico_lt_top.ne
  nonneg j t := Set.indicator_nonneg (fun _ _ => by positivity) t
  capacity t := by
    classical
    have hm : (0 : ℝ) < m := by exact_mod_cast I.m_pos
    simp only [Set.indicator_apply]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ.filter (fun j => t ∈ Set.Ico (N.S j) (N.C j))).card ≤ m := by
      calc _ ≤ (Finset.univ : Finset (Fin m)).card :=
            Finset.card_le_card_of_injOn N.M (fun _ _ => Finset.mem_univ _) ?_
        _ = m := by simp
      intro i hi j hj hij
      by_contra hne
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
        Set.mem_Ico] at hi hj
      unfold Schedule.C at hi hj
      rcases N.noOverlap i j hij hne with h | h <;> linarith [hi.1, hi.2, hj.1, hj.2]
    calc ((Finset.univ.filter (fun j => t ∈ Set.Ico (N.S j) (N.C j))).card : ℝ) * (1 / m)
        ≤ m * (1 / m) := by
          gcongr
      _ = 1 := by field_simp
  released j t ht := Set.indicator_of_notMem (fun h : t ∈ Set.Ico (N.S j) (N.C j) => by
    have := N.released j
    have := h.1
    linarith) _
  total j := by
    have hm : (0 : ℝ) < m := by exact_mod_cast I.m_pos
    rw [integral_indicator measurableSet_Ico, setIntegral_const,
      Real.volume_real_Ico_of_le (by unfold Schedule.C; linarith [I.p_pos j]), smul_eq_mul]
    unfold Schedule.C
    field_simp
    ring
  bounded j := ⟨N.C j, fun t ht => Set.indicator_of_notMem
    (fun h : t ∈ Set.Ico (N.S j) (N.C j) => by
    have := h.2
    linarith) _⟩

lemma aux_lsa_Q_CP {n m : ℕ} (I : Instance n m) (N : Schedule I) (j : Fin n) :
    (aux_lsa_Q I N).CP j ≤ N.C j :=
  aux_lsa_CP_le _ j _ (aux_lsa_done_total _ j (N.C j) (fun t ht => by
    show Set.indicator (Set.Ico (N.S j) (N.C j)) (fun _ => (1 : ℝ) / m) t = 0
    exact Set.indicator_of_notMem (fun h : t ∈ Set.Ico (N.S j) (N.C j) => by
      have := h.2
      linarith) _)).ge

end AvgCompletionSched.ParallelRelease

open AvgCompletionSched.ParallelRelease

theorem solution {n m : ℕ} (I : Instance n m) (P1 : RelaxSchedule I)
    (hP1 : P1.IsOptimal) (π : Fin n ≃ Fin n) (hπ : IsCompletionOrder P1 π)
    (Nstar : Schedule I) :
    ∑ j, listCompletion I π j ≤ (3 - (1 : ℝ) / m) * ∑ j, Nstar.C j := by
  classical
  have hm : (0 : ℝ) < m := by exact_mod_cast I.m_pos
  have hjob : ∀ k : Fin n,
      listCompletion I π (π k) ≤ 2 * P1.CP (π k) + (1 - 1 / (m : ℝ)) * I.p (π k) := by
    intro k
    have hT0 : 0 ≤ P1.CP (π k) := (I.r_nonneg _).trans (aux_lsa_CP_ge P1 _)
    have hr : ∀ i : Fin n, i ≤ k → I.r (π i) ≤ P1.CP (π k) :=
      fun i hi => (aux_lsa_CP_ge P1 _).trans (hπ i k hi)
    have hst := aux_lsa_start I π k _ hT0 hr
    have hsum := aux_lsa_sum_le P1 π (Finset.univ.filter (fun i : Fin n => i ≤ k)) _ hT0
      (fun i hi => hπ i k (by simpa using hi))
    have hfil : Finset.univ.filter (fun i : Fin n => i ≤ k)
        = insert k (Finset.univ.filter (fun i : Fin n => (i : ℕ) < k)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff,
        Fin.le_iff_val_le_val]
      omega
    rw [hfil, Finset.sum_insert (by simp)] at hsum
    rw [Finset.sum_div] at hst
    unfold listCompletion
    have : (1 - 1 / (m : ℝ)) * I.p (π k) = I.p (π k) - I.p (π k) / m := by ring
    linarith
  have hQ : ∑ j, P1.CP j ≤ ∑ j, Nstar.C j :=
    (hP1 (aux_lsa_Q I Nstar)).trans (Finset.sum_le_sum (fun j _ => aux_lsa_Q_CP I Nstar j))
  have hp : ∑ j, I.p j ≤ ∑ j, Nstar.C j :=
    Finset.sum_le_sum (fun j _ => by
      unfold Schedule.C
      linarith [Nstar.released j, I.r_nonneg j])
  have h1m : 0 ≤ 1 - 1 / (m : ℝ) := by
    have : 1 / (m : ℝ) ≤ 1 := by
      rw [div_le_one hm]
      exact_mod_cast I.m_pos
    linarith
  calc ∑ j, listCompletion I π j = ∑ k, listCompletion I π (π k) := (Equiv.sum_comp π _).symm
    _ ≤ ∑ k, (2 * P1.CP (π k) + (1 - 1 / (m : ℝ)) * I.p (π k)) :=
        Finset.sum_le_sum (fun k _ => hjob k)
    _ = 2 * ∑ k, P1.CP (π k) + (1 - 1 / (m : ℝ)) * ∑ k, I.p (π k) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = 2 * ∑ j, P1.CP j + (1 - 1 / (m : ℝ)) * ∑ j, I.p j := by
        rw [Equiv.sum_comp π P1.CP, Equiv.sum_comp π I.p]
    _ ≤ 2 * ∑ j, Nstar.C j + (1 - 1 / (m : ℝ)) * ∑ j, Nstar.C j := by
        gcongr
    _ = (3 - (1 : ℝ) / m) * ∑ j, Nstar.C j := by ring
