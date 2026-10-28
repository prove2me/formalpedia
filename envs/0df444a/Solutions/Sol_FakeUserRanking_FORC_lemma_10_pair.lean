-- Prove2me | solution 1 for FakeUserRanking.FORC.lemma_10_pair
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T07:53:38.92039+00:00
-- url     : https://prove2.me/submissions/1adbfc46-e217-48f3-a884-bbd0dc7bdfd9

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent
import Theorems.Thm_FakeUserRanking_FORC_lemma_10_high_levels
import Theorems.Thm_FakeUserRanking_FORC_lemma_16_low_levels

set_option autoImplicit false

open FakeUserRanking.FORC

namespace SolLemma10Pair

variable {n L T : ℕ}

lemma S_eq (L : ℕ) : ∑ m ∈ Finset.Ico 1 L, (1 / 2 : ℝ) ^ (m + 1) =
    ∑ i ∈ Finset.range (L - 1), (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ i := by
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [show 1 + i + 1 = i + 2 by ring, pow_add]
  norm_num
  ring

lemma S_le (L : ℕ) : ∑ m ∈ Finset.Ico 1 L, (1 / 2 : ℝ) ^ (m + 1) ≤ 1 / 2 := by
  rw [S_eq, ← Finset.mul_sum]
  have := sum_geometric_two_le (L - 1)
  linarith

lemma levelW_nonneg (L : ℕ) (k : Fin L) : 0 ≤ levelW L k := by
  unfold levelW
  split_ifs
  · linarith [S_le L]
  · positivity

lemma levelW_sum (L : ℕ) (hL : 1 ≤ L) : ∑ k : Fin L, levelW L k = 1 := by
  unfold levelW
  rw [Fin.sum_univ_eq_sum_range (fun m => if m = 0 then 1 - ∑ m ∈ Finset.Ico 1 L, (1 / 2 : ℝ) ^ (m + 1)
    else (1 / 2 : ℝ) ^ (m + 1)) L]
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  rw [Finset.sum_range_succ']
  simp only [Nat.add_one_ne_zero, if_false, if_true]
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  have : ∀ i ∈ Finset.range L', (1 / 2 : ℝ) ^ (1 + i + 1) = (1 / 2 : ℝ) ^ (i + 1 + 1) := by
    intro i _; rw [show 1 + i + 1 = i + 1 + 1 by ring]
  rw [Finset.sum_congr rfl this]
  ring

lemma realW_nonneg (inst : Instance n) (π : Equiv.Perm (Fin n)) (o : Obs n) :
    0 ≤ realW inst π o := by
  rcases o with ⟨j, b⟩
  have h1 : 0 ≤ reach inst π j := by
    unfold reach
    apply mul_nonneg <;> apply Finset.prod_nonneg <;> intro r _
    · linarith [(inst.q_mem r).2]
    · linarith [(inst.μ_mem (π r)).2]
  have h2 := (inst.μ_mem (π j)).1
  have h3 := (inst.μ_mem (π j)).2
  have h4 := (inst.q_mem j).1
  cases b
  · simp only [realW]
    apply mul_nonneg (mul_nonneg h1 (by linarith))
    split_ifs <;> linarith
  · simp only [realW]; exact mul_nonneg h1 h2

lemma obsW_nonneg (inst : Instance n) (π : Equiv.Perm (Fin n)) (a : Action n) (o : Obs n) :
    0 ≤ obsW inst π a o := by
  cases a with
  | none => exact realW_nonneg inst π o
  | some a => simp only [obsW]; split_ifs <;> norm_num

lemma stepW_nonneg (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (τ : Fin T → Step n L) (s : Fin T) :
    0 ≤ stepW inst P A τ s := by
  unfold stepW
  exact mul_nonneg (mul_nonneg (hw_nonneg _ _) ENNReal.toReal_nonneg) (obsW_nonneg _ _ _ _)

lemma trajW_nonneg (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (τ : Fin T → Step n L) :
    0 ≤ trajW inst P A T τ :=
  Finset.prod_nonneg (fun s _ => stepW_nonneg inst P A hw_nonneg τ s)

noncomputable def rho (inst : Instance n) (π : Equiv.Perm (Fin n)) (m : ℕ) : ℝ :=
  if h : m < n then reach inst π ⟨m, h⟩ else 0

lemma reach_succ (inst : Instance n) (π : Equiv.Perm (Fin n)) (m : ℕ) (h : m + 1 < n) :
    reach inst π ⟨m + 1, h⟩ = reach inst π ⟨m, by omega⟩ *
      ((1 - inst.q ⟨m, by omega⟩) * (1 - inst.μ (π ⟨m, by omega⟩))) := by
  unfold reach
  have hI : Finset.Iio (⟨m + 1, h⟩ : Fin n) = insert ⟨m, by omega⟩ (Finset.Iio ⟨m, by omega⟩) := by
    ext r; simp only [Finset.mem_Iio, Finset.mem_insert, Fin.lt_def, Fin.ext_iff]; omega
  rw [hI, Finset.prod_insert (by simp), Finset.prod_insert (by simp)]
  ring

lemma reach_zero (inst : Instance n) (π : Equiv.Perm (Fin n)) (h : 0 < n) :
    reach inst π ⟨0, h⟩ = 1 := by
  unfold reach
  have hI : Finset.Iio (⟨0, h⟩ : Fin n) = ∅ := by
    ext r; simp [Fin.lt_def]
  simp [hI]

lemma realW_pair (inst : Instance n) (π : Equiv.Perm (Fin n)) (j : Fin n) :
    realW inst π (j, true) + realW inst π (j, false) = rho inst π j - rho inst π (j + 1) := by
  simp only [realW, rho, dif_pos j.isLt]
  by_cases h : (j : ℕ) + 1 < n
  · rw [dif_pos h, if_pos h, reach_succ inst π j h]
    ring
  · rw [dif_neg h, if_neg h]; ring

lemma realW_sum (inst : Instance n) (π : Equiv.Perm (Fin n)) (hn : 1 ≤ n) :
    ∑ o, realW inst π o = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, realW_pair]
  rw [Fin.sum_univ_eq_sum_range (fun m => rho inst π m - rho inst π (m + 1)) n]
  rw [Finset.sum_range_sub']
  simp [rho, dif_pos (show 0 < n by omega), reach_zero inst π (show 0 < n by omega)]

lemma obsW_sum (inst : Instance n) (π : Equiv.Perm (Fin n)) (a : Action n) (hn : 1 ≤ n) :
    ∑ o, obsW inst π a o = 1 := by
  cases a with
  | none => exact realW_sum inst π hn
  | some a => simp [obsW]

lemma pmf_sum (p : PMF (Action n)) : ∑ a, (p a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top p a)]
  rw [← tsum_fintype (L := SummationFilter.unconditional _), PMF.tsum_coe]; simp

def DepBelow (m : ℕ) {β : Type*} (f : (Fin T → Step n L) → β) : Prop :=
  ∀ τ τ' : Fin T → Step n L, (∀ i : Fin T, (i : ℕ) < m → τ i = τ' i) → f τ = f τ'

lemma algHist_dep (s : ℕ) : DepBelow (T := T) (n := n) (L := L) s (fun τ => algHist τ s) := by
  intro τ τ' h
  beta_reduce
  unfold algHist
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]
    apply h
    simp at h1; simp; omega

lemma ranking_dep (A : Alg n L) (s : Fin T) :
    DepBelow (s + 1) (fun τ => ranking A τ s) := by
  intro τ τ' h
  beta_reduce
  unfold ranking
  have e := algHist_dep (n := n) (L := L) s τ τ' (fun i hi => h i (by omega))
  beta_reduce at e
  rw [e, h s (by omega)]

lemma pubHist_dep (A : Alg n L) (s : ℕ) : DepBelow (T := T) s (fun τ => pubHist A τ s) := by
  intro τ τ' h
  beta_reduce
  unfold pubHist
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]
    simp at h1
    have e := ranking_dep A ⟨i, by omega⟩ τ τ' (fun j hj => h j (by simp at hj; omega))
    beta_reduce at e
    rw [e, h ⟨i, by omega⟩ (by simp; omega)]

lemma stepW_dep (inst : Instance n) (P : Adversary n) (A : Alg n L) (s : Fin T) :
    DepBelow (s + 1) (fun τ => stepW inst P A τ s) := by
  intro τ τ' h
  beta_reduce
  unfold stepW
  have e1 := algHist_dep (n := n) (L := L) s τ τ' (fun i hi => h i (by omega))
  have e2 := pubHist_dep A s τ τ' (fun i hi => h i (by omega))
  have e3 := ranking_dep A s τ τ' h
  beta_reduce at e1 e2 e3
  rw [e1, e2, e3, h s (by omega)]

lemma update_agree (τ : Fin T → Step n L) (m : Fin T) (x : Step n L) :
    ∀ i : Fin T, (i : ℕ) < m → Function.update τ m x i = τ i := by
  intro i hi
  exact Function.update_of_ne (by intro h; rw [h] at hi; exact lt_irrefl _ hi) _ _

noncomputable def Wm (inst : Instance n) (P : Adversary n) (A : Alg n L) (m : ℕ)
    (τ : Fin T → Step n L) : ℝ :=
  ∏ s : Fin T, if (s : ℕ) < m then stepW inst P A τ s else (Fintype.card (Step n L) : ℝ)⁻¹

noncomputable def Em (inst : Instance n) (P : Adversary n) (A : Alg n L) (m : ℕ)
    (g : (Fin T → Step n L) → ℝ) : ℝ :=
  ∑ τ, Wm inst P A m τ * g τ

lemma sum_update_eq {α : Type*} [Fintype α] [DecidableEq α] (F : (Fin T → α) → ℝ) (m : Fin T) :
    ∑ τ, ∑ x, F (Function.update τ m x) = (Fintype.card α : ℝ) * ∑ τ, F τ := by
  let Φ : (Fin T → α) × α → (Fin T → α) × α := fun p => (Function.update p.1 m p.2, p.1 m)
  have hΦ : Function.Involutive Φ := by
    intro p; simp [Φ]
  calc ∑ τ, ∑ x, F (Function.update τ m x) = ∑ p : (Fin T → α) × α, F (Φ p).1 := by
        rw [Fintype.sum_prod_type]
    _ = ∑ p : (Fin T → α) × α, F p.1 :=
        Fintype.sum_equiv (hΦ.toPerm Φ) _ _ (fun p => rfl)
    _ = _ := by
        rw [Fintype.sum_prod_type]
        simp [Finset.sum_const, Finset.mul_sum]

lemma Wm_update (inst : Instance n) (P : Adversary n) (A : Alg n L) (m : Fin T)
    (τ : Fin T → Step n L) (x : Step n L) (hN : (0 : ℝ) < Fintype.card (Step n L)) :
    Wm inst P A (m + 1) (Function.update τ m x) =
      (Fintype.card (Step n L) : ℝ) * Wm inst P A m τ * stepW inst P A (Function.update τ m x) m := by
  unfold Wm
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ m),
    ← Finset.mul_prod_erase Finset.univ (fun s : Fin T => if (s : ℕ) < m then stepW inst P A τ s
      else (Fintype.card (Step n L) : ℝ)⁻¹) (Finset.mem_univ m)]
  simp only [lt_add_iff_pos_right, lt_irrefl, if_false, Nat.lt_succ_self, if_true]
  have hrest : ∏ s ∈ Finset.univ.erase m, (if (s : ℕ) < (m : ℕ) + 1 then
      stepW inst P A (Function.update τ m x) s else (Fintype.card (Step n L) : ℝ)⁻¹) =
      ∏ s ∈ Finset.univ.erase m, (if (s : ℕ) < m then stepW inst P A τ s
        else (Fintype.card (Step n L) : ℝ)⁻¹) := by
    apply Finset.prod_congr rfl
    intro s hs
    have hsm : s ≠ m := Finset.ne_of_mem_erase hs
    have hsm' : (s : ℕ) ≠ m := fun h => hsm (Fin.ext h)
    by_cases hlt : (s : ℕ) < m
    · rw [if_pos (by omega), if_pos hlt]
      have e := stepW_dep inst P A s _ _ (fun i hi => update_agree τ m x i (by omega))
      beta_reduce at e
      exact e
    · rw [if_neg (by omega), if_neg hlt]
  rw [hrest]
  field_simp

lemma Em_step (inst : Instance n) (P : Adversary n) (A : Alg n L) (m : Fin T)
    (g : (Fin T → Step n L) → ℝ) (hN : (0 : ℝ) < Fintype.card (Step n L)) :
    Em inst P A (m + 1) g = Em inst P A m (fun τ => ∑ x, stepW inst P A (Function.update τ m x) m *
      g (Function.update τ m x)) := by
  unfold Em
  have := sum_update_eq (fun τ => Wm inst P A (m + 1) τ * g τ) m
  have e : ∑ τ, Wm inst P A (m + 1) τ * g τ =
      (Fintype.card (Step n L) : ℝ)⁻¹ * ∑ τ, ∑ x, Wm inst P A (m + 1) (Function.update τ m x) *
        g (Function.update τ m x) := by
    rw [this]; field_simp
  rw [e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Wm_update inst P A m τ x hN]
  field_simp

lemma stepW_update (inst : Instance n) (P : Adversary n) (A : Alg n L) (m : Fin T)
    (τ : Fin T → Step n L) (x : Step n L) :
    stepW inst P A (Function.update τ m x) m = A.w (algHist τ m) x.1 *
      (P (pubHist A τ m) x.2.1).toReal * obsW inst (A.rank (algHist τ m) x.1) x.2.1 x.2.2 := by
  unfold stepW ranking
  have e1 := algHist_dep (n := n) (L := L) m _ τ (update_agree τ m x)
  have e2 := pubHist_dep A m _ τ (update_agree τ m x)
  beta_reduce at e1 e2
  rw [Function.update_self, e1, e2]

lemma stepW_sum (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n) (m : Fin T) (τ : Fin T → Step n L) :
    ∑ x, stepW inst P A (Function.update τ m x) m = 1 := by
  simp only [stepW_update]
  rw [Fintype.sum_prod_type]
  refine (Finset.sum_congr rfl (fun k _ => ?_)).trans (hw_sum (algHist τ m))
  rw [Fintype.sum_prod_type]
  simp only [mul_assoc, ← Finset.mul_sum, obsW_sum inst _ _ hn, mul_one]
  rw [pmf_sum, mul_one]

lemma Em_drop_const (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n) (hN : (0 : ℝ) < Fintype.card (Step n L))
    (m : Fin T) (c : ℝ) :
    Em inst P A (T := T) (m + 1) (fun _ => c) = Em inst P A (T := T) m (fun _ => c) := by
  rw [Em_step inst P A m (fun _ => c) hN]
  congr 1
  funext τ
  simp only [← Finset.sum_mul, stepW_sum inst P A hw_sum hn m τ, one_mul]

lemma Em_zero_one (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hN : (0 : ℝ) < Fintype.card (Step n L)) :
    Em inst P A (T := T) 0 (fun _ => 1) = 1 := by
  unfold Em Wm
  simp only [Nat.not_lt_zero, if_false, mul_one, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.sum_const, nsmul_eq_mul, Fintype.card_fun, Nat.cast_pow]
  rw [← mul_pow, mul_inv_cancel₀ hN.ne', one_pow]

lemma expect_one (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n) (hL : 1 ≤ L) :
    expect inst P A T (fun _ => 1) = 1 := by
  have hN : (0 : ℝ) < Fintype.card (Step n L) := by
    have : Nonempty (Step n L) := ⟨(⟨0, hL⟩, none, (⟨0, hn⟩, true))⟩
    exact_mod_cast Fintype.card_pos
  have hT : expect inst P A T (fun _ => 1) = Em (T := T) inst P A T (fun _ => 1) := by
    unfold expect Em trajW Wm
    apply Finset.sum_congr rfl; intro τ _; congr 1
    apply Finset.prod_congr rfl; intro s _; rw [if_pos s.isLt]
  rw [hT]
  have key : ∀ m, m ≤ T → Em inst P A (T := T) m (fun _ => 1) = 1 := by
    intro m
    induction m with
    | zero => intro _; exact Em_zero_one inst P A hN
    | succ m ih =>
      intro hm
      have := Em_drop_const inst P A hw_sum hn hN (⟨m, by omega⟩ : Fin T) 1
      simp only at this
      rw [this, ih (by omega)]
  exact key T le_rfl

lemma expect_le_const (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (hw_sum : ∀ h, ∑ k, A.w h k = 1)
    (hn : 1 ≤ n) (hL : 1 ≤ L) (g : (Fin T → Step n L) → ℝ) (B : ℝ)
    (hg : ∀ τ, g τ ≤ B) :
    expect inst P A T g ≤ B := by
  calc expect inst P A T g
      ≤ expect inst P A T (fun _ => B) := by
        unfold expect
        apply Finset.sum_le_sum
        intro τ _
        exact mul_le_mul_of_nonneg_left (hg τ) (trajW_nonneg inst P A hw_nonneg τ)
    _ = B * expect inst P A T (fun _ => 1) := by
        unfold expect
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro τ _; ring
    _ = B := by rw [expect_one inst P A hw_sum hn hL, mul_one]

open Classical in
lemma high_pathwise_bound (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (htb : ∀ h k S, S.Nonempty → tb h k S ∈ S)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (j i : Fin n) (hji : j < i) (τ : Fin T → Step n (numLevels T)) :
    (if goodEvent inst F tb fb τ then 1 else 0) *
      (∑ t : Fin T, if F ≤ 2 ^ (((τ t).1 : ℕ) + 1) ∧
        feedbackEvent (forc n T tb fb) τ t j i then (1 : ℝ) else 0) ≤
      (numLevels T : ℝ) * (gamma T inst j i + 1) := by
  have hA : 0 ≤ Real.log (4 * (n : ℝ) * T / delta n T) := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hT' : (2 : ℝ) ≤ T := by exact_mod_cast hT
    have e1 : 4 * (n : ℝ) * T / delta n T = 4 * (n : ℝ) ^ 4 * (T : ℝ) ^ 2 := by
      unfold delta; field_simp
    rw [e1]
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hn'
    nlinarith
  have hγ_nonneg : 0 ≤ gamma T inst j i := by
    unfold gamma; positivity
  by_cases hG : goodEvent inst F tb fb τ
  · rw [if_pos hG, one_mul]
    have hdecomp : ∀ t : Fin T,
        (if F ≤ 2 ^ (((τ t).1 : ℕ) + 1) ∧ feedbackEvent (forc n T tb fb) τ t j i then (1 : ℝ) else 0) =
        ∑ k : Fin (numLevels T),
          if (τ t).1 = k then
            (if F ≤ 2 ^ ((k : ℕ) + 1) ∧ feedbackEvent (forc n T tb fb) τ t j i then (1 : ℝ) else 0)
          else 0 := by
      intro t
      rw [Finset.sum_ite_eq Finset.univ (τ t).1]
      simp
    simp_rw [hdecomp]
    rw [Finset.sum_comm]
    calc (∑ k : Fin (numLevels T), ∑ t : Fin T,
            if (τ t).1 = k then
              (if F ≤ 2 ^ ((k : ℕ) + 1) ∧ feedbackEvent (forc n T tb fb) τ t j i then (1 : ℝ) else 0)
            else 0)
        ≤ ∑ _k : Fin (numLevels T), (gamma T inst j i + 1) := by
          apply Finset.sum_le_sum
          intro k _
          by_cases hk : F ≤ 2 ^ ((k : ℕ) + 1)
          · have hrew : (∑ t : Fin T,
                if (τ t).1 = k then
                  (if F ≤ 2 ^ ((k : ℕ) + 1) ∧ feedbackEvent (forc n T tb fb) τ t j i then (1 : ℝ) else 0)
                else 0) =
              ∑ t : Fin T, if (τ t).1 = k ∧ feedbackEvent (forc n T tb fb) τ t j i then (1 : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro t _
              by_cases h1 : (τ t).1 = k <;> by_cases h2 : feedbackEvent (forc n T tb fb) τ t j i <;>
                simp [h1, h2, hk]
            rw [hrew]
            exact lemma_10_high_levels n T F hn hT inst hμ tb htb fb τ hG j i hji k hk
          · have hzero : (∑ t : Fin T,
                if (τ t).1 = k then
                  (if F ≤ 2 ^ ((k : ℕ) + 1) ∧ feedbackEvent (forc n T tb fb) τ t j i then (1 : ℝ) else 0)
                else 0) = 0 := by
              apply Finset.sum_eq_zero
              intro t _
              simp [hk]
            rw [hzero]
            linarith
      _ = (numLevels T : ℝ) * (gamma T inst j i + 1) := by
          simp [Finset.sum_const, nsmul_eq_mul]; ring
  · rw [if_neg hG, zero_mul]
    positivity

lemma numLevels_le_four_log (T : ℕ) (hT : 2 ≤ T) :
    (numLevels T : ℝ) ≤ 4 * Real.log T := by
  have hT' : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hexp_half : Real.exp (1 / 2) ≤ 2 := by
    have h1 := Real.add_one_le_exp (-(1 / 2 : ℝ))
    have h2 : Real.exp (-(1 / 2 : ℝ)) * Real.exp (1 / 2) = 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    calc (1 / 2 : ℝ) = Real.log (Real.exp (1 / 2)) := (Real.log_exp _).symm
      _ ≤ Real.log 2 := Real.log_le_log (Real.exp_pos _) hexp_half
  have hlogT : (1 / 2 : ℝ) ≤ Real.log T :=
    le_trans hlog2 (Real.log_le_log (by norm_num) hT')
  have hL : 1 ≤ numLevels T := Nat.clog_pos (by norm_num) (by omega)
  have hpow : 2 ^ (numLevels T - 1) < T :=
    (Nat.lt_clog_iff_pow_lt (by norm_num)).mp (show numLevels T - 1 < numLevels T by omega)
  have hpow' : (2 : ℝ) ^ (numLevels T - 1) ≤ T := by exact_mod_cast hpow.le
  have hlog_pow : ((numLevels T - 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log T := by
    have := Real.log_le_log (by positivity) hpow'
    rwa [Real.log_pow] at this
  have hL1_nonneg : (0 : ℝ) ≤ ((numLevels T - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hL1_le : ((numLevels T - 1 : ℕ) : ℝ) ≤ 2 * Real.log T := by
    nlinarith
  have hcast : (numLevels T : ℝ) = ((numLevels T - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel hL).symm
  linarith

lemma gamma_add_one_le (n T : ℕ) (hn : 2 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ) (j i : Fin n) (hji : j < i) :
    gamma T inst j i + 1 ≤ 321 * (Real.log ((n : ℝ) * T) / gap inst j i ^ 2) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hT' : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hgap_pos : 0 < gap inst j i := by unfold gap; have := hμ hji; linarith
  have hgap_le : gap inst j i ≤ 1 := by
    unfold gap; linarith [(inst.μ_mem j).2, (inst.μ_mem i).1]
  have hgap2_pos : 0 < gap inst j i ^ 2 := by positivity
  have hgap2_le : gap inst j i ^ 2 ≤ 1 := by nlinarith
  have hexp_half : Real.exp (1 / 2) ≤ 2 := by
    have h1 := Real.add_one_le_exp (-(1 / 2 : ℝ))
    have h2 : Real.exp (-(1 / 2 : ℝ)) * Real.exp (1 / 2) = 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  have hexp1 : Real.exp 1 ≤ (n : ℝ) * T := by
    have h1 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  have hlog_nT : 1 ≤ Real.log ((n : ℝ) * T) := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log ((n : ℝ) * T) := Real.log_le_log (Real.exp_pos 1) hexp1
  have hone_le : 1 ≤ Real.log ((n : ℝ) * T) / gap inst j i ^ 2 := by
    rw [one_le_div hgap2_pos]
    linarith
  have e1 : 4 * (n : ℝ) * T / delta n T = 4 * (n : ℝ) ^ 4 * (T : ℝ) ^ 2 := by
    unfold delta; field_simp
  have hpow5 : 4 * (n : ℝ) ^ 4 * (T : ℝ) ^ 2 ≤ ((n : ℝ) * T) ^ 5 := by
    have h4 : (4 : ℝ) ≤ (n : ℝ) * (T : ℝ) ^ 3 := by
      have : (8 : ℝ) ≤ (T : ℝ) ^ 3 := by nlinarith
      nlinarith
    have hnn : 0 ≤ (n : ℝ) ^ 4 * (T : ℝ) ^ 2 := by positivity
    calc 4 * (n : ℝ) ^ 4 * (T : ℝ) ^ 2
        = 4 * ((n : ℝ) ^ 4 * (T : ℝ) ^ 2) := by ring
      _ ≤ ((n : ℝ) * (T : ℝ) ^ 3) * ((n : ℝ) ^ 4 * (T : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right h4 hnn
      _ = ((n : ℝ) * T) ^ 5 := by ring
  have hlog5 : Real.log (4 * (n : ℝ) * T / delta n T) ≤ 5 * Real.log ((n : ℝ) * T) := by
    rw [e1]
    calc Real.log (4 * (n : ℝ) ^ 4 * (T : ℝ) ^ 2)
        ≤ Real.log (((n : ℝ) * T) ^ 5) := Real.log_le_log (by positivity) hpow5
      _ = 5 * Real.log ((n : ℝ) * T) := by rw [Real.log_pow]; ring
  have hγ_le : gamma T inst j i ≤ 320 * (Real.log ((n : ℝ) * T) / gap inst j i ^ 2) := by
    unfold gamma
    rw [show 320 * (Real.log ((n : ℝ) * T) / gap inst j i ^ 2) =
      (64 * (5 * Real.log ((n : ℝ) * T))) / gap inst j i ^ 2 by ring]
    exact div_le_div_of_nonneg_right (by linarith) hgap2_pos.le
  linarith

end SolLemma10Pair

open Classical in
theorem solution :
    ∃ C : ℝ, ∀ (n T F : ℕ), 1 ≤ n → 2 ≤ T →
      ∀ (inst : Instance n), StrictAnti inst.μ →
      ∀ (P : Adversary n), WithinBudget F P →
      ∀ (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n),
        (∀ h k S, S.Nonempty → tb h k S ∈ S) →
      ∀ (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n)),
      ∀ (j i : Fin n), j < i →
        expect inst P (forc n T tb fb) T
          (fun τ => (if goodEvent inst F tb fb τ then 1 else 0) *
            ∑ t : Fin T, (if feedbackEvent (forc n T tb fb) τ t j i then 1 else 0)) ≤
          C * (((n : ℝ) ^ 2 * F + Real.log T) *
            (Real.log ((n : ℝ) * T) / gap inst j i ^ 2)) := by
  obtain ⟨C_low, hC_low⟩ := lemma_16_low_levels
  refine ⟨max C_low 0 + 1284, fun n T F hn hT inst hμ P hP tb htb fb j i hji => ?_⟩
  set A := forc n T tb fb
  have hn2 : 2 ≤ n := by
    have hj := j.isLt
    have hi := i.isLt
    have hji' : (j : ℕ) < (i : ℕ) := Fin.lt_def.mp hji
    omega
  have hL : 1 ≤ numLevels T := Nat.clog_pos (by norm_num) (by omega)
  have hw_nonneg : ∀ h k, 0 ≤ A.w h k := fun _ k => SolLemma10Pair.levelW_nonneg _ k
  have hw_sum : ∀ h, ∑ k, A.w h k = 1 := fun _ => SolLemma10Pair.levelW_sum _ hL
  have hsplit : expect inst P A T
      (fun τ => (if goodEvent inst F tb fb τ then 1 else 0) *
        ∑ t : Fin T, (if feedbackEvent A τ t j i then 1 else 0)) =
    expect inst P A T
      (fun τ => (if goodEvent inst F tb fb τ then 1 else 0) *
        ∑ t : Fin T, (if 2 ^ (((τ t).1 : ℕ) + 1) < F ∧ feedbackEvent A τ t j i then 1 else 0)) +
    expect inst P A T
      (fun τ => (if goodEvent inst F tb fb τ then 1 else 0) *
        ∑ t : Fin T, (if F ≤ 2 ^ (((τ t).1 : ℕ) + 1) ∧ feedbackEvent A τ t j i then 1 else 0)) := by
    unfold expect
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro τ _
    have hsum : (∑ t : Fin T, (if feedbackEvent A τ t j i then (1 : ℝ) else 0)) =
        (∑ t : Fin T, (if 2 ^ (((τ t).1 : ℕ) + 1) < F ∧ feedbackEvent A τ t j i then (1 : ℝ) else 0)) +
        (∑ t : Fin T, (if F ≤ 2 ^ (((τ t).1 : ℕ) + 1) ∧ feedbackEvent A τ t j i then (1 : ℝ) else 0)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t _
      by_cases h1 : 2 ^ (((τ t).1 : ℕ) + 1) < F
      · have h2 : ¬ F ≤ 2 ^ (((τ t).1 : ℕ) + 1) := by omega
        by_cases hf : feedbackEvent A τ t j i <;> simp [h1, h2, hf]
      · have h2 : F ≤ 2 ^ (((τ t).1 : ℕ) + 1) := by omega
        by_cases hf : feedbackEvent A τ t j i <;> simp [h1, h2, hf]
    dsimp only
    rw [hsum]
    ring
  rw [hsplit]
  have hlow := hC_low n T F hn hT inst hμ P hP tb htb fb j i hji
  have hhigh_exp : expect inst P A T
      (fun τ => (if goodEvent inst F tb fb τ then 1 else 0) *
        ∑ t : Fin T, (if F ≤ 2 ^ (((τ t).1 : ℕ) + 1) ∧ feedbackEvent A τ t j i then 1 else 0)) ≤
      (numLevels T : ℝ) * (gamma T inst j i + 1) :=
    SolLemma10Pair.expect_le_const inst P A hw_nonneg hw_sum hn hL _ _
      (SolLemma10Pair.high_pathwise_bound n T F hn hT inst hμ tb htb fb j i hji)
  have hL_bound := SolLemma10Pair.numLevels_le_four_log T hT
  have hγ_bound := SolLemma10Pair.gamma_add_one_le n T hn2 hT inst hμ j i hji
  set X := Real.log ((n : ℝ) * T) / gap inst j i ^ 2
  have hA : 0 ≤ gamma T inst j i + 1 := by
    have : 0 ≤ gamma T inst j i := by
      unfold gamma
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hT' : (2 : ℝ) ≤ T := by exact_mod_cast hT
      have e1 : 4 * (n : ℝ) * T / delta n T = 4 * (n : ℝ) ^ 4 * (T : ℝ) ^ 2 := by
        unfold delta; field_simp
      rw [e1]
      have hlog : 0 ≤ Real.log (4 * (n : ℝ) ^ 4 * (T : ℝ) ^ 2) := by
        apply Real.log_nonneg
        have : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hn'
        nlinarith
      positivity
    linarith
  have hX_nonneg : 0 ≤ X := by linarith
  have hhigh : (numLevels T : ℝ) * (gamma T inst j i + 1) ≤ 1284 * (Real.log T * X) := by
    have hL0 : 0 ≤ (numLevels T : ℝ) := Nat.cast_nonneg _
    have hlogT0 : 0 ≤ 4 * Real.log T := le_trans hL0 hL_bound
    calc (numLevels T : ℝ) * (gamma T inst j i + 1)
        ≤ (4 * Real.log T) * (321 * X) :=
          mul_le_mul hL_bound hγ_bound (by linarith) hlogT0
      _ = 1284 * (Real.log T * X) := by ring
  have hlogT_nonneg : 0 ≤ Real.log T := by
    have : 0 ≤ (numLevels T : ℝ) := Nat.cast_nonneg _
    linarith
  have hnF_nonneg : 0 ≤ (n : ℝ) ^ 2 * F * X := by positivity
  have hlogTX_nonneg : 0 ≤ Real.log T * X := mul_nonneg hlogT_nonneg hX_nonneg
  have hClow_le : C_low * ((n : ℝ) ^ 2 * F * X) ≤ max C_low 0 * ((n : ℝ) ^ 2 * F * X) :=
    mul_le_mul_of_nonneg_right (le_max_left C_low 0) hnF_nonneg
  have hmax_nonneg : 0 ≤ max C_low 0 := le_max_right C_low 0
  nlinarith
