-- Prove2me | solution 1 for FakeUserRanking.FORC.goodG1_step_on_goodG2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T07:48:36.982337+00:00
-- url     : https://prove2.me/submissions/2c786bde-f8d8-4db7-a303-db9602fddbf4

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent

set_option autoImplicit false

open FakeUserRanking.FORC MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SolGoodG1Step

open Classical

variable {n L T : ℕ}

/-! ### 1. Basic Cascade Observation Weights -/

lemma reach_nonneg (inst : Instance n) (π : Equiv.Perm (Fin n)) (j : Fin n) :
    0 ≤ reach inst π j := by
  unfold reach
  apply mul_nonneg <;> apply Finset.prod_nonneg <;> intro r _
  · linarith [(inst.q_mem r).2]
  · linarith [(inst.μ_mem (π r)).2]

lemma realW_nonneg (inst : Instance n) (π : Equiv.Perm (Fin n)) (o : Obs n) :
    0 ≤ realW inst π o := by
  rcases o with ⟨j, b⟩
  have h1 := reach_nonneg inst π j
  have h2 := (inst.μ_mem (π j)).1
  have h3 := (inst.μ_mem (π j)).2
  have h4 := (inst.q_mem j).1
  cases b
  · simp only [realW]
    apply mul_nonneg (mul_nonneg h1 (by linarith))
    split_ifs <;> linarith
  · simp only [realW]; exact mul_nonneg h1 h2

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

lemma tele (f : ℕ → ℝ) (j N : ℕ) (h : j ≤ N) :
    ∑ m ∈ Finset.range N, (if j ≤ m then f m - f (m + 1) else 0) = f j - f N := by
  induction N, h using Nat.le_induction with
  | base =>
    rw [Finset.sum_eq_zero]; · ring
    intro m hm; simp at hm; rw [if_neg (by omega)]
  | succ N hle ih =>
    rw [Finset.sum_range_succ, ih, if_pos hle]; ring

lemma realW_sum (inst : Instance n) (π : Equiv.Perm (Fin n)) (hn : 1 ≤ n) :
    ∑ o, realW inst π o = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  simp only [realW_pair]
  rw [Fin.sum_univ_eq_sum_range (fun m => rho inst π m - rho inst π (m + 1)) n]
  rw [Finset.sum_range_sub']
  simp [rho, dif_pos (show 0 < n by omega), reach_zero inst π (show 0 < n by omega)]

noncomputable def SS (inst : Instance n) (π : Equiv.Perm (Fin n)) (j : Fin n) : ℝ :=
  ∑ o, realW inst π o * (if j ≤ o.1 then 1 else 0)

lemma SS_eq (inst : Instance n) (π : Equiv.Perm (Fin n)) (j : Fin n) :
    SS inst π j = reach inst π j := by
  unfold SS
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  have : ∀ j' : Fin n, realW inst π (j', true) * (if j ≤ (j', true).1 then 1 else 0) +
      realW inst π (j', false) * (if j ≤ (j', false).1 then 1 else 0) =
      (if (j : ℕ) ≤ (j' : ℕ) then rho inst π j' - rho inst π (j' + 1) else 0) := by
    intro j'
    rw [← realW_pair]
    simp only [Fin.le_def]
    split_ifs <;> ring
  simp only [this]
  rw [Fin.sum_univ_eq_sum_range (fun m => if (j : ℕ) ≤ m then rho inst π m - rho inst π (m + 1)
    else 0) n]
  rw [tele _ _ _ j.isLt.le]
  simp [rho, j.isLt]

/-! ### 2. Single-Round Real Hoeffding Bound -/

lemma bernoulli_hoeffding (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    μ * Real.exp (t * (1 - μ)) + (1 - μ) * Real.exp (t * (0 - μ)) ≤ Real.exp (t ^ 2 / 8) := by
  let p : unitInterval := ⟨μ, hμ⟩
  let ν : Measure ℝ := ProbabilityTheory.bernoulliMeasure (1 : ℝ) (0 : ℝ) p
  let X : ℝ → ℝ := fun z => if z = 1 then 1 else 0
  have hXmeas : AEMeasurable X ν :=
    (Measurable.ite (measurableSet_singleton 1) measurable_const measurable_const).aemeasurable
  have hX01 : ∀ᵐ z ∂ν, X z ∈ Set.Icc (0 : ℝ) 1 :=
    ae_of_all _ (fun z => by dsimp [X]; split_ifs <;> simp)
  have hmean : ∫ z, X z ∂ν = μ := by
    rw [ProbabilityTheory.integral_bernoulliMeasure]
    simp [X, p]
  have hsub := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc hXmeas hX01
  have hmgf := hsub.mgf_le t
  rw [ProbabilityTheory.mgf, hmean, ProbabilityTheory.integral_bernoulliMeasure] at hmgf
  dsimp only [X, p] at hmgf
  simp only [if_true, zero_ne_one, if_false, smul_eq_mul] at hmgf
  refine hmgf.trans ?_
  apply Real.exp_le_exp.mpr
  have hq : (((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : NNReal) : ℝ) = 1 / 4 := by norm_num
  rw [hq]
  linarith

noncomputable def dCnt (π : Equiv.Perm (Fin n)) (i : Fin n) (o : Obs n) : ℝ :=
  if π.symm i ≤ o.1 then 1 else 0

noncomputable def dClk (π : Equiv.Perm (Fin n)) (i : Fin n) (o : Obs n) : ℝ :=
  if o.2 = true ∧ i = π o.1 then 1 else 0

lemma dClk_eq_ite (π : Equiv.Perm (Fin n)) (i : Fin n) (o : Obs n) :
    dClk π i o = if o = (π.symm i, true) then 1 else 0 := by
  unfold dClk
  rcases o with ⟨j, b⟩
  congr 1
  ext
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨rfl, rfl⟩
    exact ⟨(π.symm_apply_apply j).symm, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, (π.apply_symm_apply i).symm⟩

lemma dClk_le_dCnt (π : Equiv.Perm (Fin n)) (i : Fin n) (o : Obs n) :
    dClk π i o ≤ dCnt π i o := by
  rw [dClk_eq_ite]
  unfold dCnt
  split_ifs with h1 h2
  · norm_num
  · exfalso; apply h2; rw [h1]
  · norm_num
  · norm_num

lemma dClk_nonneg (π : Equiv.Perm (Fin n)) (i : Fin n) (o : Obs n) :
    0 ≤ dClk π i o := by
  unfold dClk; split_ifs <;> norm_num

lemma dCnt_nonneg (π : Equiv.Perm (Fin n)) (i : Fin n) (o : Obs n) :
    0 ≤ dCnt π i o := by
  unfold dCnt; split_ifs <;> norm_num

lemma dCnt_le_one (π : Equiv.Perm (Fin n)) (i : Fin n) (o : Obs n) :
    dCnt π i o ≤ 1 := by
  unfold dCnt; split_ifs <;> norm_num

lemma exp_step_decomp (π : Equiv.Perm (Fin n)) (i : Fin n) (o : Obs n) (μ t c : ℝ) :
    Real.exp (t * (dClk π i o - μ * dCnt π i o) - c * dCnt π i o) =
      1 + dCnt π i o * (Real.exp (t * (0 - μ) - c) - 1) +
        dClk π i o * (Real.exp (t * (1 - μ) - c) - Real.exp (t * (0 - μ) - c)) := by
  rw [dClk_eq_ite]
  unfold dCnt
  rcases o with ⟨j, b⟩
  by_cases h1 : (j, b) = (π.symm i, true)
  · rcases Prod.ext_iff.mp h1 with ⟨rfl, rfl⟩
    simp
  · rw [if_neg h1]
    by_cases h2 : π.symm i ≤ j
    · simp [h2]
    · simp [h2]

lemma realW_dClk_sum (inst : Instance n) (π : Equiv.Perm (Fin n)) (i : Fin n) :
    ∑ o : Obs n, realW inst π o * dClk π i o = reach inst π (π.symm i) * inst.μ i := by
  simp only [dClk_eq_ite, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp [realW]

lemma realW_hoeffding (inst : Instance n) (hn : 1 ≤ n) (π : Equiv.Perm (Fin n)) (i : Fin n)
    (t c : ℝ) (hc : t ^ 2 / 8 ≤ c) :
    ∑ o : Obs n, realW inst π o *
      Real.exp (t * (dClk π i o - inst.μ i * dCnt π i o) - c * dCnt π i o) ≤ 1 := by
  have hdecomp : ∀ o : Obs n,
      realW inst π o * Real.exp (t * (dClk π i o - inst.μ i * dCnt π i o) - c * dCnt π i o) =
      realW inst π o +
        (Real.exp (t * (0 - inst.μ i) - c) - 1) * (realW inst π o * dCnt π i o) +
        (Real.exp (t * (1 - inst.μ i) - c) - Real.exp (t * (0 - inst.μ i) - c)) *
          (realW inst π o * dClk π i o) := by
    intro o
    rw [exp_step_decomp]
    ring
  simp only [hdecomp, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [realW_sum inst π hn, show (∑ x : Obs n, realW inst π x * dCnt π i x) = SS inst π (π.symm i) from rfl,
    SS_eq, realW_dClk_sum]
  have hreach := reach_nonneg inst π (π.symm i)
  have hbern := bernoulli_hoeffding (inst.μ i) (inst.μ_mem i) t
  have hexp : Real.exp (-c) *
      (inst.μ i * Real.exp (t * (1 - inst.μ i)) + (1 - inst.μ i) * Real.exp (t * (0 - inst.μ i))) ≤ 1 := by
    calc Real.exp (-c) *
          (inst.μ i * Real.exp (t * (1 - inst.μ i)) + (1 - inst.μ i) * Real.exp (t * (0 - inst.μ i)))
        ≤ Real.exp (-c) * Real.exp (t ^ 2 / 8) :=
          mul_le_mul_of_nonneg_left hbern (Real.exp_pos _).le
      _ = Real.exp (-c + t ^ 2 / 8) := (Real.exp_add _ _).symm
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hrew : (Real.exp (t * (0 - inst.μ i) - c) - 1) * reach inst π (π.symm i) +
      (Real.exp (t * (1 - inst.μ i) - c) - Real.exp (t * (0 - inst.μ i) - c)) *
        (reach inst π (π.symm i) * inst.μ i) =
      reach inst π (π.symm i) * (Real.exp (-c) *
        (inst.μ i * Real.exp (t * (1 - inst.μ i)) + (1 - inst.μ i) * Real.exp (t * (0 - inst.μ i))) - 1) := by
    rw [show t * (0 - inst.μ i) - c = -c + t * (0 - inst.μ i) by ring,
      show t * (1 - inst.μ i) - c = -c + t * (1 - inst.μ i) by ring,
      Real.exp_add, Real.exp_add]
    ring
  linarith [mul_nonpos_of_nonneg_of_nonpos hreach (sub_nonpos.mpr hexp)]

/-! ### 3. Filtration and Expectation Infrastructure -/

def DepBelow (m : ℕ) {β : Type*} (f : (Fin T → Step n L) → β) : Prop :=
  ∀ τ τ' : Fin T → Step n L, (∀ i : Fin T, (i : ℕ) < m → τ i = τ' i) → f τ = f τ'

lemma DepBelow.mono {m m' : ℕ} {β : Type*} {f : (Fin T → Step n L) → β} (h : DepBelow m f)
    (hm : m ≤ m') : DepBelow m' f :=
  fun τ τ' hτ => h τ τ' (fun i hi => hτ i (lt_of_lt_of_le hi hm))

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

lemma obsW_sum (inst : Instance n) (π : Equiv.Perm (Fin n)) (a : Action n) (hn : 1 ≤ n) :
    ∑ o, obsW inst π a o = 1 := by
  cases a with
  | none => exact realW_sum inst π hn
  | some a => simp [obsW]

lemma obsW_nonneg (inst : Instance n) (π : Equiv.Perm (Fin n)) (a : Action n) (o : Obs n) :
    0 ≤ obsW inst π a o := by
  cases a with
  | none => exact realW_nonneg inst π o
  | some a => simp only [obsW]; split_ifs <;> norm_num

lemma pmf_sum (p : PMF (Action n)) : ∑ a, (p a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top p a)]
  rw [← tsum_fintype (L := SummationFilter.unconditional _), PMF.tsum_coe]; simp

lemma stepW_sum (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n) (m : Fin T) (τ : Fin T → Step n L) :
    ∑ x, stepW inst P A (Function.update τ m x) m = 1 := by
  simp only [stepW_update]
  rw [Fintype.sum_prod_type]
  refine (Finset.sum_congr rfl (fun k _ => ?_)).trans (hw_sum (algHist τ m))
  rw [Fintype.sum_prod_type]
  simp only
  simp only [mul_assoc, ← Finset.mul_sum, obsW_sum inst _ _ hn, mul_one]
  rw [pmf_sum, mul_one]

lemma stepW_nonneg (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (τ : Fin T → Step n L) (s : Fin T) :
    0 ≤ stepW inst P A τ s := by
  unfold stepW
  exact mul_nonneg (mul_nonneg (hw_nonneg _ _) ENNReal.toReal_nonneg) (obsW_nonneg _ _ _ _)

lemma Wm_nonneg (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (m : ℕ) (τ : Fin T → Step n L) : 0 ≤ Wm inst P A m τ := by
  unfold Wm
  apply Finset.prod_nonneg
  intro s _
  split_ifs
  · exact stepW_nonneg inst P A hw_nonneg τ s
  · positivity

lemma Em_mono (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (m : ℕ) (f g : (Fin T → Step n L) → ℝ)
    (hfg : ∀ τ, f τ ≤ g τ) : Em (T := T) inst P A m f ≤ Em (T := T) inst P A m g := by
  unfold Em
  apply Finset.sum_le_sum
  intro τ _
  exact mul_le_mul_of_nonneg_left (hfg τ) (Wm_nonneg inst P A hw_nonneg m τ)

lemma Em_drop (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n) (hN : (0 : ℝ) < Fintype.card (Step n L))
    (m : Fin T) (g : (Fin T → Step n L) → ℝ) (hg : DepBelow m g) :
    Em inst P A (m + 1) g = Em inst P A m g := by
  rw [Em_step inst P A m g hN]
  congr 1
  funext τ
  have : ∀ x, g (Function.update τ m x) = g τ := fun x => hg _ _ (update_agree τ m x)
  simp only [this, ← Finset.sum_mul, stepW_sum inst P A hw_sum hn m τ, one_mul]

lemma expect_eq_Em (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n) (hN : (0 : ℝ) < Fintype.card (Step n L))
    (m : ℕ) (hm : m ≤ T) (g : (Fin T → Step n L) → ℝ) (hg : DepBelow m g) :
    expect inst P A T g = Em inst P A m g := by
  have hT : expect inst P A T g = Em inst P A T g := by
    unfold expect Em trajW Wm
    apply Finset.sum_congr rfl
    intro τ _
    congr 1
    apply Finset.prod_congr rfl
    intro s _
    rw [if_pos s.isLt]
  rw [hT]
  have key : ∀ d, m + d ≤ T → Em inst P A (m + d) g = Em inst P A m g := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      have := Em_drop inst P A hw_sum hn hN ⟨m + d, by omega⟩ g (hg.mono (by simp))
      simp only at this
      rw [← add_assoc, this, ih (by omega)]
  have := key (T - m) (by omega)
  rwa [show m + (T - m) = T by omega] at this

lemma Em_zero_one (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hN : (0 : ℝ) < Fintype.card (Step n L)) :
    Em inst P A (T := T) 0 (fun _ => 1) = 1 := by
  unfold Em Wm
  simp only [Nat.not_lt_zero, if_false, mul_one, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.sum_const, nsmul_eq_mul, Fintype.card_fun, Nat.cast_pow]
  rw [← mul_pow, mul_inv_cancel₀ hN.ne', one_pow]

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

/-! ### 4. Cross-Learned Level Weights and Supermartingale -/

noncomputable def wk (k g : Fin L) : ℝ :=
  if g < k then 1 / 2 ^ ((k : ℕ) + 1) else if g = k then 1 else 0

lemma wk_nonneg (k g : Fin L) : 0 ≤ wk k g := by
  unfold wk; split_ifs <;> positivity

lemma wk_le_one (k g : Fin L) : wk k g ≤ 1 := by
  unfold wk
  split_ifs
  · rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  · norm_num
  · norm_num

lemma wk_sq_le (k g : Fin L) : (wk k g) ^ 2 ≤ wk k g := by
  nlinarith [wk_nonneg k g, wk_le_one k g]

noncomputable def stepEtaReal (k : Fin L) (i : Fin n) (π : Equiv.Perm (Fin n)) (x : Step n L) : ℝ :=
  if x.2.1 = none then wk k x.1 * dCnt π i x.2.2 else 0

noncomputable def stepClkReal (k : Fin L) (i : Fin n) (π : Equiv.Perm (Fin n)) (x : Step n L) : ℝ :=
  if x.2.1 = none then wk k x.1 * dClk π i x.2.2 else 0

noncomputable def stepEtaFake (k : Fin L) (i : Fin n) (π : Equiv.Perm (Fin n)) (x : Step n L) : ℝ :=
  if x.2.1.isSome then wk k x.1 * dCnt π i x.2.2 else 0

noncomputable def stepClkFake (k : Fin L) (i : Fin n) (π : Equiv.Perm (Fin n)) (x : Step n L) : ℝ :=
  if x.2.1.isSome then wk k x.1 * dClk π i x.2.2 else 0

noncomputable def facG1 (inst : Instance n) (k : Fin L) (i : Fin n) (lam : ℝ)
    (π : Equiv.Perm (Fin n)) (x : Step n L) : ℝ :=
  Real.exp (lam * (stepClkReal k i π x - inst.μ i * stepEtaReal k i π x) -
    (lam ^ 2 / 8) * stepEtaReal k i π x)

noncomputable def MtG1 (inst : Instance n) (A : Alg n L) (k : Fin L) (i : Fin n) (lam : ℝ)
    (t : ℕ) (τ : Fin T → Step n L) : ℝ :=
  ∏ r : Fin T, if (r : ℕ) < t then facG1 inst k i lam (ranking A τ r) (τ r) else 1

lemma MtG1_nonneg (inst : Instance n) (A : Alg n L) (k : Fin L) (i : Fin n) (lam : ℝ)
    (t : ℕ) (τ : Fin T → Step n L) : 0 ≤ MtG1 inst A k i lam t τ := by
  unfold MtG1
  apply Finset.prod_nonneg
  intro r _
  split_ifs
  · exact (Real.exp_pos _).le
  · norm_num

lemma MtG1_dep (inst : Instance n) (A : Alg n L) (k : Fin L) (i : Fin n) (lam : ℝ) (t : ℕ) :
    DepBelow (T := T) t (MtG1 inst A k i lam t) := by
  intro τ τ' h
  unfold MtG1
  apply Finset.prod_congr rfl
  intro r _
  split_ifs with hr
  · have er := ranking_dep A r τ τ' (fun j hj => h j (by omega))
    beta_reduce at er
    rw [er, h r hr]
  · rfl

lemma MtG1_update (inst : Instance n) (A : Alg n L) (k : Fin L) (i : Fin n) (lam : ℝ)
    (m : Fin T) (τ : Fin T → Step n L) (x : Step n L) :
    MtG1 inst A k i lam (m + 1) (Function.update τ m x) =
      MtG1 inst A k i lam m τ * facG1 inst k i lam (A.rank (algHist τ m) x.1) x := by
  unfold MtG1
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ m),
    ← Finset.mul_prod_erase Finset.univ (fun r : Fin T => if (r : ℕ) < m then
      facG1 inst k i lam (ranking A τ r) (τ r) else 1) (Finset.mem_univ m)]
  simp only [lt_irrefl, if_false, Nat.lt_succ_self, if_true, Function.update_self, one_mul]
  have e_rank : ranking A (Function.update τ m x) m = A.rank (algHist τ m) x.1 := by
    unfold ranking
    have e1 := algHist_dep (n := n) (L := L) m _ τ (update_agree τ m x)
    beta_reduce at e1
    rw [e1, Function.update_self]
  rw [e_rank, mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro r hr
  have hrm : r ≠ m := Finset.ne_of_mem_erase hr
  have hrm' : (r : ℕ) ≠ m := fun h => hrm (Fin.ext h)
  by_cases hlt : (r : ℕ) < m
  · rw [if_pos (by omega), if_pos hlt, Function.update_of_ne hrm]
    have er := ranking_dep A r (Function.update τ m x) τ (fun j hj => update_agree τ m x j (by omega))
    beta_reduce at er
    rw [er]
  · rw [if_neg (by omega), if_neg hlt]

lemma facG1_sum (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n)
    (k : Fin L) (i : Fin n) (lam : ℝ) (m : Fin T) (τ : Fin T → Step n L) :
    ∑ x : Step n L, stepW inst P A (Function.update τ m x) m *
      facG1 inst k i lam (A.rank (algHist τ m) x.1) x ≤ 1 := by
  simp only [stepW_update]
  set h := algHist τ m
  set q := P (pubHist A τ m)
  rw [Fintype.sum_prod_type]
  have hlevel : ∀ g : Fin L,
      ∑ y : Action n × Obs n, A.w h g * (q y.1).toReal * obsW inst (A.rank h g) y.1 y.2 *
        facG1 inst k i lam (A.rank h g) (g, y) ≤ A.w h g := by
    intro g
    rw [Fintype.sum_prod_type]
    have hact : ∀ a : Action n,
        ∑ o : Obs n, A.w h g * (q a).toReal * obsW inst (A.rank h g) a o *
          facG1 inst k i lam (A.rank h g) (g, a, o) ≤ A.w h g * (q a).toReal := by
      intro a
      have hfactor : ∀ o : Obs n,
          A.w h g * (q a).toReal * obsW inst (A.rank h g) a o *
            facG1 inst k i lam (A.rank h g) (g, a, o) =
          A.w h g * (q a).toReal * (obsW inst (A.rank h g) a o *
            facG1 inst k i lam (A.rank h g) (g, a, o)) := fun _ => by ring
      simp only [hfactor, ← Finset.mul_sum]
      refine mul_le_of_le_one_right (mul_nonneg (hw_nonneg h g) ENNReal.toReal_nonneg) ?_
      cases a with
      | some u =>
        have hfac1 : ∀ o : Obs n, facG1 inst k i lam (A.rank h g) (g, some u, o) = 1 := by
          intro o; unfold facG1 stepClkReal stepEtaReal; simp
        simp only [hfac1, mul_one, obsW_sum inst _ _ hn, le_rfl]
      | none =>
        have hfac_real : ∀ o : Obs n,
            facG1 inst k i lam (A.rank h g) (g, none, o) =
            Real.exp ((lam * wk k g) * (dClk (A.rank h g) i o - inst.μ i * dCnt (A.rank h g) i o) -
              (lam ^ 2 / 8 * wk k g) * dCnt (A.rank h g) i o) := by
          intro o
          unfold facG1 stepClkReal stepEtaReal
          simp only [if_true]
          congr 1; ring
        simp only [obsW, hfac_real]
        apply realW_hoeffding inst hn (A.rank h g) i (lam * wk k g) (lam ^ 2 / 8 * wk k g)
        have hsq := wk_sq_le k g
        have hlam2 : 0 ≤ lam ^ 2 / 8 := by positivity
        calc (lam * wk k g) ^ 2 / 8 = (lam ^ 2 / 8) * (wk k g) ^ 2 := by ring
          _ ≤ (lam ^ 2 / 8) * wk k g := mul_le_mul_of_nonneg_left hsq hlam2
    calc ∑ a : Action n, ∑ o : Obs n, A.w h g * (q a).toReal * obsW inst (A.rank h g) a o *
          facG1 inst k i lam (A.rank h g) (g, a, o)
        ≤ ∑ a : Action n, A.w h g * (q a).toReal := Finset.sum_le_sum (fun a _ => hact a)
      _ = A.w h g * ∑ a : Action n, (q a).toReal := (Finset.mul_sum _ _ _).symm
      _ = A.w h g := by rw [pmf_sum q, mul_one]
  calc ∑ g : Fin L, ∑ y : Action n × Obs n, A.w h g * (q y.1).toReal * obsW inst (A.rank h g) y.1 y.2 *
        facG1 inst k i lam (A.rank h g) (g, y)
      ≤ ∑ g : Fin L, A.w h g := Finset.sum_le_sum (fun g _ => hlevel g)
    _ = 1 := hw_sum h

lemma E_MtG1_le (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n)
    (hN : (0 : ℝ) < Fintype.card (Step n L))
    (k : Fin L) (i : Fin n) (lam : ℝ) :
    ∀ t, t ≤ T → expect inst P A T (MtG1 inst A k i lam t) ≤ 1 := by
  intro t
  induction t with
  | zero =>
    intro _
    have h0 : MtG1 (T := T) inst A k i lam 0 = fun _ => 1 := by
      funext τ; simp [MtG1]
    rw [h0, expect_eq_Em inst P A hw_sum hn hN 0 (Nat.zero_le _) _ (fun _ _ _ => rfl),
      Em_zero_one inst P A hN]
  | succ t ih =>
    intro ht
    rw [expect_eq_Em inst P A hw_sum hn hN (t + 1) ht _ (MtG1_dep inst A k i lam (t + 1))]
    let m : Fin T := ⟨t, by omega⟩
    rw [Em_step inst P A m (MtG1 inst A k i lam (t + 1)) hN]
    calc _ ≤ Em (T := T) inst P A t (MtG1 inst A k i lam t) := by
          apply Em_mono inst P A hw_nonneg
          intro τ
          have hu : ∀ x, MtG1 inst A k i lam (t + 1) (Function.update τ m x) =
              MtG1 inst A k i lam t τ * facG1 inst k i lam (A.rank (algHist τ m) x.1) x :=
            fun x => MtG1_update inst A k i lam m τ x
          simp only [hu]
          have hs := facG1_sum inst P A hw_nonneg hw_sum hn k i lam m τ
          have hM := MtG1_nonneg inst A k i lam t τ
          calc ∑ x, stepW inst P A (Function.update τ m x) m *
                (MtG1 inst A k i lam t τ * facG1 inst k i lam (A.rank (algHist τ m) x.1) x)
              = MtG1 inst A k i lam t τ * ∑ x, stepW inst P A (Function.update τ m x) m *
                facG1 inst k i lam (A.rank (algHist τ m) x.1) x := by
                rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
            _ ≤ MtG1 inst A k i lam t τ * 1 := mul_le_mul_of_nonneg_left hs hM
            _ = _ := mul_one _
      _ = expect inst P A T (MtG1 inst A k i lam t) :=
          (expect_eq_Em inst P A hw_sum hn hN t (by omega) _ (MtG1_dep inst A k i lam t)).symm
      _ ≤ 1 := ih (by omega)

/-! ### 5. Decomposition of `etaHat` and `rHat` into Real and Fake Parts -/

noncomputable def clkHat (st : State n L) (k : Fin L) (i : Fin n) : ℝ :=
  (∑ g ∈ Finset.univ.filter (fun g : Fin L => g < k), (st.clk g i : ℝ)) / 2 ^ ((k : ℕ) + 1) +
    st.clk k i

lemma rHat_eq_div (st : State n L) (k : Fin L) (i : Fin n) (h : etaHat st k i ≠ 0) :
    rHat st k i = clkHat st k i / etaHat st k i := by
  unfold rHat clkHat
  rw [if_neg h]

noncomputable def etaHatReal (A : Alg n L) (k : Fin L) (i : Fin n) (t : ℕ) (τ : Fin T → Step n L) : ℝ :=
  ∑ r : Fin T, if (r : ℕ) < t then stepEtaReal k i (ranking A τ r) (τ r) else 0

noncomputable def clkHatReal (A : Alg n L) (k : Fin L) (i : Fin n) (t : ℕ) (τ : Fin T → Step n L) : ℝ :=
  ∑ r : Fin T, if (r : ℕ) < t then stepClkReal k i (ranking A τ r) (τ r) else 0

noncomputable def etaHatFake (A : Alg n L) (k : Fin L) (i : Fin n) (t : ℕ) (τ : Fin T → Step n L) : ℝ :=
  ∑ r : Fin T, if (r : ℕ) < t then stepEtaFake k i (ranking A τ r) (τ r) else 0

noncomputable def clkHatFake (A : Alg n L) (k : Fin L) (i : Fin n) (t : ℕ) (τ : Fin T → Step n L) : ℝ :=
  ∑ r : Fin T, if (r : ℕ) < t then stepClkFake k i (ranking A τ r) (τ r) else 0

lemma MtG1_eq_exp (inst : Instance n) (A : Alg n L) (k : Fin L) (i : Fin n) (lam : ℝ)
    (t : ℕ) (τ : Fin T → Step n L) :
    MtG1 inst A k i lam t τ =
      Real.exp (lam * (clkHatReal A k i t τ - inst.μ i * etaHatReal A k i t τ) -
        (lam ^ 2 / 8) * etaHatReal A k i t τ) := by
  unfold MtG1 clkHatReal etaHatReal
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum,
    ← Finset.sum_sub_distrib, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro r _
  split_ifs
  · unfold facG1; rfl
  · simp

lemma foldl_fst (T : ℕ) (tb : List (Fin L × Obs n) → Fin L → Finset (Fin n) → Fin n)
    (fb : List (Fin L × Obs n) → Fin L → Equiv.Perm (Fin n)) (l : List (Fin L × Obs n))
    (acc : List (Fin L × Obs n) × State n L) :
    (l.foldl (fun (acc : List (Fin L × Obs n) × State n L) (x : Fin L × Obs n) =>
      (acc.1 ++ [x], acc.2.update n T (forcRank tb fb acc.1 acc.2 x.1) x.1 x.2)) acc).1
      = acc.1 ++ l := by
  induction l generalizing acc with
  | nil => simp
  | cons x l ih => simp [List.foldl_cons, ih]

lemma forcState_snoc (T : ℕ) (tb : List (Fin L × Obs n) → Fin L → Finset (Fin n) → Fin n)
    (fb : List (Fin L × Obs n) → Fin L → Equiv.Perm (Fin n)) (l : List (Fin L × Obs n))
    (x : Fin L × Obs n) :
    forcState n T tb fb (l ++ [x]) =
      (forcState n T tb fb l).update n T (forcRank tb fb l (forcState n T tb fb l) x.1) x.1 x.2 := by
  unfold forcState
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [foldl_fst]
  simp

lemma algHist_succ (τ : Fin T → Step n L) (t : ℕ) (ht : t < T) :
    algHist τ (t + 1) = algHist τ t ++ [((τ ⟨t, ht⟩).1, (τ ⟨t, ht⟩).2.2)] := by
  unfold algHist
  rw [List.take_add_one]
  simp [ht]

lemma stateAt_succ
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (t : ℕ) (ht : t < T) :
    stateAt tb fb τ (t + 1) =
      (stateAt tb fb τ t).update n T (ranking (forc n T tb fb) τ ⟨t, ht⟩) (τ ⟨t, ht⟩).1 (τ ⟨t, ht⟩).2.2 := by
  unfold stateAt ranking forc
  rw [algHist_succ τ t ht, forcState_snoc]

lemma stateAt_zero
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) : stateAt tb fb τ 0 = State.init := by
  unfold stateAt algHist forcState; simp

lemma etaHat_update (T : ℕ) (st : State n L) (π : Equiv.Perm (Fin n)) (ℓ : Fin L) (o : Obs n)
    (k : Fin L) (i : Fin n) :
    etaHat (st.update n T π ℓ o) k i = etaHat st k i + wk k ℓ * dCnt π i o := by
  unfold etaHat State.update wk dCnt
  dsimp only
  have hcnt : ∀ g : Fin L,
      ((if g = ℓ ∧ π.symm i ≤ o.1 then st.cnt g i + 1 else st.cnt g i : ℕ) : ℝ) =
      (st.cnt g i : ℝ) + (if g = ℓ then (if π.symm i ≤ o.1 then 1 else 0) else 0) := by
    intro g
    by_cases h1 : g = ℓ <;> by_cases h2 : π.symm i ≤ o.1 <;> simp [h1, h2]
  simp only [hcnt, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ,
    true_and]
  by_cases hlt : ℓ < k
  · have hne : k ≠ ℓ := ne_of_gt hlt
    by_cases ho : π.symm i ≤ o.1 <;> simp [hlt, hne, ho, add_div] <;> ring
  · by_cases heq : ℓ = k
    · subst heq; simp; ring
    · have hne : k ≠ ℓ := Ne.symm heq
      simp [hlt, heq, hne]

lemma clkHat_update (T : ℕ) (st : State n L) (π : Equiv.Perm (Fin n)) (ℓ : Fin L) (o : Obs n)
    (k : Fin L) (i : Fin n) :
    clkHat (st.update n T π ℓ o) k i = clkHat st k i + wk k ℓ * dClk π i o := by
  unfold clkHat State.update wk dClk
  dsimp only
  have hclk : ∀ g : Fin L,
      ((if g = ℓ ∧ o.2 = true ∧ i = π o.1 then st.clk g i + 1 else st.clk g i : ℕ) : ℝ) =
      (st.clk g i : ℝ) + (if g = ℓ then (if o.2 = true ∧ i = π o.1 then 1 else 0) else 0) := by
    intro g
    by_cases h1 : g = ℓ <;> by_cases h2 : o.2 = true ∧ i = π o.1 <;> simp [h1, h2]
  simp only [hclk, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ,
    true_and]
  by_cases hlt : ℓ < k
  · have hne : k ≠ ℓ := ne_of_gt hlt
    by_cases ho : o.2 = true ∧ i = π o.1 <;> simp [hlt, hne, ho, add_div] <;> ring
  · by_cases heq : ℓ = k
    · subst heq; simp; ring
    · have hne : k ≠ ℓ := Ne.symm heq
      simp [hlt, heq, hne]

lemma sum_lt_succ {f : Fin T → ℝ} (t : ℕ) (ht : t < T) :
    (∑ r : Fin T, if (r : ℕ) < t + 1 then f r else 0) =
      (∑ r : Fin T, if (r : ℕ) < t then f r else 0) + f ⟨t, ht⟩ := by
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (⟨t, ht⟩ : Fin T)),
    ← Finset.sum_erase_add Finset.univ (fun r : Fin T => if (r : ℕ) < t then f r else 0)
      (Finset.mem_univ (⟨t, ht⟩ : Fin T))]
  simp only [Nat.lt_succ_self, if_true, lt_irrefl, if_false, add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  have hne : (r : ℕ) ≠ t := fun h => (Finset.ne_of_mem_erase hr) (Fin.ext h)
  by_cases hlt : (r : ℕ) < t
  · rw [if_pos (by omega), if_pos hlt]
  · rw [if_neg (by omega), if_neg hlt]

lemma etaHat_decomp
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (k : Fin (numLevels T)) (i : Fin n) :
    ∀ t, t ≤ T → etaHat (stateAt tb fb τ t) k i =
      etaHatReal (forc n T tb fb) k i t τ + etaHatFake (forc n T tb fb) k i t τ := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [stateAt_zero]
    simp [etaHat, State.init, etaHatReal, etaHatFake]
  | succ t ih =>
    intro ht
    have hlt : t < T := by omega
    rw [stateAt_succ tb fb τ t hlt, etaHat_update, ih (by omega)]
    unfold etaHatReal etaHatFake
    rw [sum_lt_succ t hlt, sum_lt_succ t hlt]
    unfold stepEtaReal stepEtaFake
    cases h : (τ ⟨t, hlt⟩).2.1 <;> simp [h] <;> ring

lemma clkHat_decomp
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (k : Fin (numLevels T)) (i : Fin n) :
    ∀ t, t ≤ T → clkHat (stateAt tb fb τ t) k i =
      clkHatReal (forc n T tb fb) k i t τ + clkHatFake (forc n T tb fb) k i t τ := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [stateAt_zero]
    simp [clkHat, State.init, clkHatReal, clkHatFake]
  | succ t ih =>
    intro ht
    have hlt : t < T := by omega
    rw [stateAt_succ tb fb τ t hlt, clkHat_update, ih (by omega)]
    unfold clkHatReal clkHatFake
    rw [sum_lt_succ t hlt, sum_lt_succ t hlt]
    unfold stepClkReal stepClkFake
    cases h : (τ ⟨t, hlt⟩).2.1 <;> simp [h] <;> ring

lemma clkHatReal_nonneg (A : Alg n L) (k : Fin L) (i : Fin n) (t : ℕ) (τ : Fin T → Step n L) :
    0 ≤ clkHatReal A k i t τ := by
  unfold clkHatReal stepClkReal
  apply Finset.sum_nonneg
  intro r _
  split_ifs
  · exact mul_nonneg (wk_nonneg k _) (dClk_nonneg _ _ _)
  · norm_num
  · norm_num

lemma clkHatReal_le_etaHatReal (A : Alg n L) (k : Fin L) (i : Fin n) (t : ℕ) (τ : Fin T → Step n L) :
    clkHatReal A k i t τ ≤ etaHatReal A k i t τ := by
  unfold clkHatReal etaHatReal stepClkReal stepEtaReal
  apply Finset.sum_le_sum
  intro r _
  split_ifs
  · exact mul_le_mul_of_nonneg_left (dClk_le_dCnt _ _ _) (wk_nonneg k _)
  · norm_num
  · norm_num

lemma clkHatFake_nonneg (A : Alg n L) (k : Fin L) (i : Fin n) (t : ℕ) (τ : Fin T → Step n L) :
    0 ≤ clkHatFake A k i t τ := by
  unfold clkHatFake stepClkFake
  apply Finset.sum_nonneg
  intro r _
  split_ifs
  · exact mul_nonneg (wk_nonneg k _) (dClk_nonneg _ _ _)
  · norm_num
  · norm_num

lemma clkHatFake_le_etaHatFake (A : Alg n L) (k : Fin L) (i : Fin n) (t : ℕ) (τ : Fin T → Step n L) :
    clkHatFake A k i t τ ≤ etaHatFake A k i t τ := by
  unfold clkHatFake etaHatFake stepClkFake stepEtaFake
  apply Finset.sum_le_sum
  intro r _
  split_ifs
  · exact mul_le_mul_of_nonneg_left (dClk_le_dCnt _ _ _) (wk_nonneg k _)
  · norm_num
  · norm_num

lemma etaHatReal_nonneg (A : Alg n L) (k : Fin L) (i : Fin n) (t : ℕ) (τ : Fin T → Step n L) :
    0 ≤ etaHatReal A k i t τ :=
  le_trans (clkHatReal_nonneg A k i t τ) (clkHatReal_le_etaHatReal A k i t τ)

lemma etaHatFake_nonneg (A : Alg n L) (k : Fin L) (i : Fin n) (t : ℕ) (τ : Fin T → Step n L) :
    0 ≤ etaHatFake A k i t τ :=
  le_trans (clkHatFake_nonneg A k i t τ) (clkHatFake_le_etaHatFake A k i t τ)

/-! ### 6. Bounding Fake Contributions on `goodG2` -/

lemma pubHist_succ (A : Alg n L) (τ : Fin T → Step n L) (t : ℕ) (ht : t < T) :
    pubHist A τ (t + 1) = pubHist A τ t ++
      [(ranking A τ ⟨t, ht⟩, (τ ⟨t, ht⟩).2.1.isSome, (τ ⟨t, ht⟩).2.2)] := by
  unfold pubHist
  rw [List.take_add_one]
  simp [ht]

lemma budget_path (inst : Instance n) (P : Adversary n) (A : Alg n L) (F : ℕ)
    (hP : WithinBudget F P) (τ : Fin T → Step n L) (hτ : ∀ s, stepW inst P A τ s ≠ 0) :
    ∀ s, s ≤ T → ((pubHist A τ s).filter (fun s => s.2.1)).length ≤ F ∧
      (((pubHist A τ s).filter (fun s => s.2.1)).length : ℝ) =
        ∑ t ∈ Finset.range s, (if h : t < T then (if (τ ⟨t, h⟩).2.1.isSome then 1 else 0) else 0) := by
  intro s
  induction s with
  | zero => intro _; simp [pubHist]
  | succ s ih =>
    intro hs
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [pubHist_succ A τ s (by omega), List.filter_append, List.length_append,
      Finset.sum_range_succ, dif_pos (show s < T by omega), ← ih2]
    have hstep := hτ ⟨s, by omega⟩
    by_cases hF : F ≤ ((pubHist A τ s).filter (fun s => s.2.1)).length
    · have hPn := hP _ hF
      have hnone : (τ ⟨s, by omega⟩).2.1 = none := by
        by_contra hc
        apply hstep
        unfold stepW
        rw [hPn, PMF.pure_apply, if_neg hc]
        simp
      simp [hnone]
      omega
    · constructor
      · cases h : (τ ⟨s, by omega⟩).2.1.isSome <;> simp [h] <;> omega
      · cases h : (τ ⟨s, by omega⟩).2.1.isSome <;> simp [h]

lemma fake_count_le (inst : Instance n) (P : Adversary n) (A : Alg n L) (F : ℕ)
    (hP : WithinBudget F P) (τ : Fin T → Step n L) (hτ : ∀ s, stepW inst P A τ s ≠ 0) :
    ∑ s : Fin T, (if (τ s).2.1.isSome then (1 : ℝ) else 0) ≤ F := by
  obtain ⟨b1, b2⟩ := budget_path inst P A F hP τ hτ T le_rfl
  have : ∑ s : Fin T, (if (τ s).2.1.isSome then (1 : ℝ) else 0) =
      ∑ t ∈ Finset.range T, (if h : t < T then (if (τ ⟨t, h⟩).2.1.isSome then 1 else 0) else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun t => if h : t < T then
      (if (τ ⟨t, h⟩).2.1.isSome then (1 : ℝ) else 0) else 0) T]
    apply Finset.sum_congr rfl
    intro s _
    rw [dif_pos s.isLt]
  rw [this, ← b2]
  exact_mod_cast b1

lemma exposure_real (k : Fin L) (τ : Fin T → Step n L) :
    (exposure k τ : ℝ) = ∑ s : Fin T, (if (τ s).2.1.isSome then 1 else 0) * (if (τ s).1 = k then 1 else 0) := by
  unfold exposure
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro s _
  by_cases h1 : (τ s).1 = k <;> by_cases h2 : (τ s).2.1.isSome <;> simp [h1, h2]

lemma etaHatFake_le_on_goodG2 (inst : Instance n) (P : Adversary n) (A : Alg n (numLevels T))
    (F : ℕ) (hP : WithinBudget F P) (k : Fin (numLevels T)) (hk : F ≤ 2 ^ ((k : ℕ) + 1))
    (i : Fin n) (t : ℕ) (τ : Fin T → Step n (numLevels T))
    (hτ : ∀ s, stepW inst P A τ s ≠ 0) (hg2 : goodG2 F τ) :
    etaHatFake A k i t τ ≤ Real.log (2 * (numLevels T : ℝ) / delta n T) + 4 := by
  have hstep : ∀ r : Fin T,
      (if (r : ℕ) < t then stepEtaFake k i (ranking A τ r) (τ r) else 0) ≤
      (1 / 2 ^ ((k : ℕ) + 1) : ℝ) * (if (τ r).2.1.isSome then 1 else 0) +
        (if (τ r).2.1.isSome then 1 else 0) * (if (τ r).1 = k then 1 else 0) := by
    intro r
    unfold stepEtaFake wk
    have hd1 : dCnt (ranking A τ r) i (τ r).2.2 ≤ 1 := dCnt_le_one _ _ _
    have hd0 : 0 ≤ dCnt (ranking A τ r) i (τ r).2.2 := dCnt_nonneg _ _ _
    have hp : (0 : ℝ) ≤ 1 / 2 ^ ((k : ℕ) + 1) := by positivity
    cases h2 : (τ r).2.1.isSome
    · simp
    · by_cases h1 : (r : ℕ) < t
      · by_cases h3 : (τ r).1 < k
        · have h4 : (τ r).1 ≠ k := ne_of_lt h3
          simp only [h1, h3, h4, if_true, if_false, mul_zero, add_zero, mul_one]
          exact mul_le_of_le_one_right hp hd1
        · by_cases h4 : (τ r).1 = k
          · simp only [h1, h4, lt_irrefl, if_true, if_false, mul_one]
            linarith
          · simp only [h1, h3, h4, if_true, if_false, mul_zero, zero_mul, add_zero, mul_one]
            exact hp
      · by_cases h4 : (τ r).1 = k <;> simp [h1, h4] <;> positivity
  calc etaHatFake A k i t τ
      ≤ ∑ r : Fin T, ((1 / 2 ^ ((k : ℕ) + 1) : ℝ) * (if (τ r).2.1.isSome then 1 else 0) +
          (if (τ r).2.1.isSome then 1 else 0) * (if (τ r).1 = k then 1 else 0)) :=
        Finset.sum_le_sum (fun r _ => hstep r)
    _ = (1 / 2 ^ ((k : ℕ) + 1) : ℝ) * (∑ r : Fin T, if (τ r).2.1.isSome then (1 : ℝ) else 0) +
          exposure k τ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, exposure_real]
    _ ≤ (1 / 2 ^ ((k : ℕ) + 1) : ℝ) * F + (Real.log (2 * (numLevels T : ℝ) / delta n T) + 3) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (fake_count_le inst P A F hP τ hτ) (by positivity)
        · exact hg2 k hk
    _ ≤ 1 + (Real.log (2 * (numLevels T : ℝ) / delta n T) + 3) := by
        have hk' : (F : ℝ) ≤ 2 ^ ((k : ℕ) + 1) := by exact_mod_cast hk
        have : (1 / 2 ^ ((k : ℕ) + 1) : ℝ) * F ≤ 1 := by
          rw [one_div_mul_eq_div, div_le_one (by positivity)]
          exact hk'
        linarith
    _ = Real.log (2 * (numLevels T : ℝ) / delta n T) + 4 := by ring

/-! ### 7. Discretizing `etaHatReal` into `Fin (T + 1) × Fin (T + 1)` -/

def isRealK (A : Alg n L) (k : Fin L) (i : Fin n) (t : ℕ) (τ : Fin T → Step n L) (r : Fin T) : Prop :=
  (r : ℕ) < t ∧ (τ r).2.1 = none ∧ (τ r).1 = k ∧ (ranking A τ r).symm i ≤ (τ r).2.2.1

def isRealLtK (A : Alg n L) (k : Fin L) (i : Fin n) (t : ℕ) (τ : Fin T → Step n L) (r : Fin T) : Prop :=
  (r : ℕ) < t ∧ (τ r).2.1 = none ∧ (τ r).1 < k ∧ (ranking A τ r).symm i ≤ (τ r).2.2.1

noncomputable def pairIdx (A : Alg n L) (k : Fin L) (i : Fin n) (t : ℕ) (τ : Fin T → Step n L) :
    Fin (T + 1) × Fin (T + 1) :=
  (⟨(Finset.univ.filter (isRealK A k i t τ)).card,
      Nat.lt_succ_of_le (by simpa using Finset.card_le_univ (Finset.univ.filter (isRealK A k i t τ)))⟩,
   ⟨(Finset.univ.filter (isRealLtK A k i t τ)).card,
      Nat.lt_succ_of_le (by simpa using Finset.card_le_univ (Finset.univ.filter (isRealLtK A k i t τ)))⟩)

noncomputable def evalE (k : Fin L) (p : Fin (T + 1) × Fin (T + 1)) : ℝ :=
  (p.1 : ℝ) + (p.2 : ℝ) / 2 ^ ((k : ℕ) + 1)

lemma evalE_nonneg (k : Fin L) (p : Fin (T + 1) × Fin (T + 1)) : 0 ≤ evalE k p := by
  unfold evalE; positivity

lemma etaHatReal_eq_evalE (A : Alg n L) (k : Fin L) (i : Fin n) (t : ℕ) (τ : Fin T → Step n L) :
    etaHatReal A k i t τ = evalE k (pairIdx A k i t τ) := by
  unfold etaHatReal evalE pairIdx
  dsimp only
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  unfold stepEtaReal wk dCnt isRealK isRealLtK
  by_cases h1 : (r : ℕ) < t <;> by_cases h2 : (τ r).2.1 = none <;>
    by_cases h3 : (τ r).1 < k <;> by_cases h4 : (τ r).1 = k <;>
    by_cases h5 : (ranking A τ r).symm i ≤ (τ r).2.2.1 <;>
    simp [h1, h2, h3, h4, h5]

/-! ### 8. Pathwise Reduction from Bad Step on `goodG2` to `BadReal` -/

lemma log_facts (n T : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T) :
    1 ≤ Real.log (4 * n * T / delta n T) ∧ 0 ≤ Real.log (2 * (numLevels T : ℝ) / delta n T) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hT' : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hL1 : 1 ≤ numLevels T := Nat.clog_pos (by norm_num) (by omega)
  have hL1' : (1 : ℝ) ≤ numLevels T := by exact_mod_cast hL1
  have e1 : 4 * (n : ℝ) * T / delta n T = 4 * (n : ℝ) ^ 4 * (T : ℝ) ^ 2 := by
    unfold delta; field_simp
  have e2 : 2 * (numLevels T : ℝ) / delta n T = 2 * (numLevels T : ℝ) * (n : ℝ) ^ 3 * T := by
    unfold delta; field_simp
  rw [e1, e2]
  have hn3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hn'
  have hn4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hn'
  refine ⟨?_, ?_⟩
  · have : Real.exp 1 ≤ 4 * (n : ℝ) ^ 4 * (T : ℝ) ^ 2 := by
      have := Real.exp_one_lt_d9
      nlinarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos 1) this
  · apply Real.log_nonneg
    have : (1 : ℝ) ≤ 2 * (numLevels T : ℝ) * (n : ℝ) ^ 3 := by nlinarith
    nlinarith

noncomputable def BadReal (inst : Instance n) (A : Alg n L) (k : Fin L) (i : Fin n) (t : ℕ)
    (Alog : ℝ) (p : Fin (T + 1) × Fin (T + 1)) (τ : Fin T → Step n L) : Prop :=
  pairIdx A k i t τ = p ∧
    Real.sqrt (Alog * evalE k p) < |clkHatReal A k i t τ - inst.μ i * evalE k p|

lemma bad_step_imp_badReal (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (P : Adversary n)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (hP : WithinBudget F P) (s : Fin T) (k : Fin (numLevels T)) (hk : F ≤ 2 ^ ((k : ℕ) + 1))
    (i : Fin n) (τ : Fin T → Step n (numLevels T))
    (hτ : ∀ r, stepW inst P (forc n T tb fb) τ r ≠ 0)
    (hg2 : goodG2 F τ)
    (hfail : ¬ (rHat (stateAt tb fb τ ((s : ℕ) + 1)) k i -
        window21 n T (stateAt tb fb τ ((s : ℕ) + 1)) k i ≤ inst.μ i ∧
      inst.μ i ≤ rHat (stateAt tb fb τ ((s : ℕ) + 1)) k i +
        window21 n T (stateAt tb fb τ ((s : ℕ) + 1)) k i)) :
    ∃ p : Fin (T + 1) × Fin (T + 1),
      BadReal inst (forc n T tb fb) k i ((s : ℕ) + 1)
        ((3 / 2) * Real.log (4 * n * T / delta n T)) p τ := by
  set A := forc n T tb fb
  set t₀ := (s : ℕ) + 1
  set st := stateAt tb fb τ t₀
  set Alog := (3 / 2) * Real.log (4 * n * T / delta n T)
  set Blog := Real.log (2 * (numLevels T : ℝ) / delta n T) + 4
  obtain ⟨hlog1, hlog2⟩ := log_facts n T hn hT
  have hAlog : 0 < Alog := by dsimp [Alog]; linarith
  have hBlog : 4 ≤ Blog := by dsimp [Blog]; linarith
  have ht₀ : t₀ ≤ T := by dsimp [t₀]; omega
  have heta_eq := etaHat_decomp tb fb τ k i t₀ ht₀
  have hclk_eq := clkHat_decomp tb fb τ k i t₀ ht₀
  have hcr0 := clkHatReal_nonneg A k i t₀ τ
  have hcr1 := clkHatReal_le_etaHatReal A k i t₀ τ
  have hcf0 := clkHatFake_nonneg A k i t₀ τ
  have hcf1 := clkHatFake_le_etaHatFake A k i t₀ τ
  have her0 := etaHatReal_nonneg A k i t₀ τ
  have hef0 := etaHatFake_nonneg A k i t₀ τ
  have hef_le : etaHatFake A k i t₀ τ ≤ Blog :=
    etaHatFake_le_on_goodG2 inst P A F hP k hk i t₀ τ hτ hg2
  have hμ0 := (inst.μ_mem i).1
  have hμ1 := (inst.μ_mem i).2
  have heta_nonneg : 0 ≤ etaHat st k i := by linarith
  have hclk_nonneg : 0 ≤ clkHat st k i := by linarith
  have hclk_le_eta : clkHat st k i ≤ etaHat st k i := by linarith
  have hrHat_bounds : 0 ≤ rHat st k i ∧ rHat st k i ≤ 1 := by
    by_cases h0 : etaHat st k i = 0
    · unfold rHat; rw [if_pos h0]; exact ⟨le_rfl, zero_le_one⟩
    · rw [rHat_eq_div st k i h0]
      have hpos : 0 < etaHat st k i := lt_of_le_of_ne heta_nonneg (Ne.symm h0)
      exact ⟨div_nonneg hclk_nonneg heta_nonneg, (div_le_one hpos).mpr hclk_le_eta⟩
  have habs_le_one : |rHat st k i - inst.μ i| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hrHat_bounds.1, hrHat_bounds.2]
  have habs_gt : window21 n T st k i < |rHat st k i - inst.μ i| := by
    rw [lt_abs]
    by_contra hle
    push Not at hle
    apply hfail
    constructor <;> linarith [hle.1, hle.2]
  have heta_gt_one : 1 < etaHat st k i := by
    by_contra hle1
    push Not at hle1
    have hmax : max (etaHat st k i) 1 = 1 := max_eq_right hle1
    have hw_ge : 4 ≤ window21 n T st k i := by
      unfold window21
      rw [hmax, div_one, div_one]
      have : 0 ≤ Real.sqrt Alog := Real.sqrt_nonneg _
      linarith
    linarith
  have hmax : max (etaHat st k i) 1 = etaHat st k i := max_eq_left heta_gt_one.le
  have heta_pos : 0 < etaHat st k i := by linarith
  have heta_ne : etaHat st k i ≠ 0 := heta_pos.ne'
  have hmul : window21 n T st k i * etaHat st k i < |clkHat st k i - inst.μ i * etaHat st k i| := by
    calc window21 n T st k i * etaHat st k i
        < |rHat st k i - inst.μ i| * etaHat st k i := mul_lt_mul_of_pos_right habs_gt heta_pos
      _ = |rHat st k i - inst.μ i| * |etaHat st k i| := by rw [abs_of_pos heta_pos]
      _ = |(rHat st k i - inst.μ i) * etaHat st k i| := (abs_mul _ _).symm
      _ = |clkHat st k i - inst.μ i * etaHat st k i| := by
          congr 1; rw [rHat_eq_div st k i heta_ne, sub_mul, div_mul_cancel₀ _ heta_ne]
  have hw_mul : window21 n T st k i * etaHat st k i = Real.sqrt (Alog * etaHat st k i) + Blog := by
    unfold window21
    rw [hmax, add_mul, div_mul_cancel₀ _ heta_ne]
    congr 1
    have hsq : ((3 / 2) * Real.log (4 * (n : ℝ) * T / delta n T) / etaHat st k i) *
        etaHat st k i ^ 2 = Alog * etaHat st k i := by
      dsimp [Alog]; field_simp
    calc Real.sqrt ((3 / 2) * Real.log (4 * (n : ℝ) * T / delta n T) / etaHat st k i) * etaHat st k i
        = Real.sqrt ((3 / 2) * Real.log (4 * (n : ℝ) * T / delta n T) / etaHat st k i) *
            Real.sqrt (etaHat st k i ^ 2) := by
          rw [Real.sqrt_sq heta_pos.le]
      _ = Real.sqrt (((3 / 2) * Real.log (4 * (n : ℝ) * T / delta n T) / etaHat st k i) *
            etaHat st k i ^ 2) := (Real.sqrt_mul (by positivity) _).symm
      _ = Real.sqrt (Alog * etaHat st k i) := by rw [hsq]
  rw [hw_mul] at hmul
  have hfake_abs : |clkHatFake A k i t₀ τ - inst.μ i * etaHatFake A k i t₀ τ| ≤ Blog := by
    rw [abs_le]
    constructor
    · nlinarith
    · nlinarith
  have hsplit : clkHat st k i - inst.μ i * etaHat st k i =
      (clkHatReal A k i t₀ τ - inst.μ i * etaHatReal A k i t₀ τ) +
        (clkHatFake A k i t₀ τ - inst.μ i * etaHatFake A k i t₀ τ) := by
    rw [hclk_eq, heta_eq]; ring
  have htri := abs_add_le (clkHatReal A k i t₀ τ - inst.μ i * etaHatReal A k i t₀ τ)
    (clkHatFake A k i t₀ τ - inst.μ i * etaHatFake A k i t₀ τ)
  rw [← hsplit] at htri
  have hreal_gt : Real.sqrt (Alog * etaHat st k i) <
      |clkHatReal A k i t₀ τ - inst.μ i * etaHatReal A k i t₀ τ| := by linarith
  have hsqrt_mono : Real.sqrt (Alog * etaHatReal A k i t₀ τ) ≤ Real.sqrt (Alog * etaHat st k i) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  refine ⟨pairIdx A k i t₀ τ, rfl, ?_⟩
  rw [← etaHatReal_eq_evalE]
  exact lt_of_le_of_lt hsqrt_mono hreal_gt

/-! ### 9. Concentration Bound for Each `BadReal` Pair and Final Union Bound -/

lemma prob_badReal_le (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n)
    (hN : (0 : ℝ) < Fintype.card (Step n L))
    (k : Fin L) (i : Fin n) (t : ℕ) (ht : t ≤ T) (Alog : ℝ) (hAlog : 0 < Alog)
    (p : Fin (T + 1) × Fin (T + 1)) :
    prob inst P A T (BadReal inst A k i t Alog p) ≤ 2 * Real.exp (-2 * Alog) := by
  by_cases hE : evalE k p ≤ 0
  · have hE0 : evalE k p = 0 := le_antisymm hE (evalE_nonneg k p)
    have hzero : prob inst P A T (BadReal inst A k i t Alog p) = 0 := by
      unfold prob expect
      apply Finset.sum_eq_zero
      intro τ _
      suffices ¬ BadReal inst A k i t Alog p τ by simp [this]
      rintro ⟨hp, hgt⟩
      have her0 : etaHatReal A k i t τ = 0 := by rw [etaHatReal_eq_evalE, hp, hE0]
      have hcr0 : clkHatReal A k i t τ = 0 :=
        le_antisymm (by linarith [clkHatReal_le_etaHatReal A k i t τ]) (clkHatReal_nonneg A k i t τ)
      rw [hE0, hcr0] at hgt
      simp at hgt
    rw [hzero]
    positivity
  · push Not at hE
    set E := evalE k p with hE_def
    set lam := 4 * Real.sqrt (Alog / E) with hlam_def
    have hlam_pos : 0 < lam := by positivity
    have hlam_sq : (lam ^ 2 / 8) * E = 2 * Alog := by
      rw [hlam_def, mul_pow, Real.sq_sqrt (by positivity)]
      field_simp
      ring
    have hlam_mul : lam * Real.sqrt (Alog * E) = 4 * Alog := by
      rw [hlam_def, mul_assoc, ← Real.sqrt_mul (by positivity)]
      have : (Alog / E) * (Alog * E) = Alog ^ 2 := by field_simp
      rw [this, Real.sqrt_sq hAlog.le]
    have hpt : ∀ τ : Fin T → Step n L,
        (if BadReal inst A k i t Alog p τ then (1 : ℝ) else 0) ≤
        Real.exp (-2 * Alog) * (MtG1 inst A k i lam t τ + MtG1 inst A k i (-lam) t τ) := by
      intro τ
      have hM1 := MtG1_nonneg inst A k i lam t τ
      have hM2 := MtG1_nonneg inst A k i (-lam) t τ
      by_cases hb : BadReal inst A k i t Alog p τ
      · rw [if_pos hb]
        rcases hb with ⟨hp, hgt⟩
        have heta : etaHatReal A k i t τ = E := by rw [etaHatReal_eq_evalE, hp]
        rw [lt_abs] at hgt
        rcases hgt with hpos | hneg
        · have h1 : 1 ≤ Real.exp (-2 * Alog) * MtG1 inst A k i lam t τ := by
            rw [MtG1_eq_exp, heta, hlam_sq, ← Real.exp_add]
            apply Real.one_le_exp
            have := mul_lt_mul_of_pos_left hpos hlam_pos
            linarith
          linarith [mul_nonneg (Real.exp_pos (-2 * Alog)).le hM2]
        · have h2 : 1 ≤ Real.exp (-2 * Alog) * MtG1 inst A k i (-lam) t τ := by
            rw [MtG1_eq_exp, heta, neg_sq, hlam_sq, ← Real.exp_add]
            apply Real.one_le_exp
            have hpos' : Real.sqrt (Alog * E) < -(clkHatReal A k i t τ - inst.μ i * E) := hneg
            have := mul_lt_mul_of_pos_left hpos' hlam_pos
            linarith
          linarith [mul_nonneg (Real.exp_pos (-2 * Alog)).le hM1]
      · rw [if_neg hb]
        positivity
    have hE1 := E_MtG1_le inst P A hw_nonneg hw_sum hn hN k i lam t ht
    have hE2 := E_MtG1_le inst P A hw_nonneg hw_sum hn hN k i (-lam) t ht
    calc prob inst P A T (BadReal inst A k i t Alog p)
        ≤ expect inst P A T (fun τ => Real.exp (-2 * Alog) *
            (MtG1 inst A k i lam t τ + MtG1 inst A k i (-lam) t τ)) := by
          unfold prob expect
          apply Finset.sum_le_sum
          intro τ _
          have hW : 0 ≤ trajW inst P A T τ :=
            Finset.prod_nonneg (fun r _ => stepW_nonneg inst P A hw_nonneg τ r)
          exact mul_le_mul_of_nonneg_left (hpt τ) hW
      _ = Real.exp (-2 * Alog) *
            (expect inst P A T (MtG1 inst A k i lam t) +
              expect inst P A T (MtG1 inst A k i (-lam) t)) := by
          unfold expect
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro τ _; ring
      _ ≤ Real.exp (-2 * Alog) * (1 + 1) :=
          mul_le_mul_of_nonneg_left (add_le_add hE1 hE2) (Real.exp_pos _).le
      _ = 2 * Real.exp (-2 * Alog) := by ring

lemma union_pt {ι : Type*} [Fintype ι] (E : Prop) (Ek : ι → Prop) (h : E → ∃ k, Ek k) :
    (if E then (1 : ℝ) else 0) ≤ ∑ k, if Ek k then (1 : ℝ) else 0 := by
  have hnn : ∀ j ∈ (Finset.univ : Finset ι), (0 : ℝ) ≤ if Ek j then (1 : ℝ) else 0 := by
    intro j _; split_ifs <;> norm_num
  by_cases hE' : E
  · rw [if_pos hE']
    obtain ⟨k, hk'⟩ := h hE'
    refine le_trans ?_ (Finset.single_le_sum hnn (Finset.mem_univ k))
    rw [if_pos hk']
  · rw [if_neg hE']
    exact Finset.sum_nonneg hnn

end SolGoodG1Step

open Classical SolGoodG1Step in
theorem solution (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (_hμ : StrictAnti inst.μ)
    (P : Adversary n) (hP : WithinBudget F P)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (_htb : ∀ h k S, S.Nonempty → tb h k S ∈ S)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (s : Fin T) (k : Fin (numLevels T)) (hk : F ≤ 2 ^ ((k : ℕ) + 1)) (i : Fin n) :
    prob inst P (forc n T tb fb) T
      (fun τ => goodG2 F τ ∧ ¬ (
        rHat (stateAt tb fb τ ((s : ℕ) + 1)) k i -
          window21 n T (stateAt tb fb τ ((s : ℕ) + 1)) k i ≤ inst.μ i ∧
        inst.μ i ≤
          rHat (stateAt tb fb τ ((s : ℕ) + 1)) k i +
            window21 n T (stateAt tb fb τ ((s : ℕ) + 1)) k i)) ≤
      delta n T / (4 * (T : ℝ) * (numLevels T : ℝ) * (n : ℝ)) := by
  set A := forc n T tb fb
  set t₀ := (s : ℕ) + 1
  set Alog := (3 / 2) * Real.log (4 * n * T / delta n T)
  have hL : 1 ≤ numLevels T := Nat.clog_pos (by norm_num) (by omega)
  have hLT : numLevels T ≤ T := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have hN : (0 : ℝ) < Fintype.card (Step n (numLevels T)) := by
    have : Nonempty (Step n (numLevels T)) := ⟨(⟨0, hL⟩, none, (⟨0, hn⟩, true))⟩
    exact_mod_cast Fintype.card_pos
  have hw_nonneg : ∀ h g, 0 ≤ A.w h g := fun _ g => levelW_nonneg _ g
  have hw_sum : ∀ h, ∑ g, A.w h g = 1 := fun _ => levelW_sum _ hL
  obtain ⟨hlog1, _⟩ := log_facts n T hn hT
  have hAlog : 0 < Alog := by dsimp [Alog]; linarith
  have ht₀ : t₀ ≤ T := by dsimp [t₀]; omega
  have hunion :
      prob inst P A T (fun τ => goodG2 F τ ∧ ¬ (
        rHat (stateAt tb fb τ t₀) k i - window21 n T (stateAt tb fb τ t₀) k i ≤ inst.μ i ∧
        inst.μ i ≤ rHat (stateAt tb fb τ t₀) k i + window21 n T (stateAt tb fb τ t₀) k i)) ≤
      ∑ p : Fin (T + 1) × Fin (T + 1), prob inst P A T (BadReal inst A k i t₀ Alog p) := by
    unfold prob expect
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro τ _
    rw [← Finset.mul_sum]
    by_cases h0 : trajW inst P A T τ = 0
    · rw [h0]; simp
    have hτ : ∀ r, stepW inst P A τ r ≠ 0 := by
      intro r hr; apply h0; unfold trajW
      exact Finset.prod_eq_zero (Finset.mem_univ r) hr
    have hW : 0 ≤ trajW inst P A T τ :=
      Finset.prod_nonneg (fun r _ => stepW_nonneg inst P A hw_nonneg τ r)
    apply mul_le_mul_of_nonneg_left _ hW
    refine union_pt _ _ ?_
    rintro ⟨hg2, hfail⟩
    exact bad_step_imp_badReal n T F hn hT inst P tb fb hP s k hk i τ hτ hg2 hfail
  have hsum :
      (∑ p : Fin (T + 1) × Fin (T + 1), prob inst P A T (BadReal inst A k i t₀ Alog p)) ≤
      ((T + 1 : ℝ) ^ 2) * (2 * Real.exp (-2 * Alog)) := by
    calc _ ≤ ∑ _p : Fin (T + 1) × Fin (T + 1), (2 * Real.exp (-2 * Alog)) :=
          Finset.sum_le_sum (fun p _ => prob_badReal_le inst P A hw_nonneg hw_sum hn hN k i t₀ ht₀ Alog hAlog p)
      _ = ((T + 1 : ℝ) ^ 2) * (2 * Real.exp (-2 * Alog)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          ring
  have hδ_pos : 0 < delta n T := by unfold delta; positivity
  have h4nT_pos : 0 < 4 * (n : ℝ) * T / delta n T := by positivity
  have hexp_eq : Real.exp (-2 * Alog) = (delta n T / (4 * (n : ℝ) * T)) ^ 3 := by
    have h2A : -2 * Alog = -(3 * Real.log (4 * (n : ℝ) * T / delta n T)) := by
      dsimp [Alog]; ring
    rw [h2A, Real.exp_neg, show (3 : ℝ) * Real.log (4 * (n : ℝ) * T / delta n T) =
      (3 : ℕ) * Real.log (4 * (n : ℝ) * T / delta n T) by norm_num,
      Real.exp_nat_mul, Real.exp_log h4nT_pos, ← inv_pow, inv_div]
  have hfinal :
      ((T + 1 : ℝ) ^ 2) * (2 * (delta n T / (4 * (n : ℝ) * T)) ^ 3) ≤
      delta n T / (4 * (T : ℝ) * (numLevels T : ℝ) * (n : ℝ)) := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hT' : (2 : ℝ) ≤ T := by exact_mod_cast hT
    have hL1' : (1 : ℝ) ≤ numLevels T := by exact_mod_cast hL
    have hLT' : (numLevels T : ℝ) ≤ T := by exact_mod_cast hLT
    have hn0 : (0 : ℝ) < n := by linarith
    have hT0 : (0 : ℝ) < T := by linarith
    have hL0 : (0 : ℝ) < numLevels T := by linarith
    have hlhs : ((T + 1 : ℝ) ^ 2) * (2 * (delta n T / (4 * (n : ℝ) * T)) ^ 3) =
        delta n T * ((T + 1 : ℝ) ^ 2 / (32 * (n : ℝ) ^ 9 * (T : ℝ) ^ 5)) := by
      unfold delta; field_simp; ring
    have hrhs : delta n T / (4 * (T : ℝ) * (numLevels T : ℝ) * (n : ℝ)) =
        delta n T * (1 / (4 * (T : ℝ) * (numLevels T : ℝ) * (n : ℝ))) := by ring
    rw [hlhs, hrhs]
    apply mul_le_mul_of_nonneg_left _ hδ_pos.le
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hn8 : (1 : ℝ) ≤ (n : ℝ) ^ 8 := one_le_pow₀ hn'
    have hT1 : (T + 1 : ℝ) ^ 2 ≤ 4 * (T : ℝ) ^ 2 := by nlinarith
    have hLT_mul : (numLevels T : ℝ) * (T + 1 : ℝ) ^ 2 ≤ 4 * (T : ℝ) ^ 3 := by nlinarith
    have hmul : (numLevels T : ℝ) * (T + 1 : ℝ) ^ 2 ≤ 8 * (n : ℝ) ^ 8 * (T : ℝ) ^ 4 := by
      calc (numLevels T : ℝ) * (T + 1 : ℝ) ^ 2 ≤ 4 * (T : ℝ) ^ 3 := hLT_mul
        _ ≤ 8 * 1 * (T : ℝ) ^ 4 := by nlinarith
        _ ≤ 8 * (n : ℝ) ^ 8 * (T : ℝ) ^ 4 := by
            apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hmul2 := mul_le_mul_of_nonneg_right hmul (show (0 : ℝ) ≤ 4 * (n : ℝ) * (T : ℝ) by positivity)
    linarith
  rw [hexp_eq] at hsum
  exact hunion.trans (hsum.trans hfinal)
