-- Prove2me | solution 1 for DRLogReg.Reformulation.worst_case_loss_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T08:54:37.812023+00:00
-- url     : https://prove2.me/submissions/80c0327a-9652-4ace-9b9f-5b297c54721f

import Mathlib
import Definitions.Def_DRLogReg_Reformulation_Core
import Definitions.Def_DRLogReg_Reformulation_Program

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

open DRLogReg.Reformulation in
theorem wcld_sgn_not (y : Bool) : sgn (!y) = - sgn y := by cases y <;> simp [sgn]

theorem wcld_softplus (t : ℝ) :
    Real.log (1 + Real.exp t) = t + Real.log (1 + Real.exp (-t)) := by
  have h : 1 + Real.exp t = Real.exp t * (1 + Real.exp (-t)) := by
    rw [mul_add, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero, add_comm]
  rw [h, Real.log_mul (Real.exp_pos t).ne' (by positivity), Real.log_exp]

open DRLogReg.Reformulation in
theorem wcld_flip {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (β : V →L[ℝ] ℝ) (x : V) (y : Bool) :
    logloss β x (!y) = logloss β x y + sgn y * β x := by
  unfold logloss
  rw [wcld_sgn_not, neg_mul, neg_neg, wcld_softplus (sgn y * β x)]
  ring

open DRLogReg.Reformulation in
theorem wcld_max {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (β : V →L[ℝ] ℝ) (x : V) (y : Bool) (c : ℝ) :
    max (logloss β x y) (logloss β x (!y) - c) =
      logloss β x y + max 0 (sgn y * β x - c) := by
  rw [wcld_flip, ← max_add_add_left, add_zero]
  congr 1
  ring

open DRLogReg.Reformulation in
theorem solution
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 ≤ ε) {N : ℕ} (hN : 0 < N)
    (xhat : Fin N → V) (yhat : Fin N → Bool)
    (βhat : V →L[ℝ] ℝ) (lamhat : ℝ) (shat : Fin N → ℝ)
    (hfeas : (βhat, lamhat, shat) ∈ feasible7 κ xhat yhat)
    (hopt : ∀ q ∈ feasible7 κ xhat yhat, objective7 ε (βhat, lamhat, shat) ≤ objective7 ε q) :
    value7 κ ε xhat yhat =
      ENNReal.ofReal (lamhat * ε + (N : ℝ)⁻¹ * ∑ i, logloss βhat (xhat i) (yhat i) +
        (N : ℝ)⁻¹ * ∑ i, max 0 (sgn (yhat i) * βhat (xhat i) - lamhat * κ)) := by
  obtain ⟨h1, h2, h3⟩ := hfeas
  -- the minimal slack
  set s' : Fin N → ℝ := fun i =>
    max (logloss βhat (xhat i) (yhat i)) (logloss βhat (xhat i) (!yhat i) - lamhat * κ) with hs'
  have hle : ∀ i, s' i ≤ shat i := fun i => max_le (h1 i) (h2 i)
  have hfeas' : (βhat, lamhat, s') ∈ feasible7 κ xhat yhat :=
    ⟨fun i => le_max_left _ _, fun i => le_max_right _ _, h3⟩
  have hNpos : (0 : ℝ) < (N : ℝ)⁻¹ := by positivity
  have hsum : ∑ i, shat i = ∑ i, s' i := by
    have hA := hopt _ hfeas'
    unfold objective7 at hA
    simp only at hA
    have hB : ∑ i, shat i ≤ ∑ i, s' i := by
      by_contra hc
      rw [not_le] at hc
      have := mul_lt_mul_of_pos_left hc hNpos
      linarith
    exact le_antisymm hB (Finset.sum_le_sum fun i _ => hle i)
  have hval : value7 κ ε xhat yhat = ENNReal.ofReal (objective7 ε (βhat, lamhat, shat)) := by
    apply le_antisymm
    · exact iInf₂_le _ ⟨h1, h2, h3⟩
    · exact le_iInf₂ fun q hq => ENNReal.ofReal_le_ofReal (hopt q hq)
  rw [hval]
  congr 1
  unfold objective7
  simp only
  rw [hsum, add_assoc, ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hs']
  exact wcld_max βhat (xhat i) (yhat i) (lamhat * κ)
