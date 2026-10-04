-- Prove2me | solution 1 for DRLogReg.Reformulation.regularized_limit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T19:16:04.644261+00:00
-- url     : https://prove2.me/submissions/22c72c71-b968-47e4-ac79-aef0e4b7a64f

import Mathlib
import Definitions.Def_DRLogReg_Reformulation_Core
import Definitions.Def_DRLogReg_Reformulation_Program

set_option autoImplicit false

universe u

open MeasureTheory
open scoped ENNReal

theorem rl4259_softplus_flip (t : ℝ) :
    Real.log (1 + Real.exp t) ≤ Real.log (1 + Real.exp (-t)) + |t| := by
  have h1 : 0 < 1 + Real.exp t := by positivity
  have h2 : 0 < 1 + Real.exp (-t) := by positivity
  rw [← Real.log_exp |t|, ← Real.log_mul h2.ne' (Real.exp_pos _).ne']
  apply Real.log_le_log h1
  have e1 : Real.exp t ≤ Real.exp |t| := Real.exp_le_exp.mpr (le_abs_self t)
  have e2 : (1 : ℝ) ≤ Real.exp (-t) * Real.exp |t| := by
    rw [← Real.exp_add]; exact Real.one_le_exp (by linarith [le_abs_self t])
  nlinarith

open DRLogReg.Reformulation in
theorem rl4259_flip_le {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (β : V →L[ℝ] ℝ) (x : V) (y : Bool) :
    logloss β x (!y) ≤ logloss β x y + ‖β‖ * ‖x‖ := by
  have hs : sgn (!y) = - sgn y := by cases y <;> simp [sgn]
  have habs : |sgn y * β x| ≤ ‖β‖ * ‖x‖ := by
    rw [abs_mul]
    have : |sgn y| = 1 := by cases y <;> simp [sgn]
    rw [this, one_mul, ← Real.norm_eq_abs]
    exact β.le_opNorm x
  unfold logloss
  rw [hs, neg_mul, neg_neg]
  linarith [rl4259_softplus_flip (sgn y * β x)]

open DRLogReg.Reformulation in
theorem solution
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {ε : ℝ} (hε : 0 ≤ ε) {N : ℕ} (hN : 0 < N)
    (xhat : Fin N → V) (yhat : Fin N → Bool) :
    Filter.Tendsto (fun κ : ℝ => value7 κ ε xhat yhat) Filter.atTop
      (nhds (⨅ β : V →L[ℝ] ℝ,
        ENNReal.ofReal (ε * ‖β‖ + (N : ℝ)⁻¹ * ∑ i, logloss β (xhat i) (yhat i)))) := by
  set L := ⨅ β : V →L[ℝ] ℝ,
    ENNReal.ofReal (ε * ‖β‖ + (N : ℝ)⁻¹ * ∑ i, logloss β (xhat i) (yhat i)) with hL
  have hNinv : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  have lower : ∀ κ : ℝ, L ≤ value7 κ ε xhat yhat := by
    intro κ
    unfold value7
    refine le_iInf₂ fun p hp => ?_
    refine iInf_le_of_le p.1 (ENNReal.ofReal_le_ofReal ?_)
    obtain ⟨h1, _, h3⟩ := hp
    unfold objective7
    have hs : ∑ i, logloss p.1 (xhat i) (yhat i) ≤ ∑ i, p.2.2 i :=
      Finset.sum_le_sum fun i _ => h1 i
    have := mul_le_mul_of_nonneg_left hs hNinv
    have := mul_le_mul_of_nonneg_left h3 hε
    nlinarith
  have upper : ∀ β : V →L[ℝ] ℝ, ∀ᶠ κ in Filter.atTop, value7 κ ε xhat yhat ≤
      ENNReal.ofReal (ε * ‖β‖ + (N : ℝ)⁻¹ * ∑ i, logloss β (xhat i) (yhat i)) := by
    intro β
    filter_upwards [Filter.eventually_all.2 (fun i => Filter.eventually_ge_atTop ‖xhat i‖)]
      with κ hκ
    unfold value7
    have hmem : (β, ‖β‖, fun i => logloss β (xhat i) (yhat i)) ∈ feasible7 κ xhat yhat := by
      refine ⟨fun i => le_rfl, fun i => ?_, le_rfl⟩
      have h1 := rl4259_flip_le β (xhat i) (yhat i)
      have h2 : ‖β‖ * ‖xhat i‖ ≤ ‖β‖ * κ := mul_le_mul_of_nonneg_left (hκ i) (norm_nonneg _)
      simp only
      linarith
    refine (iInf₂_le _ hmem).trans (le_of_eq ?_)
    unfold objective7
    congr 1
    simp only
    ring
  rw [tendsto_order]
  refine ⟨fun a ha => Filter.Eventually.of_forall fun κ => lt_of_lt_of_le ha (lower κ),
    fun b hb => ?_⟩
  obtain ⟨β, hβ⟩ := iInf_lt_iff.1 hb
  filter_upwards [upper β] with κ hκ
  exact lt_of_le_of_lt hκ hβ
