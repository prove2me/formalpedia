-- Prove2me | solution 1 for DemandResponse.FirstBest.prop3_1_firstBest_value
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T07:32:25.517003+00:00
-- url     : https://prove2.me/submissions/0b578137-56bf-41e3-93b9-9d7d1f2c8f48
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DemandResponse_FirstBest_Model
import Definitions.Def_DemandResponse_FirstBest_ClosedForm
import Theorems.Thm_DemandResponse_FirstBest_eqA5_reduction
import Theorems.Thm_DemandResponse_FirstBest_propA3_Vbar_closed_form
import Theorems.Thm_DemandResponse_FirstBest_prop2_1_best_response

open DemandResponse.FirstBest

theorem solution {N d : ℕ} (P : Params N d)
    (hA : xneg (delta P) * P.T ≤ P.Amax) :
    VFB P = ((U P (vbarFB P 0 P.X₀ - L0 P) : ℝ) : EReal) := by
  obtain ⟨w, hw, hVbar, hVFB⟩ := eqA5_reduction P
  have hA3 := propA3_Vbar_closed_form P
  have hHm := (prop2_1_best_response P).2.2.1
  rw [hVbar] at hA3
  have hw' : w = -Real.exp (-rho P * vbarA6 P 0 P.X₀) := EReal.coe_injective hA3
  -- the two value functions agree at (0, X₀)
  have hv : vbarA6 P 0 P.X₀ = vbarFB P 0 P.X₀ := by
    unfold vbarA6 vbarFB
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le P.hT.le] at hs
    obtain ⟨hs0, hsT⟩ := hs
    simp only [mbar, mFB]
    congr 1
    rw [hHm]
    have hneg : xneg (delta P * (P.T - s)) = xneg (delta P) * (P.T - s) := by
      unfold xneg
      have hTs : 0 ≤ P.T - s := by linarith
      rw [max_mul_of_nonneg _ _ hTs, zero_mul, neg_mul]
    have hxn : 0 ≤ xneg (delta P) := le_max_left _ _
    have hle : xneg (delta P) * (P.T - s) ≤ P.Amax := by
      calc xneg (delta P) * (P.T - s) ≤ xneg (delta P) * P.T :=
            mul_le_mul_of_nonneg_left (by linarith) hxn
        _ ≤ P.Amax := hA
    rw [hneg, min_eq_left hle]
    ring
  rw [hVFB, hw', ← hv]
  congr 1
  -- algebra: R₀ (exp(-ρ v)/(-R₀))^{1+p/r} = -exp(-p (v - L₀))
  have hr := P.hr
  have hp := P.hp
  have hR := P.hR₀
  set v := vbarA6 P 0 P.X₀
  have hpos : 0 < -P.R₀ := by linarith
  have hq : -Real.exp (-rho P * v) / P.R₀ = Real.exp (-rho P * v - Real.log (-P.R₀)) := by
    rw [Real.exp_sub, Real.exp_log hpos]
    field_simp
  rw [hq, ← Real.exp_mul]
  unfold U L0
  have hR0 : P.R₀ = -Real.exp (Real.log (-P.R₀)) := by rw [Real.exp_log hpos]; ring
  rw [hR0, neg_mul, ← Real.exp_add]
  congr 2
  unfold rho
  field_simp
  try simp only [Real.log_exp]
  ring
