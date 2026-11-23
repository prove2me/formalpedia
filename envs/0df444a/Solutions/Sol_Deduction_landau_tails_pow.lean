-- Prove2me | solution 1 for Deduction.landau_tails_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:20.305392+00:00
-- url     : https://prove2.me/submissions/ee81419f-3523-4f54-a544-dbef9a12da62

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_kernelIntegral
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_landauTails

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
namespace Deduction
theorem _root_.solution (k : ℕ) {σ a x c : ℝ} (hσ : 0 < σ) (ha : 0 < a)
    (h : x + k * ((σ - a) / a) ≤ c) :
    Real.exp x * (a ^ (k + 1))⁻¹ ≤ Real.exp c / a / σ ^ k := by
  have h1 : σ / a ≤ Real.exp ((σ - a) / a) := by
    have := Real.add_one_le_exp ((σ - a) / a)
    have e : (σ - a) / a + 1 = σ / a := by field_simp; ring
    linarith
  have h2 : (σ / a) ^ k ≤ Real.exp (k * ((σ - a) / a)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) h1 k
  have h3 : Real.exp x * (σ / a) ^ k ≤ Real.exp c := by
    calc _ ≤ Real.exp x * Real.exp (k * ((σ - a) / a)) := by gcongr
      _ = Real.exp (x + k * ((σ - a) / a)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.2 h
  calc _ = Real.exp x * (σ / a) ^ k / a / σ ^ k := by
        rw [div_pow, pow_succ]; field_simp
    _ ≤ _ := by gcongr
end Deduction
