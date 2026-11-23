-- Prove2me | solution 1 for Deduction.mellin_Gchi_modOne_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:21.56232+00:00
-- url     : https://prove2.me/submissions/00b6676d-e563-48ec-a1ed-dff6a67c3ef1

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_MellinRamp
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_mellinGchiModOne

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
theorem _root_.solution {μ : Measure ℝ} (T : ℕ → ℝ → ℂ) (E : ℝ → ℂ)
    (hT : ∀ n, Integrable (T n) μ) (hE : Integrable E μ)
    (hs : Summable fun n => ∫ a, ‖T n a‖ ∂μ) (hp : ∀ a, Summable fun n => T n a) :
    ∫ a, (E a + ∑' n, T n a) ∂μ = ∫ a, E a ∂μ + ∑' n, ∫ a, T n a ∂μ := by
  let F : ℕ → ℝ → ℂ := fun n => Nat.casesOn n E T
  have hF : ∀ n, Integrable (F n) μ := fun n => by
    cases n with
    | zero => exact hE
    | succ n => exact hT n
  have hFs : Summable fun n => ∫ a, ‖F n a‖ ∂μ := (summable_nat_add_iff 1).mp hs
  have h := hasSum_integral_of_summable_integral_norm hF hFs
  have h2 : ∀ a, ∑' n, F n a = E a + ∑' n, T n a := fun a =>
    ((summable_nat_add_iff (f := fun n => F n a) 1).mp (hp a)).tsum_eq_zero_add
  simp_rw [h2] at h
  rw [← h.tsum_eq, h.summable.tsum_eq_zero_add]
  rfl
end Deduction
