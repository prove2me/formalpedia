-- Prove2me | solution 1 for FourierJacobi.Analysis.core_scalar_denominators_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:51:58.988067+00:00
-- url     : https://prove2.me/submissions/d5656e46-7efa-439a-a40c-9c8abab3667c

import Definitions.Def_FourierJacobi_Analysis_HaarCoreAssembly
import Definitions.Def_FourierJacobi_Analysis_HaarLimits
import Theorems.Thm_FourierJacobi_Algebra_unit_ne_zero


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations FourierJacobi.Measure
open MeasureTheory Filter
open scoped Topology
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (a b : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    (q : ℂ) ≠ 0 ∧ (q : ℂ) + 1 ≠ 0 ∧ (q : ℂ) - 1 ≠ 0 ∧
      (q : ℂ) - 2 ≠ 0 ∧ a * b ≠ 0 := by
  have hq₀ : (q : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (show 0 < q by linarith)
  have hqp : (q : ℂ) + 1 ≠ 0 := by
    exact_mod_cast ne_of_gt (show 0 < q + 1 by linarith)
  have hqm : (q : ℂ) - 1 ≠ 0 := by
    exact_mod_cast ne_of_gt (show 0 < q - 1 by linarith)
  have hqm₂ : (q : ℂ) - 2 ≠ 0 := by
    exact_mod_cast ne_of_gt (show 0 < q - 2 by linarith)
  exact ⟨hq₀, hqp, hqm, hqm₂, mul_ne_zero (unit_ne_zero ha) (unit_ne_zero hb)⟩
end FourierJacobi.Analysis
