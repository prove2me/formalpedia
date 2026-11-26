-- Prove2me | solution 1 for FourierJacobi.Analysis.inverseSqrt_even_zpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:35:30.732742+00:00
-- url     : https://prove2.me/submissions/f80de7ec-f9cc-4a40-bcf5-f18aaea0e281

import Definitions.Def_FourierJacobi_Analysis_ExplicitKernel
import Definitions.Def_FourierJacobi_Measure_PaperMultiplicativeHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_FourierJacobi_Analysis_HaarKernel
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_sq
import Theorems.Thm_FourierJacobi_Valuations_actualEntryInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_actualMinorInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.actualEntryInteger_coe
attribute [local simp] FourierJacobi.Valuations.actualMinorInteger_coe
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero



set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (hq : 0 ≤ q) (e : ℤ) :
    inverseSqrt q ^ (2 * e) = q ^ (-e) := by
  rw [zpow_mul]
  simp [inverseSqrt_sq hq, zpow_neg]
end FourierJacobi.Analysis
