-- Prove2me | solution 1 for FourierJacobi.Analysis.explicitWeylKernel_q_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:50:08.700476+00:00
-- url     : https://prove2.me/submissions/146b8e94-c4e0-4503-9b57-dc4c9afd2e1d

import Definitions.Def_FourierJacobi_Analysis_ExplicitKernel
import Definitions.Def_FourierJacobi_Measure_PaperMultiplicativeHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_FourierJacobi_Analysis_HaarKernel
import Theorems.Thm_FourierJacobi_Analysis_inverseSqrt_even_zpow
import Theorems.Thm_FourierJacobi_Analysis_coreScaleExponent_coe
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_pos
import Theorems.Thm_FourierJacobi_Analysis_explicitWeylKernel_norm_le
import Theorems.Thm_FourierJacobi_Valuations_actualEntryInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_actualMinorInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.actualEntryInteger_coe
attribute [local simp] FourierJacobi.Valuations.actualMinorInteger_coe
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero


attribute [local simp] FourierJacobi.Analysis.coreScaleExponent_coe

set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (hq : 1 < q)
    (a b : ℂ) (p : KernelPoint K) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖explicitWeylKernel K (inverseSqrt q : ℂ) a b p‖ ≤
      ((∑ i : Fin 8, ‖weylWeights (inverseSqrt q : ℂ) a b i‖) /
        poincare (inverseSqrt q)) * q ^ (-3 * kernelN K p - 2 * kernelB K p) := by
  have hn := explicitWeylKernel_norm_le K (inverseSqrt q) a b p
    (inverseSqrt_pos hq).le ha hb
  have he : 3 * kernelEll K p + 4 * kernelB K p =
      2 * (3 * kernelN K p + 2 * kernelB K p) := by unfold kernelEll; ring
  rw [he, inverseSqrt_even_zpow q (by linarith)] at hn
  have he' : -(3 * kernelN K p + 2 * kernelB K p) =
      -3 * kernelN K p - 2 * kernelB K p := by ring
  simpa only [he'] using hn
end FourierJacobi.Analysis
