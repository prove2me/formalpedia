-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.lintegral_inv_norm_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:04:56.51958+00:00
-- url     : https://prove2.me/submissions/74e5cf7d-22fb-41fd-a360-b99df27ac6c7

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (R : ℝ) :
    (∫⁻ c in Metric.closedBall (0 : ℂ) R, ENNReal.ofReal (‖c‖⁻¹)) < ∞ := by
  rw [← lintegral_indicator Metric.isClosed_closedBall.measurableSet, ← Complex.lintegral_comp_polarCoord_symm]
  have hS : MeasurableSet (Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
    measurableSet_Ioc.prod measurableSet_Ioo
  have hle : ∀ p ∈ polarCoord.target, ENNReal.ofReal p.1 •
      (Metric.closedBall (0 : ℂ) R).indicator (fun c => ENNReal.ofReal (‖c‖⁻¹)) (Complex.polarCoord.symm p) ≤
      (Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator (fun _ => (1 : ℝ≥0∞)) p := by
    intro p hp
    rw [polarCoord_target] at hp
    have hp1 : 0 < p.1 := hp.1
    have hn : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
    by_cases hR : p.1 ≤ R
    · have hm : Complex.polarCoord.symm p ∈ Metric.closedBall (0 : ℂ) R := by
        rw [mem_closedBall_zero_iff, hn]; exact hR
      have hm2 : p ∈ Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi := ⟨⟨hp1, hR⟩, hp.2⟩
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm2, hn, smul_eq_mul,
        ← ENNReal.ofReal_mul hp1.le, mul_inv_cancel₀ hp1.ne', ENNReal.ofReal_one]
    · have hm : Complex.polarCoord.symm p ∉ Metric.closedBall (0 : ℂ) R := by
        rw [mem_closedBall_zero_iff, hn]; exact hR
      rw [Set.indicator_of_notMem hm, smul_zero]
      exact zero_le
  refine lt_of_le_of_lt (setLIntegral_mono' polarCoord.open_target.measurableSet hle) ?_
  refine lt_of_le_of_lt (setLIntegral_le_lintegral _ _) ?_
  rw [lintegral_indicator hS, setLIntegral_const, one_mul, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Ioc, Real.volume_Ioo]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
end Formalism.FourierDecayAlt.P.B2x8
