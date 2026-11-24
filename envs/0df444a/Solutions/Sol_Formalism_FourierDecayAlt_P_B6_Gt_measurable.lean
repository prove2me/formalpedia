-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.Gt_measurable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:41:27.184606+00:00
-- url     : https://prove2.me/submissions/9842d4b6-b6cd-489f-9e52-9f9b3508527b

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_wt_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_phase_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Et_measurable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') : StronglyMeasurable (fun x : (ℝ × ℝ) × SS k r => Gt D F F' x.1 x.2) := by
  have o1 : OpensMeasurableSpace ((ℝ × ℝ) × SS k r) := Prod.opensMeasurableSpace
  have o2 : OpensMeasurableSpace (((ℝ × ℝ) × SS k r) × (ℝ × ℝ)) := Prod.opensMeasurableSpace
  have h1 : StronglyMeasurable (fun x : (ℝ × ℝ) × SS k r => ((wt D x.1 x.2 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp (wt_continuous D)).stronglyMeasurable
  have h2 : StronglyMeasurable (fun y : ((ℝ × ℝ) × SS k r) × (ℝ × ℝ) =>
      Et D F F' (y.1.2, y.2) * Complex.exp (Complex.I * (phase D y.1.1 y.1.2 y.2 : ℂ))) := by
    refine StronglyMeasurable.mul ((Et_measurable H hF hF').comp_measurable (by fun_prop))
      (Continuous.stronglyMeasurable ?_)
    exact Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp (phase_continuous D)))
  exact h1.mul h2.integral_prod_right'
end Formalism.FourierDecayAlt.P.B6
