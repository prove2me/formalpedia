-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.wt_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:22:51.716578+00:00
-- url     : https://prove2.me/submissions/d97135de-df20-4f0d-85f6-73e8bc3ffdf7

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_lam_continuous

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) : Continuous (fun x : (ℝ × ℝ) × SS k r => wt D x.1 x.2) := by
  unfold wt
  have c1 : Continuous (fun x : (ℝ × ℝ) × SS k r => lam k r D.z (Matrix.of x.2.1.2)) :=
    (lam_continuous k r D.z).comp (continuous_snd.comp (continuous_fst.comp continuous_snd))
  have c2 : Continuous (fun x : (ℝ × ℝ) × SS k r => lam k r D.z' (Matrix.of x.2.2.2)) :=
    (lam_continuous k r D.z').comp (continuous_snd.comp (continuous_snd.comp continuous_snd))
  refine Continuous.mul (Continuous.inv₀ (by fun_prop) (fun x => by positivity))
    (Continuous.inv₀ (by fun_prop) (fun x => by positivity))
end Formalism.FourierDecayAlt.P.B6
