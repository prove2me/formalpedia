-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.adm_gN_rpow_neg_smul_of_norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:06:07.635176+00:00
-- url     : https://prove2.me/submissions/d11892e1-95d9-46cd-a50b-946a913e1517

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_scaled_operator_norm

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
theorem _root_.solution (T : Wq →L[ℂ] Wp) (hT : ‖T‖ = 1) :
    admitted α 1 (fun g : Mat k r => ((gN g ^ (-α) : ℝ) : ℂ) • T) := by
  refine ⟨?_, fun g hg => ?_⟩
  · have h1 : ContinuousOn (fun g : Mat k r => gN g ^ (-α)) (GV k r) :=
      gN_continuous.continuousOn.rpow_const (fun g hg => Or.inl (gN_pos hg).ne')
    exact (Complex.continuous_ofReal.comp_continuousOn h1).smul continuousOn_const
  · rw [scaled_operator_norm T hT, ← Real.rpow_add (gN_pos hg)]
    simp
end Formalism.FourierDecayAlt.P.B6
