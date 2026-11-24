-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.model_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:49:38.542195+00:00
-- url     : https://prove2.me/submissions/21972b42-aa4e-44aa-b705-ccadbca258d0

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_scaled_operator_norm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_adm_gN_rpow_neg_smul_of_norm_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_translated_product_integrable_bound
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_one


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
theorem _root_.solution (H : Hyp D Ξ α) :
    Integrable (fun g : Mt k r => gN (Matrix.of g : Mat k r) ^ (-α) * gN (Matrix.of g : Mat k r) ^ (-α)) D.μG := by
  obtain ⟨T, hT⟩ := H.T0
  obtain ⟨K, -, hK⟩ := translated_product_integrable_bound H
  have h := (hK _ _ 1 1 (adm_gN_rpow_neg_smul_of_norm_eq_one (α := α) T hT) (adm_gN_rpow_neg_smul_of_norm_eq_one (α := α) T hT) 1 WeylGroupFacts.uh_one 1 WeylGroupFacts.uh_one).1
  simpa only [scaled_operator_norm T hT, inv_one, Matrix.one_mul, Matrix.mul_one] using h
end Formalism.FourierDecayAlt.P.B6
