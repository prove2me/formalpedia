-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx8.rho_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:55:19.175484+00:00
-- url     : https://prove2.me/submissions/15dd6969-a6e7-44c5-85a7-678b38d09646

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MulIntegralStatement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.M
variable {P : M.Par}
namespace Formalism.FourierDecayAlt.P.Qx8
theorem _root_.solution (h : P.OK) (π : Ty P) (i : ℕ) (hi : i ∈ Finset.Icc 1 (P.k - 1)) :
    ∃ n : ℤ, rho P π i - P.u 1 - 1 / 2 = n := by
  have hi' := Finset.mem_Icc.1 hi
  have hi1 : i + 1 ∈ Finset.Icc 1 P.k := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  obtain ⟨n₁, hn₁⟩ := h.int_u (i + 1) hi1
  obtain ⟨n₂, hn₂⟩ := h.int_u' (i + 1) hi1
  unfold rho
  rw [dif_pos hi']
  unfold M.Par.lo
  rcases max_choice (P.u (i + 1)) (P.u' (i + 1)) with hm | hm
  · rw [hm]
    exact ⟨n₁ + ((π ⟨i - 1, by omega⟩ : Fin _) : ℕ), by push_cast; linarith⟩
  · rw [hm]
    exact ⟨n₂ + ((π ⟨i - 1, by omega⟩ : Fin _) : ℕ), by push_cast; linarith⟩
end Formalism.FourierDecayAlt.P.Qx8
