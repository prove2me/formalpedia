-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.self_mem_Sr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:36:29.438798+00:00
-- url     : https://prove2.me/submissions/f1acacc2-ab6b-4284-bd49-b97a4dc86c0c

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantEstimate
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivativeRulesA1
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
theorem _root_.solution {g0 : Mat k r} (hg0 : g0 ∈ GV k r) : g0 ∈ Sr g0 := by
  have hgu : IsUnit g0.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0
  have hg1 : g0 * g0⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  have h2 : (1 + 1 : Mat k r) = (2 : ℂ) • (1 : Mat k r) := by rw [two_smul]
  show IsUnit (g0 * g0⁻¹ + 1).det
  rw [hg1, h2, Matrix.det_smul, Matrix.det_one, mul_one]
  exact (isUnit_iff_ne_zero.2 two_ne_zero).pow _
end Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
