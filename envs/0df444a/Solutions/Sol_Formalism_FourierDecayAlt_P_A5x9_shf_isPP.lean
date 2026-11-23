-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.shf_isPP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:15.862137+00:00
-- url     : https://prove2.me/submissions/d6736585-c733-4706-b53f-e5269772e25c

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_shf_isP
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_shf_dot_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_shf_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution (ξ β : Fin n → K) (hξ : ∀ j : Fin n, k < j.val → ξ j = 0)
    (hβ : ∀ b : Fin n, b.val ≤ k → β b = 0) : IsPP R k (1 + vecMulVec ξ β) := by
  refine ⟨shf_isP R k ξ β hξ hβ, ?_⟩
  rw [shf_inv ξ β (shf_dot_zero k ξ β hξ hβ)]
  exact shf_isP R k (-ξ) β (fun j hj => by rw [Pi.neg_apply, hξ j hj, neg_zero]) hβ
end Formalism.FourierDecayAlt.P.A5x9
