-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CommonEigenvectors.hop_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:56:38.885842+00:00
-- url     : https://prove2.me/submissions/5622f1e4-02ed-4f80-9b5d-2248b6a40d87

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommonEigenvectors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CommonEigenvectors
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.CommonEigenvectors
theorem _root_.solution {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {θ : Fin n → ℂ} {x : V}
    (hx : ∀ a, E a a x = θ a • x) :
    hop E x = (∑ c : Fin n, ((n : ℂ) - ((c : ℕ) : ℂ)) * θ c) • x := by
  unfold hop
  rw [LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [LinearMap.smul_apply, hx, smul_smul]
end Formalism.FourierDecayAlt.P.CommonEigenvectors
