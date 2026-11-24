-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.KK_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:53:50.678766+00:00
-- url     : https://prove2.me/submissions/c907901d-c08a-4ffd-ac24-1807f87920de

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_EE_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_KK_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} (E : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V)
namespace Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
theorem _root_.solution (hE : GlRel E) {v : V} {X : Fin (N + 1) → V} (hX : X ∈ Gd E v) : KK E X ∈ Gd E v := by
  rw [KK_apply]
  exact (Gd E v).sub_mem ((Gd E v).smul_mem _ hX) (EE_mem E hE hX)
end Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
