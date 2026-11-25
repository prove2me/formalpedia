-- Prove2me | solution 1 for Formalism.E.existsSesqForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:23:51.05505+00:00
-- url     : https://prove2.me/submissions/59c76d04-5340-4b8a-ae55-8b41b8d7f91f

import Definitions.Def_Formalism_FockGram_StatementFock
import Definitions.Def_Formalism_FockGram_FockGramProofs_FockSesq
import Theorems.Thm_Formalism_E_fock_add_left
import Theorems.Thm_Formalism_E_fock_smul_left
import Theorems.Thm_Formalism_E_fock_add_right
import Theorems.Thm_Formalism_E_fock_smul_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MvPolynomial
open Formalism Formalism.E
namespace Formalism.E
theorem _root_.solution : FockSesq := by
  intro R τ _ _
  exact ⟨LinearMap.mk₂'ₛₗ (RingHom.id R) (starRingEnd R) (fun f g => fock f g)
    (fun f f' g => fock_add_left f f' g) (fun c f g => by rw [fock_smul_left]; rfl)
    (fun f g g' => fock_add_right f g g') (fun c f g => by rw [fock_smul_right]; rfl),
    fun f g => rfl⟩
end Formalism.E
