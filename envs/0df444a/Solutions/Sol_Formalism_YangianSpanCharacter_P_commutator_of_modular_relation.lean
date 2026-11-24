-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.commutator_of_modular_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:56:43.17546+00:00
-- url     : https://prove2.me/submissions/8b1f5bc3-4824-47bc-8eca-e42ffb6dfd8a

import Definitions.Def_Formalism_YangianSpanCharacter_StatementY
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_DiagonalEntryEqOfModularRelation
import Theorems.Thm_Formalism_YangianSpanCharacter_P_conj_commutator_of_scaled_relation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.YangianSpanCharacter Formalism.YangianSpanCharacter.P
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] {t : 𝕜 → Matrix (Fin 2) (Fin 2) A}
  {τinv : 𝕜 → A} {q : 𝕜 → 𝕜} {S : Set 𝕜}
namespace Formalism.YangianSpanCharacter.P
theorem _root_.solution (H : ModHyp t τinv q S) {u v : 𝕜} (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) :
    t u 1 1 * lf t τinv v - lf t τinv v * t u 1 1 = -(t u 1 1 * eta t τinv u v) := by
  simp only [lf, eta]
  exact conj_commutator_of_scaled_relation (sub_ne_zero.mpr huv) (H.1 u v 1 1 1 0) (H.2.2.2.1 v hv).1 (H.2.2.2.1 v hv).2
    (H.2.2.2.1 u hu).1 (H.2.2.2.2.1 u v).eq
end Formalism.YangianSpanCharacter.P
