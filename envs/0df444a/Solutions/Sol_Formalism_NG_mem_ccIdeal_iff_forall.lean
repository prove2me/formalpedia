-- Prove2me | solution 1 for Formalism.NG.mem_ccIdeal_iff_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:09:43.550886+00:00
-- url     : https://prove2.me/submissions/b4572907-eaa1-4da7-b753-df0f1831448b

import Definitions.Def_Formalism_CharacterColumnKernels_StatementBC
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_MemCcIdealIffForall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
namespace Formalism.NG
theorem _root_.solution {O : Type*} [CommRing O] {X : Type*} (T : Subalgebra O (X → O))
    (Z : Set X) (c : T) : c ∈ ccIdeal T Z ↔ ∀ x ∉ Z, (c : X → O) x = 0 := by
  unfold ccIdeal
  rw [RingHom.mem_ker]
  constructor
  · intro h x hx
    have := congrFun h ⟨x, hx⟩
    simpa [resOff] using this
  · intro h
    funext x
    simp [resOff, h x.1 x.2]
end Formalism.NG
