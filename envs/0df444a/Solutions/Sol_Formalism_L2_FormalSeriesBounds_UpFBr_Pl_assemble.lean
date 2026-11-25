-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.assemble
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:11:57.75205+00:00
-- url     : https://prove2.me/submissions/6fbf40df-f71b-427a-be57-95c43886a37b

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieUpFBrPl
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_DetNeZeroOfChars
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_exists_jj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.UpFBr Formalism.L2.FormalSeriesBounds.UpFBr.Pl
namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl
theorem _root_.solution {X : Type} {d : ℕ} [NeZero d] (n : ℕ) (hn : n = d) (Emb : Set X) (em : ZMod d → X)
    (hinj : Function.Injective em) (hmem : ∀ a, em a ∈ Emb) (hsurj : ∀ τ ∈ Emb, ∃ a, τ = em a) :
    ∃ (_ : NeZero n) (t : Fin n ≃ Emb) (jj : ZMod d ≃ Fin n),
      (∀ a, jj (a + 1) = jj a + 1) ∧ ∀ a, ((t (jj a) : Emb) : X) = em a := by
  subst n
  obtain ⟨jj, hjj⟩ := exists_jj d
  let e : ZMod d ≃ Emb := Equiv.ofBijective (fun a => (⟨em a, hmem a⟩ : Emb))
    ⟨fun a a' h => hinj (congrArg Subtype.val h), fun τ => by
      obtain ⟨a, ha⟩ := hsurj τ τ.2
      exact ⟨a, Subtype.ext ha.symm⟩⟩
  refine ⟨inferInstance, jj.symm.trans e, jj, hjj, fun a => ?_⟩
  show ((e (jj.symm (jj a)) : Emb) : X) = em a
  rw [Equiv.symm_apply_apply]
  rfl
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
