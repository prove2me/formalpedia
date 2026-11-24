-- Prove2me | solution 1 for Formalism.LatticeIndexTer.LatticeIndexLength.idx_eq_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:49:29.803086+00:00
-- url     : https://prove2.me/submissions/8fea4386-2615-4f52-a74d-42824a334d6f

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_GeneralBFactSecondFurther_Imports
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxBase
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexLength_length_quotient_tower_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeIndexTer
open Module
open scoped Pointwise
open Formalism.LatticeIndexTer.LatticeIndexLength
namespace Formalism.LatticeIndexTer.LatticeIndexLength
theorem _root_.solution {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]
    (P Q D : Submodule O X) (hD : D ≤ P ⊓ Q)
    (hP : Module.length O (P ⧸ D.comap P.subtype) ≠ ⊤)
    (hQ : Module.length O (Q ⧸ D.comap Q.subtype) ≠ ⊤) :
    idx O X P Q = ((Module.length O (P ⧸ D.comap P.subtype)).toNat : ℤ) -
      ((Module.length O (Q ⧸ D.comap Q.subtype)).toNat : ℤ) := by
  have eP := length_quotient_tower_add D (P ⊓ Q) P hD inf_le_left
  have eQ := length_quotient_tower_add D (P ⊓ Q) Q hD inf_le_right
  have cP : Q.comap P.subtype = (P ⊓ Q).comap P.subtype := by
    rw [Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]
  have cQ : P.comap Q.subtype = (P ⊓ Q).comap Q.subtype := by
    rw [Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]
  unfold idx qlen
  rw [cP, cQ]
  rw [eP] at hP ⊢
  rw [eQ] at hQ ⊢
  obtain ⟨h1, h2⟩ := WithTop.add_ne_top.1 hP
  obtain ⟨_, h3⟩ := WithTop.add_ne_top.1 hQ
  rw [ENat.toNat_add h1 h2, ENat.toNat_add h1 h3]
  push_cast
  ring
end Formalism.LatticeIndexTer.LatticeIndexLength
