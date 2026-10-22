-- Prove2me | solution 1 for BUP.homotopy_invariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T01:05:41.242596+00:00
-- url     : https://prove2.me/submissions/bfbdac91-c4f4-46b2-9cad-a3a61c3ced4b

import Mathlib
import Definitions.Def_BUP_alg
import Definitions.Def_BUP_tor
open BUP

theorem g74o_conj_one {A B P Bg : Type*} [Group A] [Group B] [Group P] [Group Bg]
    (C : InvSES A B) (D : BraidData A P Bg) (h1 h2 : A →* A) (w : A)
    (hw : ∀ v : A, h1 v = w * h2 v * w⁻¹) :
    NoBUP C D h2 → NoBUP C D h1 := by
  rintro ⟨phi, psi, e1, e2, e3⟩
  obtain ⟨p, hp⟩ := D.p1_surj w
  refine ⟨(MulAut.conj p).toMonoidHom.comp phi, (MulAut.conj (D.iota p)).toMonoidHom.comp psi,
    ?_, ?_, ?_⟩
  · intro a
    simp [MulAut.conj_apply, e1, hp, hw]
  · intro a
    simp [MulAut.conj_apply, e2]
  · intro b
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, map_mul, map_inv, e3]
    rw [mul_comm (D.piBr (D.iota p)), mul_assoc, mul_inv_cancel, mul_one]

theorem solution {A B P Bg : Type*} [Group A] [Group B] [Group P] [Group Bg]
    (C : InvSES A B) (D : BraidData A P Bg) (h1 h2 : A →* A)
    (hequiv : homEquiv h1 h2) :
    NoBUP C D h1 ↔ NoBUP C D h2 := by
  obtain ⟨w, hw⟩ := hequiv
  refine ⟨g74o_conj_one C D h2 h1 w⁻¹ ?_, g74o_conj_one C D h1 h2 w hw⟩
  intro v
  rw [hw v]; group
