-- Prove2me | solution 1 for BUP.world_transport
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T01:05:18.492901+00:00
-- url     : https://prove2.me/submissions/f540e4b7-fbaa-43de-89de-5aad9c8ac986

import Mathlib
import Definitions.Def_BUP_alg
import Definitions.Def_BUP_tor
open BUP

theorem g74o_transport_one {A B P Bg A' B' P' Bg' : Type*} [Group A] [Group B] [Group P] [Group Bg]
    [Group A'] [Group B'] [Group P'] [Group Bg']
    (C : InvSES A B) (D : BraidData A P Bg) (C' : InvSES A' B') (D' : BraidData A' P' Bg')
    (eA : A ≃* A') (eB : B ≃* B') (eP : P ≃* P') (eBg : Bg ≃* Bg')
    (hc1 : ∀ a : A, eB (C.inj a) = C'.inj (eA a))
    (hc2 : ∀ b : B, C'.proj (eB b) = C.proj b)
    (hb1 : ∀ p : P, eBg (D.iota p) = D'.iota (eP p))
    (hb2 : ∀ g : Bg, D'.piBr (eBg g) = D.piBr g)
    (hb3 : ∀ p : P, eA (D.p1 p) = D'.p1 (eP p))
    (h : A →* A) (h' : A' →* A')
    (hcomm : ∀ a : A, eA (h a) = h' (eA a)) :
    NoBUP C D h → NoBUP C' D' h' := by
  rintro ⟨phi, psi, h1, h2, h3⟩
  refine ⟨eP.toMonoidHom.comp (phi.comp eA.symm.toMonoidHom),
    eBg.toMonoidHom.comp (psi.comp eB.symm.toMonoidHom), ?_, ?_, ?_⟩
  · intro a
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    rw [← hb3, h1, hcomm, MulEquiv.apply_symm_apply]
  · intro a
    have : eB.symm (C'.inj a) = C.inj (eA.symm a) := by
      rw [MulEquiv.symm_apply_eq, hc1, MulEquiv.apply_symm_apply]
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    rw [this, h2, hb1]
  · intro b
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    rw [hb2, h3, ← hc2, MulEquiv.apply_symm_apply]

theorem solution {A B P Bg A' B' P' Bg' : Type*} [Group A] [Group B] [Group P] [Group Bg]
    [Group A'] [Group B'] [Group P'] [Group Bg']
    (C : InvSES A B) (D : BraidData A P Bg) (C' : InvSES A' B') (D' : BraidData A' P' Bg')
    (eA : A ≃* A') (eB : B ≃* B') (eP : P ≃* P') (eBg : Bg ≃* Bg')
    (hc1 : ∀ a : A, eB (C.inj a) = C'.inj (eA a))
    (hc2 : ∀ b : B, C'.proj (eB b) = C.proj b)
    (hb1 : ∀ p : P, eBg (D.iota p) = D'.iota (eP p))
    (hb2 : ∀ g : Bg, D'.piBr (eBg g) = D.piBr g)
    (hb3 : ∀ p : P, eA (D.p1 p) = D'.p1 (eP p))
    (h : A →* A) (h' : A' →* A')
    (hcomm : ∀ a : A, eA (h a) = h' (eA a)) :
    NoBUP C D h ↔ NoBUP C' D' h' := by
  refine ⟨g74o_transport_one C D C' D' eA eB eP eBg hc1 hc2 hb1 hb2 hb3 h h' hcomm,
    g74o_transport_one C' D' C D eA.symm eB.symm eP.symm eBg.symm ?_ ?_ ?_ ?_ ?_ h' h ?_⟩
  · intro a
    rw [MulEquiv.symm_apply_eq, hc1, MulEquiv.apply_symm_apply]
  · intro b
    rw [← hc2, MulEquiv.apply_symm_apply]
  · intro p
    rw [MulEquiv.symm_apply_eq, hb1, MulEquiv.apply_symm_apply]
  · intro g
    rw [← hb2, MulEquiv.apply_symm_apply]
  · intro p
    rw [MulEquiv.symm_apply_eq, hb3, MulEquiv.apply_symm_apply]
  · intro a
    rw [MulEquiv.symm_apply_eq, hcomm, MulEquiv.apply_symm_apply]
