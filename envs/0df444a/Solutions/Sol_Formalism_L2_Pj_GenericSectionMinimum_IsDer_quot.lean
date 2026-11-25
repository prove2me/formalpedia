-- Prove2me | solution 1 for Formalism.L2.Pj.GenericSectionMinimum.IsDer.quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:22:37.145256+00:00
-- url     : https://prove2.me/submissions/b2a64c1e-e453-4a02-bdaf-01b94d42f893

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PowMapMemOfPowMulMem
import Theorems.Thm_Formalism_L2_Pj_GenericSectionMinimum_IsDer_der_sub

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
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenericSectionMinimum
open Formalism.L2.Pj.GenericSectionMinimum.IsDer
variable {A : Type*} [CommRing A] {δ : A → A}
namespace Formalism.L2.Pj.GenericSectionMinimum.IsDer
theorem _root_.solution (h : IsDer δ) (I : Ideal A) (hI : ∀ x ∈ I, δ x ∈ I) :
    ∃ δ' : A ⧸ I → A ⧸ I, IsDer δ' ∧ ∀ x, δ' (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (δ x) := by
  classical
  let s := Function.surjInv (Ideal.Quotient.mk_surjective (I := I))
  have hs : ∀ q, Ideal.Quotient.mk I (s q) = q := Function.surjInv_eq _
  have key : ∀ x, Ideal.Quotient.mk I (δ (s (Ideal.Quotient.mk I x))) = Ideal.Quotient.mk I (δ x) := by
    intro x
    rw [Ideal.Quotient.eq, ← h.der_sub]
    exact hI _ (Ideal.Quotient.eq.mp (hs _))
  refine ⟨fun q => Ideal.Quotient.mk I (δ (s q)), ⟨fun a b => ?_, fun a b => ?_⟩, key⟩
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_add, key, key, key, h.add, map_add]
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul, key, key, key, h.mul, map_add, map_mul, map_mul]
end Formalism.L2.Pj.GenericSectionMinimum.IsDer
