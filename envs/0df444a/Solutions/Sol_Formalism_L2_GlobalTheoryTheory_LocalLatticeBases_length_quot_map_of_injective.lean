-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.length_quot_map_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:12:29.456579+00:00
-- url     : https://prove2.me/submissions/118b8085-e49f-4699-ab78-b2d33cf189e0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL6_LinearIndependentProdRenameOfCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
open MvPolynomial
variable {K : Type*} [Field K] {S₁ S₂ : Type*}
namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
theorem _root_.solution {O M M' : Type*} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    (f : M →ₗ[O] M') (hf : Function.Injective f) (A B : Submodule O M) :
    Module.length O (A.map f ⧸ (B.map f).comap (A.map f).subtype) = Module.length O (A ⧸ B.comap A.subtype) := by
  have h : (B.comap A.subtype).map (Submodule.equivMapOfInjective f hf A : A →ₗ[O] A.map f) =
      (B.map f).comap (A.map f).subtype := by
    ext ⟨y, hy⟩
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨⟨x, hxA⟩, hxB, hx⟩
      refine ⟨x, hxB, ?_⟩
      have hx' := congrArg Subtype.val hx
      exact hx'
    · rintro ⟨x, hxB, rfl⟩
      obtain ⟨x', hx'A, hx'⟩ := Submodule.mem_map.1 hy
      have hxx : x' = x := hf hx'
      subst hxx
      exact ⟨⟨x', hx'A⟩, hxB, Subtype.ext rfl⟩
  exact (Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf A) h).length_eq.symm
end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
