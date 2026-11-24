-- Prove2me | solution 1 for Formalism.L2.NCov.length_quot_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:13:46.206309+00:00
-- url     : https://prove2.me/submissions/18773d79-b5f3-4ecf-8f22-5888cb4a9092

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverLen
import Theorems.Thm_Formalism_L2_NCov_length_eq_of_bijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.L2.NCov
open Module
section
variable {R R' M M' : Type*} [CommRing R] [CommRing R'] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R' M']
private theorem length_quotient_eq_of_bijective_semilinear (φ : R ≃+* R') (f : M →ₛₗ[(φ : R →+* R')] M')
    (hf : Function.Bijective f) (q : Submodule R M) (q' : Submodule R' M')
    (h : ∀ x, f x ∈ q' ↔ x ∈ q) :
    Module.length R' (M' ⧸ q') = Module.length R (M ⧸ q) := by
  let g : (M ⧸ q) →ₛₗ[(φ : R →+* R')] (M' ⧸ q') := q.mapQ q' f (fun x hx => (h x).2 hx)
  refine length_eq_of_bijective φ g ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective q y
    have hy' : (Submodule.Quotient.mk (f a) : M' ⧸ q') = 0 := hy
    rw [Submodule.Quotient.mk_eq_zero] at hy'
    rw [Submodule.Quotient.mk_eq_zero]
    exact (h a).1 hy'
  · intro y
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective q' y
    obtain ⟨a, rfl⟩ := hf.2 b
    exact ⟨Submodule.Quotient.mk a, rfl⟩
end
end Formalism.L2.NCov
end

set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.NCov
open Module
variable {R R' M M' : Type*} [CommRing R] [CommRing R'] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R' M']
namespace Formalism.L2.NCov
theorem _root_.solution (φ : R ≃+* R') (f : M →ₛₗ[(φ : R →+* R')] M') (hf : Function.Injective f)
    (p q : Submodule R M) :
    haveI := RingHomInvPair.of_ringEquiv φ
    Module.length R' (↥(p.map f) ⧸ (q.map f).comap (p.map f).subtype) =
      Module.length R (↥p ⧸ q.comap p.subtype) := by
  letI := RingHomInvPair.of_ringEquiv φ
  let g : ↥p →ₛₗ[(φ : R →+* R')] ↥(p.map f) :=
    { toFun := fun x => ⟨f x, Submodule.mem_map_of_mem x.2⟩
      map_add' := fun x y => Subtype.ext (map_add f (x : M) (y : M))
      map_smul' := fun r x => Subtype.ext (f.map_smulₛₗ r (x : M)) }
  refine length_quotient_eq_of_bijective_semilinear φ g ⟨?_, ?_⟩ _ _ ?_
  · intro x y hxy
    exact Subtype.ext (hf (congrArg Subtype.val hxy))
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    exact ⟨⟨x, hx⟩, rfl⟩
  · intro x
    show f x ∈ q.map f ↔ (x : M) ∈ q
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hx
      rw [← hf hyx]
      exact hy
    · intro hx
      exact Submodule.mem_map_of_mem hx
end Formalism.L2.NCov
