-- Prove2me | solution 1 for Formalism.L2.NCov.length_quot_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:13:47.892608+00:00
-- url     : https://prove2.me/submissions/3e8c5178-c3da-4f3a-849d-3f40240b4fb9

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
theorem _root_.solution (φ : R ≃+* R') (n : ℕ) :
    Module.length R' (R' ⧸ Ideal.span {(n : R')}) = Module.length R (R ⧸ Ideal.span {(n : R)}) := by
  let F : R →ₛₗ[(φ : R →+* R')] R' :=
    { toFun := φ
      map_add' := map_add φ
      map_smul' := fun r x => by simp only [smul_eq_mul, map_mul, RingEquiv.coe_toRingHom] }
  refine length_quotient_eq_of_bijective_semilinear φ F φ.bijective _ _ ?_
  intro x
  show φ x ∈ Ideal.span {(n : R')} ↔ x ∈ Ideal.span {(n : R)}
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨φ.symm c, by apply φ.injective; simp [hc]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨φ c, by simp⟩
end Formalism.L2.NCov
