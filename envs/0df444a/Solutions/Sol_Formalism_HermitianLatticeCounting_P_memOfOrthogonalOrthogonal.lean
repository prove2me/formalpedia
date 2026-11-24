-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.memOfOrthogonalOrthogonal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:39.406412+00:00
-- url     : https://prove2.me/submissions/f3c3cae7-8ae7-48a3-874b-9362a7b37a9b

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
namespace Formalism.HermitianLatticeCounting.P
section Base
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
end Base
private theorem HermSpace_exists_B_right_eq_linearForm {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (f : V →ₗ[K] K) : ∃ v : V, ∀ u : V, H.B u v = f u := by
  let b := Module.finBasis K V
  let Ψ : V →ₗ[K] (Fin (Module.finrank K V) → K) := LinearMap.pi fun i => H.B.flip (b i)
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    apply H.nondeg v
    have hb : ∀ i, H.B v (b i) = 0 := fun i => by simpa [Ψ] using congrFun hv i
    have h0 : H.B v = 0 := b.ext fun i => by rw [hb i, LinearMap.zero_apply]
    intro y
    rw [h0, LinearMap.zero_apply]
  have hsurj : Function.Surjective Ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hΨ
  obtain ⟨v, hv⟩ := hsurj (fun i => star (f (b i)))
  refine ⟨v, fun u => ?_⟩
  have hfl : H.B.flip v = f := b.ext fun i => by
    have h1 := congrFun hv i
    simp only [Ψ, LinearMap.pi_apply, LinearMap.flip_apply] at h1
    rw [LinearMap.flip_apply, ← H.herm v (b i), h1, star_star]
  have := LinearMap.congr_fun hfl u
  simpa using this
section Base2
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
end Base2
section CaseA
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {H : HermSpace K V} {r : ℕ}
end CaseA
section Gram
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
end Gram
section V0
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
end V0
section Sig
variable {K U : Type} [Field K] [StarRing K] [AddCommGroup U] [Module K U]
end Sig
section Perp
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
end Perp
section DetBlocks
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
end DetBlocks
section Lift
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
end Lift
end Formalism.HermitianLatticeCounting.P
end

set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.PerpPerp := by
  intro K V _ _ _ _ _ H S w hw
  by_contra hwS
  have hq : S.mkQ w ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hwS
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K (V ⧸ S), φ (S.mkQ w) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hq ((Module.forall_dual_apply_eq_zero_iff K _).1 h)
  obtain ⟨v, hv⟩ := HermSpace_exists_B_right_eq_linearForm H (φ.comp S.mkQ)
  apply hφ
  have h1 := hw v (fun s hs => by
    rw [hv s, LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero S).2 hs, map_zero])
  rw [hv w, LinearMap.comp_apply] at h1
  exact h1
end Formalism.HermitianLatticeCounting.P
