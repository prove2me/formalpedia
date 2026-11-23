-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.lastVectorNotMemSup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:19.032858+00:00
-- url     : https://prove2.me/submissions/0347e06d-deec-4263-867e-56499e0b1b53

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_B_swap0
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_X_iso
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_z_X
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
private theorem HermSpace_B_add_left (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (x y z : V) : H.B (x + y) z = H.B x z + H.B y z := by
  rw [map_add, LinearMap.add_apply]
private theorem HermSpace_B_add_right (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (x y z : V) : H.B x (y + z) = H.B x y + H.B x z :=
  map_add _ _ _
end Base
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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.LastVectorNotMemSup := by
  intro K V _ _ _ _ H r F F' hz
  obtain ⟨u, hu, u', hu', hsum⟩ := Submodule.mem_sup.1 hz
  have hzu : H.B F.z u = 0 := (z_X F) hu
  have huu : H.B u u = 0 := (X_iso F) hu hu
  have hu'u' : H.B u' u' = 0 := (X_iso F') hu' hu'
  have e1 : H.B F.z F.z = H.B u u' := by
    have h1 : H.B F.z (u + u') = H.B F.z F.z := by rw [hsum]
    rw [HermSpace_B_add_right, hzu, zero_add] at h1
    rw [← h1, ← hsum, HermSpace_B_add_left, hu'u', add_zero]
  have e2 : H.B F.z F.z = H.B u u' + H.B u' u := by
    rw [← hsum, HermSpace_B_add_left, HermSpace_B_add_right, HermSpace_B_add_right, huu, hu'u']
    ring
  have h3 : H.B u' u = 0 := by
    rw [e1] at e2
    linear_combination -e2
  have h4 : H.B u u' = 0 := B_swap0 H h3
  have h5 : H.B F.z F.z = -F.T := F.zz
  rw [e1, h4] at h5
  exact F.hT (neg_eq_zero.1 h5.symm)
end Formalism.HermitianLatticeCounting.P
