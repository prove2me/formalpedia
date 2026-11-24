-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.normSqScalarMulEq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:44.727881+00:00
-- url     : https://prove2.me/submissions/32a972fb-b4a0-4590-a7e4-bd2ce63c0de4

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_B_swap0
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_X_iso
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pairing_isotropicSpan_lastVector
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_z_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pairing_lastVector_lastVector
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
private theorem HermSpace_B_smul_left (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (c : K) (x y : V) : H.B (c • x) y = c * H.B x y := by
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
private theorem HermSpace_B_add_right (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (x y z : V) : H.B x (y + z) = H.B x y + H.B x z :=
  map_add _ _ _
private theorem HermSpace_B_sub_right (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (x y z : V) : H.B x (y - z) = H.B x y - H.B x z :=
  map_sub _ _ _
private theorem HermSpace_B_smul_right_eq_star_mul (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (c : K) (x y : V) : H.B x (c • y) = star c * H.B x y := by
  rw [LinearMap.map_smulₛₗ, smul_eq_mul, starRingEnd_apply]
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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.NFAbsC := by
  intro K V _ _ _ _ H r F F' j hj c _ _ hz _
  obtain ⟨u, hu, u', hu', hsum⟩ := Submodule.mem_sup.1 hz
  obtain ⟨p, hp⟩ : ∃ p : V, p = c • F.z + u := ⟨_, rfl⟩
  have hz' : F'.z = p + u' := by
    rw [hp, add_assoc, hsum]
    abel
  have hpp : H.B p p = -(c * star c * F.T) := by
    rw [hp]
    simp only [HermSpace_B_add_left, HermSpace_B_add_right, HermSpace_B_smul_left, HermSpace_B_smul_right_eq_star_mul, (pairing_lastVector_lastVector F),
      (z_X F) hu, (pairing_isotropicSpan_lastVector F) hu,
      (X_iso F) hu hu]
    ring
  have hu'z' : H.B u' F'.z = 0 := (pairing_isotropicSpan_lastVector F') hu'
  have hu'u' : H.B u' u' = 0 := (X_iso F') hu' hu'
  have hu'p : H.B u' p = 0 := by
    have hp' : p = F'.z - u' := by
      rw [hz']
      abel
    rw [hp', HermSpace_B_sub_right, hu'z', hu'u', sub_zero]
  have hpu' : H.B p u' = 0 := B_swap0 H hu'p
  have h1 : H.B F'.z F'.z = -F'.T := (pairing_lastVector_lastVector F')
  rw [hz', HermSpace_B_add_left, HermSpace_B_add_right, HermSpace_B_add_right, hpp, hpu', hu'p, hu'u'] at h1
  linear_combination -h1
end Formalism.HermitianLatticeCounting.P
