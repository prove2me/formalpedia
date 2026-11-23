-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.eichlerMapIsometry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:35.697833+00:00
-- url     : https://prove2.me/submissions/e3f6519f-78d5-4c3b-ad43-f5a6f0d045a2

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_B_swap0
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
private theorem HermSpace_B_sub_left (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (x y z : V) : H.B (x - y) z = H.B x z - H.B y z := by
  rw [map_sub, LinearMap.sub_apply]
private theorem HermSpace_B_smul_left (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (c : K) (x y : V) : H.B (c • x) y = c * H.B x y := by
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
private theorem HermSpace_B_neg_left (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (x y : V) : H.B (-x) y = -H.B x y := by
  rw [map_neg, LinearMap.neg_apply]
private theorem HermSpace_B_add_right (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (x y z : V) : H.B x (y + z) = H.B x y + H.B x z :=
  map_add _ _ _
private theorem HermSpace_B_sub_right (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (x y z : V) : H.B x (y - z) = H.B x y - H.B x z :=
  map_sub _ _ _
private theorem HermSpace_B_smul_right_eq_star_mul (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (c : K) (x y : V) : H.B x (c • y) = star c * H.B x y := by
  rw [LinearMap.map_smulₛₗ, smul_eq_mul, starRingEnd_apply]
private theorem xv_apply_eq_B_smul_sub_B_smul (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (x v y : V) :
    Formalism.HermitianLatticeCounting.S6.xv H x v y = H.B y v • x - H.B y x • v := by
  simp only [Formalism.HermitianLatticeCounting.S6.xv, LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.flip_apply]
private theorem eich_apply_eq_add_wedge_add_smul (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (x v : V) (c : K) (y : V) :
    Formalism.HermitianLatticeCounting.S6.eich H x v c y = y + (H.B y v • x - H.B y x • v) + c • H.B y x • x := by
  simp only [Formalism.HermitianLatticeCounting.S6.eich, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
    LinearMap.flip_apply, xv_apply_eq_B_smul_sub_B_smul]
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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.EichlerIsom := by
  intro K V _ _ _ _ H x v c hxx hxv hc
  have hvx : H.B v x = 0 := B_swap0 H hxv
  have hcs : star c = -H.B v v - c := by linear_combination hc
  refine ⟨fun y y' => ?_, fun y => ?_, fun y => ?_⟩
  · simp only [eich_apply_eq_add_wedge_add_smul, HermSpace_B_add_left, HermSpace_B_sub_left, HermSpace_B_smul_left, HermSpace_B_add_right, HermSpace_B_sub_right, HermSpace_B_smul_right_eq_star_mul,
      H.herm, hxx, hxv, hvx]
    linear_combination (H.B y x * H.B x y') * hc
  · simp only [eich_apply_eq_add_wedge_add_smul, HermSpace_B_add_left, HermSpace_B_sub_left, HermSpace_B_smul_left, HermSpace_B_neg_left, map_neg, LinearMap.neg_apply, hxx, hxv, hvx]
    rw [hcs]
    module
  · simp only [eich_apply_eq_add_wedge_add_smul, HermSpace_B_add_left, HermSpace_B_sub_left, HermSpace_B_smul_left, HermSpace_B_neg_left, map_neg, LinearMap.neg_apply, hxx, hxv, hvx]
    rw [hcs]
    module
end Formalism.HermitianLatticeCounting.P
