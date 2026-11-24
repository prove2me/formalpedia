-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.leadingMinorNeZero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:30.557923+00:00
-- url     : https://prove2.me/submissions/360188cc-c80c-4a15-b7f2-acdb9d4e8257

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_B_swap0
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_perp_sup
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_le_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_mem_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_X_iso
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pairing_isotropicSpan_lastVector
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Dl_zeroL
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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.NFDj := by
  intro K V _ _ _ _ H r F F' j hj c hA' hb hI' hz hD
  obtain ⟨x, hx, hx0, hxu⟩ := Dl_zeroL F F' hj hD
  have hxI : x ∈ F.X := (Xa_le_X F) j hx
  have hxI' : ∀ u ∈ F'.X, H.B x u = 0 := by
    rw [hI']
    intro u hu
    obtain ⟨y, hy, m, hm, rfl⟩ := Submodule.mem_sup.1 hu
    rw [HermSpace_B_add_right, hxu y hy, (X_iso F) hxI (Submodule.mem_inf.1 hm).1, add_zero]
  have hxS : ∀ u ∈ F.X ⊔ F'.X, H.B u x = 0 := by
    apply perp_sup H
    · intro u hu
      exact (X_iso F) hu hxI
    · intro u hu
      exact B_swap0 H (hxI' u hu)
  have hxz' : H.B x F'.z = 0 := by
    have h1 := B_swap0 H (hxS _ hz)
    rw [HermSpace_B_sub_right, HermSpace_B_smul_right_eq_star_mul, (pairing_isotropicSpan_lastVector F) hxI, mul_zero, sub_zero] at h1
    exact h1
  have hxF' : x ∈ F'.X := by
    apply hA' x
    · intro a
      apply B_swap0 H
      induction a using Fin.lastCases with
      | last => exact hxz'
      | cast b => exact hxI' _ ((e_mem_X F') b)
    · exact (X_iso F) hxI hxI
  have hmem : x ∈ Formalism.HermitianLatticeCounting.S6.II F F' ⊓ F.Xa j := Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hxI, hxF'⟩, hx⟩
  rw [hb] at hmem
  exact hx0 ((Submodule.mem_bot K).1 hmem)
end Formalism.HermitianLatticeCounting.P
