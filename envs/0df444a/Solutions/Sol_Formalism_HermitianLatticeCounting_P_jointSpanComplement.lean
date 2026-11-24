-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.jointSpanComplement
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:37.367072+00:00
-- url     : https://prove2.me/submissions/b290daab-f3d1-4dcb-8ce2-60f47b810cd5

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_perp_sup
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_le_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_perp_Xa
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_perp_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_X_iso
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_z_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Dl_solveL
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pairing_eq_zero_of_mem_jointSpan
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pairing_lastVector_right_eq_zero
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
private theorem HermSpace_B_sub_right (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (x y z : V) : H.B x (y - z) = H.B x y - H.B x z :=
  map_sub _ _ _
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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.JointSpanComplement := by
  intro K V _ _ _ _ H r F F' j hj c hI' hz hD w hw
  obtain ⟨x, hx, hxt⟩ := Dl_solveL F F' hj hD
    (fun b => H.B w (F'.e (Fin.castLE (hj.trans (Nat.le_succ r)) b)))
  have hxI : x ∈ F.X := (Xa_le_X F) j hx
  refine ⟨x, hxI, ?_⟩
  have hwI : ∀ u ∈ F.X, H.B u w = 0 := (perp_X F) (fun b => hw b.castSucc)
  have h1 : ∀ u ∈ F.X, H.B u (w - x) = 0 := fun u hu => by
    rw [HermSpace_B_sub_right, hwI u hu, (X_iso F) hu hxI, sub_zero]
  have h3 : H.B F.z (w - x) = 0 := by
    rw [HermSpace_B_sub_right, (z_X F) hxI, sub_zero]
    exact hw (Fin.last r)
  have h2 : ∀ u ∈ F'.X, H.B u (w - x) = 0 := by
    rw [hI']
    apply perp_sup H
    · apply (perp_Xa F')
      intro b hb
      have h4 : H.B x (F'.e b.castSucc) = H.B w (F'.e b.castSucc) := hxt ⟨b.val, hb⟩
      rw [HermSpace_B_sub_right, ← H.herm x, h4, H.herm, sub_self]
    · intro u hu
      exact h1 u (Submodule.mem_inf.1 hu).1
  exact pairing_eq_zero_of_mem_jointSpan F F' h1 h2 h3 (pairing_lastVector_right_eq_zero F F' hz h1 h2 h3)
end Formalism.HermitianLatticeCounting.P
