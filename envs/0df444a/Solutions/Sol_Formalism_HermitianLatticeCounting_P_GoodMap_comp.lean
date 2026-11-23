-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.GoodMap.comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:41.486199+00:00
-- url     : https://prove2.me/submissions/f36a19d7-f7bf-4c59-856b-3a240657fb4c

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_X_iso
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
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
namespace Formalism.HermitianLatticeCounting.P
namespace GoodMap
theorem _root_.solution (F F' : FlagD H r) {g g' : V →ₗ[K] V} (hg : GoodMap F F' g) (hg' : GoodMap F F' g') :
    GoodMap F F' (g ∘ₗ g') := by
  obtain ⟨hiso, hbij, hfix, hmeet⟩ := id hg
  obtain ⟨hiso', hbij', hfix', hmeet'⟩ := id hg'
  unfold Formalism.HermitianLatticeCounting.P.GoodMap
  refine ⟨fun x y => ?_, ?_, fun y hy => ?_, fun y hy => ?_⟩
  · simp only [LinearMap.comp_apply]
    rw [hiso, hiso']
  · rw [LinearMap.coe_comp]
    exact hbij.comp hbij'
  · simp only [LinearMap.comp_apply]
    rw [hfix' y hy, hfix y hy]
  · simp only [LinearMap.comp_apply]
    have h1 := hmeet' y hy
    have h2 : ∀ u ∈ Formalism.HermitianLatticeCounting.S6.II F F', H.B u (g' y) = 0 := by
      intro u hu
      have hgy : g' y = y + (g' y - y) := by abel
      rw [hgy, _root_.Formalism.HermitianLatticeCounting.P.HermSpace_B_add_right, hy u hu, zero_add]
      exact (Formalism.HermitianLatticeCounting.P.X_iso F) (Submodule.mem_inf.1 hu).1 (Submodule.mem_inf.1 h1).1
    have h3 := hmeet (g' y) h2
    have hsplit : g (g' y) - y = (g (g' y) - g' y) + (g' y - y) := by abel
    rw [hsplit]
    exact Submodule.add_mem _ h3 h1
end GoodMap
end Formalism.HermitianLatticeCounting.P
