-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.good_family
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:28.39878+00:00
-- url     : https://prove2.me/submissions/39c8e1c4-06ce-448d-b4ed-b6d585a57f0f

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pairing_jointSpan_isotropicMeet
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_isotropicMeet_le_jointSpan
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_GoodMap_comp
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_eich_good
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_eich_perp
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_exists_half
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
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (hE : Formalism.HermitianLatticeCounting.S6.EichlerIsom) (hR : Formalism.HermitianLatticeCounting.S6.EichlerInR) (F F' : FlagD H r) (hμ : ∃ μ : K, μ + star μ ≠ 0) (n : ℕ) (x v : Fin n → V)
    (hx : ∀ i, x i ∈ II F F') (hv : ∀ i, ∀ y ∈ V0 F F', H.B y (v i) = 0) :
    ∃ g : V →ₗ[K] V, GoodMap F F' g ∧
      ∀ w : V, (∀ y ∈ V0 F F', H.B y w = 0) → g w = w + ∑ i, H.B w (v i) • x i := by
  induction n with
  | zero =>
    refine ⟨LinearMap.id, ?_, fun w _ => by simp⟩
    unfold GoodMap
    refine ⟨fun _ _ => rfl, Function.bijective_id, fun _ _ => rfl, fun y _ => by simp⟩
  | succ n ih =>
    obtain ⟨g₀, hg₀, hg₀w⟩ := ih (fun i => x i.castSucc) (fun i => v i.castSucc) (fun i => hx _) (fun i => hv _)
    obtain ⟨c, hc⟩ := exists_half hμ (H.B (v (Fin.last n)) (v (Fin.last n))) (H.herm _ _)
    have hE' := eich_good hE F F' (hx (Fin.last n)) (hv (Fin.last n)) hc
    refine ⟨Formalism.HermitianLatticeCounting.S6.eich H (x (Fin.last n)) (v (Fin.last n)) c ∘ₗ g₀, Formalism.HermitianLatticeCounting.P.GoodMap.comp F F' hE' hg₀,
      fun w hw => ?_⟩
    rw [LinearMap.comp_apply, hg₀w w hw]
    have hsum : ∑ i : Fin n, H.B w (v i.castSucc) • x i.castSucc ∈ Formalism.HermitianLatticeCounting.S6.II F F' :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hx _)
    have hw' : ∀ y ∈ Formalism.HermitianLatticeCounting.S6.V0 F F', H.B y (w + ∑ i : Fin n, H.B w (v i.castSucc) • x i.castSucc) = 0 := by
      intro y hy
      rw [HermSpace_B_add_right, hw y hy, pairing_jointSpan_isotropicMeet F F' hsum y hy, add_zero]
    rw [eich_perp F F' (hx (Fin.last n)) hw', Fin.sum_univ_castSucc]
    have h0 : H.B (∑ i : Fin n, H.B w (v i.castSucc) • x i.castSucc) (v (Fin.last n)) = 0 :=
      hv _ _ (isotropicMeet_le_jointSpan F F' hsum)
    rw [HermSpace_B_add_left, h0, add_zero, add_assoc]
end Formalism.HermitianLatticeCounting.P
