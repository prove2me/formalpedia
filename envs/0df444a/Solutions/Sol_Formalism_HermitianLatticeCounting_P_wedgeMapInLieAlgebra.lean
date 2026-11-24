-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.wedgeMapInLieAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:23.8162+00:00
-- url     : https://prove2.me/submissions/01f62ff1-9c8e-4af6-9bd5-2b3b0bf2fae8

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_B_swap0
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_mono
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_le_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_perp_Xa
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_perp_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_X_iso
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_level_mem
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_level_mem_X
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
private theorem HermSpace_B_sub_left (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (x y z : V) : H.B (x - y) z = H.B x z - H.B y z := by
  rw [map_sub, LinearMap.sub_apply]
private theorem HermSpace_B_smul_left (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (c : K) (x y : V) : H.B (c • x) y = c * H.B x y := by
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
private theorem HermSpace_B_sub_right (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (x y z : V) : H.B x (y - z) = H.B x y - H.B x z :=
  map_sub _ _ _
private theorem HermSpace_B_smul_right_eq_star_mul (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (c : K) (x y : V) : H.B x (c • y) = star c * H.B x y := by
  rw [LinearMap.map_smulₛₗ, smul_eq_mul, starRingEnd_apply]
private theorem xv_apply_eq_B_smul_sub_B_smul (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (x v y : V) :
    Formalism.HermitianLatticeCounting.S6.xv H x v y = H.B y v • x - H.B y x • v := by
  simp only [Formalism.HermitianLatticeCounting.S6.xv, LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.flip_apply]
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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.Y1 := by
  intro K V _ _ _ _ H r F x v a al hx hv
  obtain ⟨hal, hxa⟩ := id hx
  have hxI : x ∈ F.X := (level_mem_X F) hx
  have hx1 : x ∈ F.Xa (a.val + 1) := (level_mem F) hx
  have hex : ∀ i : Fin (r + 1), H.B (F.e i) x = 0 := fun i => (e_X F) i hxI
  have hY : ∀ y, Formalism.HermitianLatticeCounting.S6.xv H x v y = H.B y v • x - H.B y x • v := xv_apply_eq_B_smul_sub_B_smul H x v
  have hYe : ∀ i : Fin (r + 1), Formalism.HermitianLatticeCounting.S6.xv H x v (F.e i) = H.B (F.e i) v • x := by
    intro i
    rw [hY, hex i, zero_smul, sub_zero]
  have hv' : ∀ y ∈ F.Xa (a.val + 1), H.B y v = 0 := by
    apply (perp_Xa F)
    intro b hb
    exact hv b (Fin.le_iff_val_le_val.2 (by omega))
  have hx' : ∀ y ∈ F.Xa (a.val + 1), H.B y x = 0 := fun y hy =>
    (X_iso F) ((Xa_le_X F) _ hy) hxI
  have hperp : ∀ y : V, (∀ b : Fin r, H.B (F.e b.castSucc) y = 0) → Formalism.HermitianLatticeCounting.S6.xv H x v y = H.B y v • x := by
    intro y hy
    have h1 : H.B x y = 0 := (perp_X F) hy x hxI
    rw [hY, B_swap0 H h1, zero_smul, sub_zero]
  have har := a.isLt
  refine ⟨fun y hy => by rw [hY, hv' y hy, hx' y hy]; simp, fun y hy => ?_, ?_, ?_⟩
  · rw [hperp y hy]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
  · unfold Formalism.HermitianLatticeCounting.S6.FlagD.LieN
    refine ⟨fun y y' => ?_, fun b => ?_, fun y hy => ?_⟩
    · simp only [hY, HermSpace_B_sub_left, HermSpace_B_smul_left, HermSpace_B_sub_right, HermSpace_B_smul_right_eq_star_mul]
      rw [H.herm y' v, H.herm y' x]
      ring
    · rw [hYe]
      by_cases hba : b ≤ a
      · rw [hv b hba, zero_smul]
        exact Submodule.zero_mem _
      · push_neg at hba
        exact Submodule.smul_mem _ _ ((Xa_mono F) (by have := Fin.lt_iff_val_lt_val.1 hba; omega) hx1)
    · rw [hperp y hy]
      exact Submodule.smul_mem _ _ hxI
  · unfold Formalism.HermitianLatticeCounting.S6.FlagD.DPsi
    refine ⟨fun b => if b = a then al * H.B (F.e a.succ) v else 0, by simp, fun b => ?_⟩
    dsimp only
    rw [hYe]
    rcases lt_trichotomy b a with hba | hba | hba
    · have hba' := Fin.lt_iff_val_lt_val.1 hba
      have hb1 : b.succ = (⟨b.val + 1, by omega⟩ : Fin r).castSucc := Fin.ext (by simp)
      have h0 : H.B (F.e b.succ) v = 0 := by
        rw [hb1]
        exact hv _ (Fin.le_iff_val_le_val.2 (show b.val + 1 ≤ a.val by omega))
      rw [h0, if_neg (ne_of_lt hba)]
      simp
    · subst hba
      rw [if_pos rfl, mul_comm, ← smul_smul, ← smul_sub]
      exact Submodule.smul_mem _ _ hxa
    · rw [if_neg (ne_of_gt hba), zero_smul, sub_zero]
      exact Submodule.smul_mem _ _ ((Xa_mono F) (by have := Fin.lt_iff_val_lt_val.1 hba; omega) hx1)
end Formalism.HermitianLatticeCounting.P
