-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.normalFormMinorNeZero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:21.37374+00:00
-- url     : https://prove2.me/submissions/6324bccf-f11b-44a4-aacd-19dfc267f166

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_B_swap0
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_perp_sup
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_mem_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_perp_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_X_iso
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pairing_isotropicSpan_lastVector
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_z_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pairing_lastVector_lastVector
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Dl_eq
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Dl_swap
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Dl_solveL
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
private theorem det_eq_last_mul_det_submatrix_of_last_row_eq_zero {R : Type} [CommRing R] {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (h : ∀ j : Fin m, A (Fin.last m) j.castSucc = 0) :
    A.det = A (Fin.last m) (Fin.last m) * (A.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row A (Fin.last m), Fin.sum_univ_castSucc]
  simp only [h, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Fin.succAbove_last, Fin.val_last]
  rw [show ((-1 : R) ^ (m + m)) = 1 from Even.neg_one_pow ⟨m, rfl⟩, one_mul]
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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.NFCaseB := by
  intro K V _ _ _ _ H r F F' hD
  have hD' : Formalism.HermitianLatticeCounting.S6.Dl F' F r (Nat.le_succ r) ≠ 0 := by
    rw [Dl_swap]
    exact fun h => hD (star_eq_zero.1 h)
  obtain ⟨x, hx, hxe⟩ := Dl_solveL F F' (le_refl r) hD
    (fun b => H.B F.z (F'.e b.castSucc))
  obtain ⟨x', hx', hxe'⟩ := Dl_solveL F' F (le_refl r) hD'
    (fun a => H.B F'.z (F.e a.castSucc))
  have hxI : x ∈ F.X := hx
  have hxI' : x' ∈ F'.X := hx'
  have hxe2 : ∀ b : Fin r, H.B x (F'.e b.castSucc) = H.B F.z (F'.e b.castSucc) := fun b => hxe b
  have hxe2' : ∀ a : Fin r, H.B x' (F.e a.castSucc) = H.B F'.z (F.e a.castSucc) := fun a => hxe' a
  have h1 : ∀ w ∈ F.X ⊔ F'.X, H.B w (F.z - x) = 0 := by
    apply perp_sup H
    · intro s hs
      rw [HermSpace_B_sub_right, (pairing_isotropicSpan_lastVector F) hs, (X_iso F) hs hxI, sub_zero]
    · exact (perp_X F')
        (fun b => B_swap0 H (by rw [HermSpace_B_sub_left, hxe2 b, sub_self]))
  have h2 : ∀ w ∈ F.X ⊔ F'.X, H.B w (F'.z - x') = 0 := by
    apply perp_sup H
    · exact (perp_X F)
        (fun a => B_swap0 H (by rw [HermSpace_B_sub_left, hxe2' a, sub_self]))
    · intro s hs
      rw [HermSpace_B_sub_right, (pairing_isotropicSpan_lastVector F') hs, (X_iso F') hs hxI', sub_zero]
  have h3 : H.B (F.z - x) (F.z - x) = -F.T := by
    rw [HermSpace_B_sub_left, h1 x (Submodule.mem_sup_left hxI), sub_zero, HermSpace_B_sub_right,
      (z_X F) hxI, sub_zero]
    exact (pairing_lastVector_lastVector F)
  have h4 : H.B (F'.z - x') (F'.z - x') = -F'.T := by
    rw [HermSpace_B_sub_left, h2 x' (Submodule.mem_sup_right hxI'), sub_zero, HermSpace_B_sub_right,
      (z_X F') hxI', sub_zero]
    exact (pairing_lastVector_lastVector F')
  obtain ⟨P, hPdef⟩ : ∃ P : Matrix (Fin (r + 1)) (Fin (r + 1)) K,
      P = Matrix.of fun a b => H.B (F.e a) (F'.e b) := ⟨_, rfl⟩
  have hrowdet : ∀ y ∈ F.X, (P.updateRow (Fin.last r) (fun b => H.B y (F'.e b))).det = 0 := by
    let f : V →ₗ[K] K :=
      { toFun := fun y => (P.updateRow (Fin.last r) (fun b => H.B y (F'.e b))).det
        map_add' := fun y y' => by
          simp only [HermSpace_B_add_left]
          exact Matrix.det_updateRow_add P (Fin.last r) (fun b => H.B y (F'.e b)) (fun b => H.B y' (F'.e b))
        map_smul' := fun c y => by
          simp only [HermSpace_B_smul_left, RingHom.id_apply, smul_eq_mul]
          exact Matrix.det_updateRow_smul P (Fin.last r) c (fun b => H.B y (F'.e b)) }
    have hle : F.X ≤ LinearMap.ker f := by
      show Submodule.span K ((fun b : Fin r => F.e b.castSucc) '' {b | b.val < r}) ≤ LinearMap.ker f
      rw [Submodule.span_le]
      rintro _ ⟨a, -, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      show (P.updateRow (Fin.last r) (fun b => H.B (F.e a.castSucc) (F'.e b))).det = 0
      apply Matrix.det_zero_of_row_eq (Fin.castSucc_ne_last a)
      rw [Matrix.updateRow_self, Matrix.updateRow_ne (Fin.castSucc_ne_last a)]
      funext b
      simp [hPdef]
    intro y hy
    exact LinearMap.mem_ker.1 (hle hy)
  have hzrow : (fun b => H.B F.z (F'.e b)) = P (Fin.last r) := by
    funext b
    simp [hPdef, Formalism.HermitianLatticeCounting.S6.FlagD.z]
  have hQ : (P.updateRow (Fin.last r) (fun b => H.B (F.z - x) (F'.e b))).det = P.det := by
    have e1 : (fun b => H.B (F.z - x) (F'.e b)) =
        (fun b => H.B F.z (F'.e b)) + (-1 : K) • (fun b => H.B x (F'.e b)) := by
      funext b
      simp only [HermSpace_B_sub_left, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, hrowdet x hxI, mul_zero, add_zero, hzrow,
      Matrix.updateRow_eq_self]
  have hlast : ∀ j : Fin r,
      (P.updateRow (Fin.last r) (fun b => H.B (F.z - x) (F'.e b))) (Fin.last r) j.castSucc = 0 := by
    intro j
    rw [Matrix.updateRow_self]
    exact B_swap0 H (h1 _ (Submodule.mem_sup_right ((e_mem_X F') j)))
  have hsub : (P.updateRow (Fin.last r) (fun b => H.B (F.z - x) (F'.e b))).submatrix Fin.castSucc Fin.castSucc =
      Matrix.of fun a b : Fin r => H.B (F.e (Fin.castLE (Nat.le_succ r) a)) (F'.e (Fin.castLE (Nat.le_succ r) b)) := by
    ext a b
    simp [hPdef, Matrix.updateRow_ne (Fin.castSucc_ne_last a)] <;> rfl
  have hP : Formalism.HermitianLatticeCounting.S6.Dl F F' (r + 1) le_rfl = P.det := by
    rw [hPdef]
    exact Dl_eq F F' (r + 1) le_rfl
  have hLr := Dl_eq F F' r (Nat.le_succ r)
  have hbb : H.B (F.z - x) (F'.e (Fin.last r)) = H.B (F.z - x) (F'.z - x') := by
    rw [HermSpace_B_sub_right H (F.z - x) F'.z x',
      B_swap0 H (h1 x' (Submodule.mem_sup_right hxI')), sub_zero]
    rfl
  have hlm : Formalism.HermitianLatticeCounting.S6.Dl F F' (r + 1) le_rfl =
      Formalism.HermitianLatticeCounting.S6.Dl F F' r (Nat.le_succ r) * H.B (F.z - x) (F'.z - x') := by
    rw [hP, ← hQ, det_eq_last_mul_det_submatrix_of_last_row_eq_zero _ hlast, hsub, ← hLr, Matrix.updateRow_self, ← hbb]
    exact mul_comm _ _
  refine ⟨x, hxI, x', hxI', h1, h2, h3, h4, hlm, ?_⟩
  unfold Formalism.HermitianLatticeCounting.S6.Gval
  rw [hlm, star_mul']
  ring
end Formalism.HermitianLatticeCounting.P
