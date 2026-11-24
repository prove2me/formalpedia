-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.exists_row
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:51.870054+00:00
-- url     : https://prove2.me/submissions/88ab35f0-ab04-4bc0-ad18-cfe00e6cedfd

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_CardStabilizerVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.LogVandermondeBounds.StandardLattice
open Finset
private theorem vecMul_one_add_vecMulVec_single {F : Type} [Field F] {n : ℕ} (k : Fin n)
    (c z : Fin n → F) :
    Matrix.vecMul z (1 + Matrix.vecMulVec (Pi.single k 1) c) = z + z k • c := by
  rw [Matrix.vecMul_add, Matrix.vecMul_one]
  congr 1
  funext j
  simp [Matrix.vecMul, dotProduct, Matrix.vecMulVec_apply, Pi.single_apply]
private theorem single_one_vecMul_apply {F : Type} [Field F] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    Matrix.vecMul (Pi.single i 1) M j = M i j := by
  simp [Matrix.vecMul, dotProduct, Pi.single_apply]
private theorem one_add_vecMulVec_single_mul_inverse_eq_one {F : Type} [Field F] {n : ℕ} (k : Fin n)
    (x y : Fin n → F) (hx : x k ≠ 0) (hy : y k ≠ 0) :
    (1 + Matrix.vecMulVec (Pi.single k 1) ((x k)⁻¹ • (y - x))) *
      (1 + Matrix.vecMulVec (Pi.single k 1) ((y k)⁻¹ • (x - y))) = 1 := by
  have key : ∀ z : Fin n → F, Matrix.vecMul z
      ((1 + Matrix.vecMulVec (Pi.single k 1) ((x k)⁻¹ • (y - x))) *
        (1 + Matrix.vecMulVec (Pi.single k 1) ((y k)⁻¹ • (x - y)))) = z := by
    intro z
    rw [← Matrix.vecMul_vecMul, vecMul_one_add_vecMulVec_single,
      vecMul_one_add_vecMulVec_single]
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  ext i j
  have h1 := congrFun (key (Pi.single i 1)) j
  rw [single_one_vecMul_apply] at h1
  rw [h1]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]
private theorem exists_GL_vecMul_eq_of_ne_zero_at {F : Type} [Field F] {n : ℕ} (k : Fin n)
    (x y : Fin n → F) (hx : x k ≠ 0) (hy : y k ≠ 0) :
    ∃ A : GL (Fin n) F, Matrix.vecMul x (A : Matrix (Fin n) (Fin n) F) = y := by
  refine ⟨(⟨1 + Matrix.vecMulVec (Pi.single k 1) ((x k)⁻¹ • (y - x)),
    1 + Matrix.vecMulVec (Pi.single k 1) ((y k)⁻¹ • (x - y)),
    one_add_vecMulVec_single_mul_inverse_eq_one k x y hx hy,
    one_add_vecMulVec_single_mul_inverse_eq_one k y x hy hx⟩ : (Matrix (Fin n) (Fin n) F)ˣ), ?_⟩
  show Matrix.vecMul x (1 + Matrix.vecMulVec (Pi.single k 1) ((x k)⁻¹ • (y - x))) = y
  rw [vecMul_one_add_vecMulVec_single]
  funext j
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [mul_inv_cancel_left₀ hx]
  ring
end Formalism.LogVandermondeBounds.StandardLattice
end

set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution {F : Type} [Field F] [Fintype F] {n : ℕ} (v w : Fin n → F) (hv : v ≠ 0)
    (hw : w ≠ 0) : ∃ A : GL (Fin n) F, Matrix.vecMul v (A : Matrix (Fin n) (Fin n) F) = w := by
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra h
    exact hv (funext fun i => not_not.mp fun hi => h ⟨i, hi⟩)
  obtain ⟨l, hl⟩ : ∃ l, w l ≠ 0 := by
    by_contra h
    exact hw (funext fun i => not_not.mp fun hi => h ⟨i, hi⟩)
  obtain ⟨A, hA⟩ := exists_GL_vecMul_eq_of_ne_zero_at k v (fun _ : Fin n => (1 : F)) hk one_ne_zero
  obtain ⟨B, hB⟩ := exists_GL_vecMul_eq_of_ne_zero_at l (fun _ : Fin n => (1 : F)) w one_ne_zero hl
  refine ⟨A * B, ?_⟩
  rw [Units.val_mul, ← Matrix.vecMul_vecMul, hA, hB]
end Formalism.LogVandermondeBounds.StandardLattice
