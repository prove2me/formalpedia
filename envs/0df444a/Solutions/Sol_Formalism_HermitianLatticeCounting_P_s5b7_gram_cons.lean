-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5b7_gram_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:50.875914+00:00
-- url     : https://prove2.me/submissions/89885351-932a-44c7-815f-5e33ea425b70

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Module Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (r : ℕ) (v0 : V)
    (c : Fin r → ℂ) (w : Fin r → V) (hw : ∀ b, inner ℂ v0 (w b) = 0) :
    (Matrix.gram ℂ (Fin.cons v0 (fun b => c b • v0 + w b) : Fin (r + 1) → V)).det =
      ((‖v0‖ : ℂ) ^ 2) * (Matrix.gram ℂ w).det := by
  set v : Fin (r + 1) → V := Fin.cons v0 (fun b => c b • v0 + w b) with hv
  set v' : Fin (r + 1) → V := Fin.cons v0 w with hv'
  let cc : Fin (r + 1) → ℂ := Fin.cons 0 c
  have hvv : ∀ i, v i = cc i • v0 + v' i - (if i = 0 then 0 else 0) := by
    intro i
    refine Fin.cases ?_ (fun b => ?_) i
    · simp [hv, hv', cc]
    · simp [hv, hv', cc]
  have hvv' : ∀ i, v i = cc i • v' 0 + v' i := by
    intro i
    rw [hvv i]; simp [hv']
  have h1 : (Matrix.gram ℂ v).det = (Matrix.of fun i j => inner ℂ (v' i) (v j)).det := by
    refine Matrix.det_eq_of_forall_row_eq_smul_add_const (fun i => conj (cc i)) 0 (by simp [cc]) ?_
    intro i j
    rw [Matrix.gram_apply, hvv' i, inner_add_left, inner_smul_left]
    simp only [Matrix.of_apply]
    ring
  have h2 : (Matrix.of fun i j => inner ℂ (v' i) (v j)).det = (Matrix.gram ℂ v').det := by
    rw [← Matrix.det_transpose, ← Matrix.det_transpose (Matrix.gram ℂ v')]
    refine Matrix.det_eq_of_forall_row_eq_smul_add_const cc 0 (by simp [cc]) ?_
    intro i j
    rw [Matrix.transpose_apply, Matrix.transpose_apply, Matrix.transpose_apply, Matrix.of_apply,
      Matrix.gram_apply, Matrix.gram_apply, hvv' i, inner_add_right, inner_smul_right]
    ring
  rw [h1, h2, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have h3 : ∀ j : Fin r, Matrix.gram ℂ v' 0 j.succ = 0 := by
    intro j
    rw [Matrix.gram_apply]
    simpa [hv'] using hw j
  have h4 : (Matrix.gram ℂ v').submatrix Fin.succ (Fin.succAbove 0) = Matrix.gram ℂ w := by
    ext i j
    simp [Matrix.gram_apply, hv']
  have h5 : Matrix.gram ℂ v' 0 0 = (‖v0‖ : ℂ) ^ 2 := by
    rw [Matrix.gram_apply]
    simp [hv', inner_self_eq_norm_sq_to_K]
  rw [Finset.sum_eq_zero (fun j _ => by rw [h3 j]; ring), h4, h5]
  simp
end Formalism.HermitianLatticeCounting.P
