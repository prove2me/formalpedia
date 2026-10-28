-- Prove2me | solution 1 for D1Bound5.even_root_matrix_det_sq_char_two
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:27:39.53833+00:00
-- url     : https://prove2.me/submissions/fa7f703c-40bf-44a7-886e-00c1cab1d81f

import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Theorems.Thm_D1Bound5_det_identity_plus_two_rank_one

section
open scoped NumberField BigOperators
open Matrix Module

namespace D1Bound5



/-- Entrywise square data force determinant square one in characteristic
two and even dimension. Symmetry of the matrix is unnecessary. -/
theorem _root_.solution {R n : Type*} [CommRing R]
    [CharP R 2] [Fintype n] [DecidableEq n]
    (hn : Even (Fintype.card n)) (v : n → R) (M : Matrix n n R)
    (hd : ∀ i, M i i = v i)
    (hs : ∀ i j, i ≠ j → (M i j)^2 = v i*v j+1) : M.det^2 = 1 := by
  let F : R →+* R := frobenius R 2
  have hcard : (Fintype.card n : R) = 0 := by
    rw [CharTwo.natCast_eq_ite,if_pos hn]
  have hsum : (∑ i, v i^2) = (∑ i, v i)^2 := by
    exact (map_sum F v Finset.univ).symm
  have hM : M.map F = (fun i j => (if i=j then 1 else 0)+1+v i*v j) := by
    ext i j
    by_cases hij : i=j
    · subst j
      simp [Matrix.map_apply,F,frobenius_def,hd,pow_two,CharTwo.add_self_eq_zero]
    · simp [Matrix.map_apply,F,frobenius_def,hs i j hij,hij,add_comm]
  have hdet := RingHom.map_det F M
  change M.det^2 = (M.map F).det at hdet
  rw [hdet,hM,det_identity_plus_two_rank_one,hcard,hsum]
  ring







end D1Bound5
end
