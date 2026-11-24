-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gram_determinant_general
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:03.279191+00:00
-- url     : https://prove2.me/submissions/b7b60b6c-74ac-42fd-b08b-69acc46c18f1

import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductPlacesInequalitySq
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LocalIntegralStructure
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_cofactor_vector_formula
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_det_swap_blocks_alt
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_det_from_blocks_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Formalism.HermitianLatticeCounting.LocalIntegralStructure nonZeroDivisors
set_option linter.all false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Matrix Polynomial
variable {R : Type} [CommRing R]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : GramDetGen := by
  intro R _ r Z W t t'
  have hdiag : ∀ s : R, (Matrix.diagonal fun i : Fin (r + 1) => if i = Fin.last r then -s else 0) =
      (-s) • Matrix.single (Fin.last r) (Fin.last r) (1 : R) := by
    intro s
    ext i j
    by_cases hi : i = Fin.last r
    · subst hi
      by_cases hj : j = Fin.last r
      · subst hj
        simp
      · simp [Matrix.diagonal_apply, Matrix.single_apply, Ne.symm hj]
    · simp [Matrix.diagonal_apply, Matrix.single_apply, hi, Ne.symm hi]
  have hS : Matrix.fromBlocks (Matrix.diagonal fun i : Fin (r + 1) => if i = Fin.last r then -t else 0) W Z
      (Matrix.diagonal fun i : Fin (r + 1) => if i = Fin.last r then -t' else 0) *
      Matrix.fromBlocks 0 1 1 0 =
      Matrix.fromBlocks W ((-t) • Matrix.single (Fin.last r) (Fin.last r) (1 : R))
        ((-t') • Matrix.single (Fin.last r) (Fin.last r) (1 : R)) Z := by
    rw [hdiag t, hdiag t', Matrix.fromBlocks_multiply]
    simp
  have hdetS := det_swap_blocks_alt (R := R) (n := Fin (r + 1))
  have hB := det_from_blocks_single r W Z (Fin.last r) t t'
  have hcW := (cofactor_vector_formula R r W).2
  have hcZ := (cofactor_vector_formula R r Z).2
  have h1 := congrArg Matrix.det hS
  rw [Matrix.det_mul, hdetS, Fintype.card_fin, hB, hcW, hcZ] at h1
  have hsq : ((-1 : R) ^ (r + 1)) * ((-1) ^ (r + 1)) = 1 := by
    rw [← mul_pow]
    simp
  have key : ∀ x : R, x * (-1) ^ (r + 1) = W.det * Z.det - t * t' *
      (W.submatrix Fin.castSucc Fin.castSucc).det * (Z.submatrix Fin.castSucc Fin.castSucc).det →
      x = (-1) ^ (r + 1) * (Z.det * W.det - t * t' * (Z.submatrix Fin.castSucc Fin.castSucc).det *
        (W.submatrix Fin.castSucc Fin.castSucc).det) := by
    intro x hx
    linear_combination ((-1 : R) ^ (r + 1)) * hx - x * hsq
  exact key _ h1
end Formalism.HermitianLatticeCounting.P
