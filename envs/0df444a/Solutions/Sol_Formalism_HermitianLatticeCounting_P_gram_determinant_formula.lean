-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gram_determinant_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:26.651641+00:00
-- url     : https://prove2.me/submissions/23ebdd06-6f00-4a40-adb3-d4682ea0ded3

import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductPlacesInequalitySq
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LocalIntegralStructure
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gram_determinant_general

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
theorem _root_.solution : GramDet := by
  intro r Z T T'
  have h := gram_determinant_general ℂ r Z Z.conjTranspose (T : ℂ) (T' : ℂ)
  rw [h, ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose, Matrix.det_conjTranspose]
  congr 1
  have hs : ∀ z : ℂ, z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    first
      | exact Complex.mul_conj' z
      | (rw [Complex.star_def, Complex.mul_conj']; push_cast; ring)
      | (rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq])
  rw [mul_assoc ((T : ℂ) * (T' : ℂ)), hs, hs]
  push_cast <;> ring
end Formalism.HermitianLatticeCounting.P
