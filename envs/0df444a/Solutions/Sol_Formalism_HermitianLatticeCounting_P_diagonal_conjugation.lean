-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.diagonal_conjugation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:13:03.207048+00:00
-- url     : https://prove2.me/submissions/74a58a58-57db-4c96-b820-162fb427e43d

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : DiagConj := by
  intro ga T T' hT hT'
  have h1 : (Real.sqrt T : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hT).ne'
  have h2 : (Real.sqrt T' : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hT').ne'
  have hinv : (Matrix.diagonal ![(Real.sqrt T : ℂ), (Real.sqrt T' : ℂ)])⁻¹ =
      Matrix.diagonal ![(Real.sqrt T : ℂ)⁻¹, (Real.sqrt T' : ℂ)⁻¹] := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext i j; fin_cases i <;> fin_cases j <;> simp [h1, h2]
  rw [hinv]
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]
  field_simp
end Formalism.HermitianLatticeCounting.P
