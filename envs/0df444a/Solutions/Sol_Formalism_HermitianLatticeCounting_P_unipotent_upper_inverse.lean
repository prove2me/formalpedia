-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.unipotent_upper_inverse
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:41.495+00:00
-- url     : https://prove2.me/submissions/c2454c02-f1ab-44cf-af32-cb945eea631e

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
theorem _root_.solution : IndefiniteUnitaryInverse := by
  intro N h
  apply Matrix.inv_eq_left_inv
  have hJ : Formalism.SLP.GlobalBoundRefinements.J * Formalism.SLP.GlobalBoundRefinements.J = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Formalism.SLP.GlobalBoundRefinements.J, Matrix.mul_apply, Fin.sum_univ_two]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc N.conjTranspose, h, hJ]
end Formalism.HermitianLatticeCounting.P
