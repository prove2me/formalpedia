-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.list_prod_le_exp_sum_div_e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:12.11549+00:00
-- url     : https://prove2.me/submissions/c79881fc-125f-42f1-b343-dd5915ec534f

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_le_exp_div_e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (l : List ℕ) : ((l.prod : ℕ) : ℝ) ≤ Real.exp (((l.sum : ℕ) : ℝ) / Real.exp 1) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.prod_cons, List.sum_cons]
    rw [Nat.cast_mul, Nat.cast_add, add_div, Real.exp_add]
    exact mul_le_mul (le_exp_div_e a) ih (Nat.cast_nonneg _) (Real.exp_pos _).le
end Formalism.HermitianLatticeCounting.P
