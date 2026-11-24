-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.exp_div_e_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:44.083191+00:00
-- url     : https://prove2.me/submissions/1265a170-3728-4cf3-a83e-f8f6dc07a10c

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample

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
theorem _root_.solution (n : ℕ) : Real.exp ((n : ℝ) / Real.exp 1) ≤ 2 ^ n := by
  have h1 : Real.exp (1 / Real.exp 1) ≤ 2 := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have h2 : 1 / Real.exp 1 ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num) he
    have h3 : Real.exp (1 / 2) ≤ 2 := by
      have h4 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
        rw [← Real.exp_nat_mul]; norm_num
      have h5 : Real.exp 1 < 4 := by
        have := Real.exp_one_lt_d9; linarith
      nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    exact (Real.exp_le_exp.mpr h2).trans h3
  have h2 : Real.exp ((n : ℝ) / Real.exp 1) = Real.exp (1 / Real.exp 1) ^ n := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [h2]
  exact pow_le_pow_left₀ (Real.exp_pos _).le h1 n
end Formalism.HermitianLatticeCounting.P
