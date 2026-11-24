-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.blockMinorSumPowSixtyFour_of_blockMinorSumExplicit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:40.594035+00:00
-- url     : https://prove2.me/submissions/cc322bfd-24d7-4039-9647-0987c662bc91

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_exp_div_e_le_two_pow

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
theorem _root_.solution (h : BlockMinorSumExplicit) : BlockMinorSumPowSixtyFour := by
  intro E _ _ _ r S hS
  refine (h E r S hS).trans ?_
  set f := Fintype.card (InfinitePlace E) with hf
  have hf1 : 1 ≤ f := Fintype.card_pos
  have h1 : Real.exp (((r : ℝ) + 1) / Real.exp 1) ≤ 2 ^ (r + 1) := by
    have := exp_div_e_le_two_pow (r + 1); push_cast at this; exact this
  have h2 : (2 : ℝ) ^ r ≤ 2 ^ (r + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : (2 : ℝ) ^ (r + 1) * 2 ^ (r + 1) = 4 ^ (r + 1) := by
    rw [← mul_pow]; norm_num
  have h4 : (4 : ℝ) ^ (r + 1) ≤ 4 ^ (f * (r + 1)) :=
    pow_le_pow_right₀ (by norm_num) (by nlinarith)
  have h5 : (64 : ℝ) ^ (f * (r + 1)) = 4 ^ (f * (r + 1)) * 16 ^ (f * (r + 1)) := by
    rw [← mul_pow]; norm_num
  rw [h5]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc (2 : ℝ) ^ r * Real.exp (((r : ℝ) + 1) / Real.exp 1) ≤ 2 ^ (r + 1) * 2 ^ (r + 1) :=
        mul_le_mul h2 h1 (Real.exp_pos _).le (by positivity)
    _ = 4 ^ (r + 1) := h3
    _ ≤ _ := h4
end Formalism.HermitianLatticeCounting.P
