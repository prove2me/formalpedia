-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.c_prime_le_weight_correction_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:24:46.924867+00:00
-- url     : https://prove2.me/submissions/b0e76545-b017-4d21-8262-53eebe379473

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Theorems.Thm_Formalism_CohomologicalDescent_jw_Il_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
open Formalism.RankGapBounds.ChebyshevFactorialBounds
namespace Formalism.CohomologicalDescent.DepthNonnegative
theorem _root_.solution : CPrimeLeCW5 := by
  intro ι D τ l hl hτ hP
  obtain ⟨hh1, _, _, hD0, _, _, _, _, _, hT⟩ := hP
  obtain ⟨hmB, hlo, hxx, hS, hxh, _⟩ := hT τ hτ
  have hl0R : (0 : ℝ) < l := by exact_mod_cast hl.pos
  have hl1R : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
    linarith
  have hk : (0 : ℝ) ≤ D.k := Nat.cast_nonneg _
  have hi : (0 : ℝ) ≤ (D.depth τ l : ℝ) := Nat.cast_nonneg _
  have hil : (0 : ℝ) ≤ (D.depth τ l : ℝ) / (l : ℝ) := div_nonneg hi hl0R.le
  have hpeel : ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * (((D.h : ℝ) - 1) / ((l : ℝ) - 1)) ≤
      ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * (((D.h : ℝ) + (D.Nr : ℝ)) / ((l : ℝ) - 1) + 6) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h1 : ((D.h : ℝ) - 1) / ((l : ℝ) - 1) ≤ ((D.h : ℝ) + (D.Nr : ℝ)) / ((l : ℝ) - 1) := by
      apply div_le_div_of_nonneg_right _ hl1R.le
      have : (0 : ℝ) ≤ (D.Nr : ℝ) := Nat.cast_nonneg _
      linarith
    linarith
  have hA : (D.k : ℝ) * (((D.xhi τ - D.xlo τ : ℤ) : ℝ) / (l : ℝ) + D.Icl τ l) ≤
      (D.k : ℝ) * ((D.S : ℝ) / (l : ℝ) + D.Icl τ l) := by
    apply mul_le_mul_of_nonneg_left _ hk
    have h1 : ((D.xhi τ - D.xlo τ : ℤ) : ℝ) ≤ (D.S : ℝ) := by exact_mod_cast hS
    have := div_le_div_of_nonneg_right h1 hl0R.le
    linarith
  have hH : harm l D.h (D.depth τ l : ℝ) ≤
      ((D.depth τ l : ℝ) / (l : ℝ)) * max 0 (1 + Real.log ((D.h : ℝ) / (l : ℝ))) := by
    unfold harm
    split_ifs
    · exact mul_nonneg hil (le_max_left _ _)
    · exact mul_le_mul_of_nonneg_left (le_max_right _ _) hil
  have hG : (if ((d0 l (D.xlo τ - D.maxB τ) : ℕ) : ℤ) < D.xlo τ - D.maxB τ then
      min (min (D.k : ℝ) (D.t : ℝ)) ((D.depth τ l : ℝ) / (d0 l (D.xlo τ - D.maxB τ) : ℝ)) else 0) =
      (if ((D.d0 τ l : ℕ) : ℤ) < Cor.DB D τ then
      min (min (D.k : ℝ) (D.t : ℝ)) ((D.depth τ l : ℝ) / (D.d0 τ l : ℝ)) else 0) := rfl
  unfold cPrime labelSumBoundPos Cor.coefficientBoundTau
  rw [jw_Il_eq, hG]
  linarith
end Formalism.CohomologicalDescent.DepthNonnegative
