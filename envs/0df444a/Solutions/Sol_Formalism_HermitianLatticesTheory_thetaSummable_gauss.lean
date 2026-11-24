-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.thetaSummable_gauss
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:19.487023+00:00
-- url     : https://prove2.me/submissions/497d1999-f5ca-486c-a0ce-0a8e9dcbb71c

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementTheta
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaSummable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun n : ℤ => Real.exp (-δ * (n : ℝ) ^ 2)) := by
  have hr1 : Real.exp (-δ) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hg : Summable (fun n : ℕ => Real.exp (-δ) ^ n) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le hr1
  have key : ∀ n : ℕ, Real.exp (-δ * (n : ℝ) ^ 2) ≤ Real.exp (-δ) ^ n := by
    intro n
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have h1 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ n := by exact_mod_cast h
        nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hδ.le]
  apply Summable.of_nat_of_neg
  · refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) hg
    simpa using key n
  · refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) hg
    simpa [neg_sq] using key n
end Formalism.HermitianLatticesTheory
