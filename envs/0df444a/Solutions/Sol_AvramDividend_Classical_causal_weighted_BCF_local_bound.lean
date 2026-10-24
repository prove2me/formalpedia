-- Prove2me | solution 1 for AvramDividend.Classical.causal_weighted_BCF_local_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:06:47.905862+00:00
-- url     : https://prove2.me/submissions/f6a7144f-4fa0-4ee4-acb7-8c87d20d65d5

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set
open scoped NNReal ENNReal

/-- An exponentially unweighted BCF is locally uniformly bounded. -/
theorem solution
    (f : BoundedContinuousFunction ℝ≥0 ℝ) (w R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R →
      |Real.exp (w * s) * f ⟨max s 0, le_max_right s 0⟩| ≤ C := by
  refine ⟨Real.exp (|w| * R) * ‖f‖, ?_⟩
  intro s hs
  have hs0 : 0 ≤ s := le_of_lt hs.1
  have hsR : s ≤ R := hs.2
  have hwr : w * s ≤ |w| * R := by
    calc
      w * s ≤ |w| * s :=
        mul_le_mul_of_nonneg_right (le_abs_self w) hs0
      _ ≤ |w| * R :=
        mul_le_mul_of_nonneg_left hsR (abs_nonneg w)
  have hexp : Real.exp (w * s) ≤ Real.exp (|w| * R) :=
    Real.exp_le_exp.mpr hwr
  have hf : |f ⟨max s 0, le_max_right s 0⟩| ≤ ‖f‖ := by
    simpa only [Real.norm_eq_abs] using
      f.norm_coe_le_norm ⟨max s 0, le_max_right s 0⟩
  calc
    |Real.exp (w * s) * f ⟨max s 0, le_max_right s 0⟩| =
        Real.exp (w * s) * |f ⟨max s 0, le_max_right s 0⟩| := by
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (|w| * R) * ‖f‖ :=
      mul_le_mul hexp hf (abs_nonneg _) (Real.exp_nonneg _)
