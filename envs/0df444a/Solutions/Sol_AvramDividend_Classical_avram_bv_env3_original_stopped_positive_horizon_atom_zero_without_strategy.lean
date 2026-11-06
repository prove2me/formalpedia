-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_original_stopped_positive_horizon_atom_zero_without_strategy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:00:00.862501+00:00
-- url     : https://prove2.me/submissions/c9bbaefd-1d9c-4936-ab5e-251123de0353

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At a stopped positive horizon original paymentTimes excludes the singleton, regardless of D. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (hT : 0 < T) (hσ : σ ≤ (T : ℝ≥0∞)) (q : ℝ) :
    (∫⁻ t in paymentTimes σ ∩ {(T : ℝ)},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) = 0 := by
  have hTr : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hEmpty : paymentTimes σ ∩ {(T : ℝ)} = ∅ := by
    ext t
    constructor
    · intro ht
      obtain ⟨hPay, htEq⟩ := ht
      subst t
      rcases hPay with ⟨_, hZero | hBefore⟩
      · exact False.elim ((ne_of_gt hTr) hZero)
      · have hCast : ENNReal.ofReal (T : ℝ) = (T : ℝ≥0∞) := by simp
        rw [hCast] at hBefore
        exact False.elim ((not_lt_of_ge hσ) hBefore)
    · intro ht
      exact False.elim (by simpa using ht)
  rw [hEmpty]
  simp
