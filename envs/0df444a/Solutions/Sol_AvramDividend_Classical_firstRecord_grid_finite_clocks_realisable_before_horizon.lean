-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_grid_finite_clocks_realisable_before_horizon
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:34:44.726053+00:00
-- url     : https://prove2.me/submissions/37730eb3-1a49-49d5-b4fc-2b0ce8136b1f

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.Nat.Basic
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_threshold_iInf_mono

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (b h : ℝ) (hh : 0 ≤ h) (T : ℝ≥0) (N : ℕ)
    (hN : (⨅ (r : ℝ≥0)
      (_ : b + (N : ℝ) * h < X.X r ω), (r : ℝ≥0∞)) <
      (T : ℝ≥0∞)) :
    ∃ u : ℕ → ℝ≥0,
      (∀ k : ℕ, k ≤ N →
        (u k : ℝ≥0∞) =
          (⨅ (r : ℝ≥0)
            (_ : b + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞))) ∧
      (∀ k : ℕ, k < N → (u k : ℝ) ≤ (u (k + 1) : ℝ)) ∧
      (u N : ℝ≥0∞) < (T : ℝ≥0∞) := by
  set c : ℕ → ℝ≥0∞ := fun k => ⨅ (r : ℝ≥0) (_ : b + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞) with hc
  have hmono : ∀ j k : ℕ, j ≤ k → c j ≤ c k := by
    intro j k hjk
    apply AvramDividend.Classical.firstUpcrossing_threshold_iInf_mono
    have : (j : ℝ) ≤ k := by exact_mod_cast hjk
    nlinarith
  have hfin : ∀ k, k ≤ N → c k ≠ ⊤ := fun k hk =>
    ne_top_of_lt (lt_of_le_of_lt (hmono k N hk) hN)
  refine ⟨fun k => (c k).toNNReal, fun k hk => ENNReal.coe_toNNReal (hfin k hk), fun k hk => ?_, ?_⟩
  · simp only [NNReal.coe_le_coe]
    exact ENNReal.toNNReal_mono (hfin (k + 1) hk) (hmono k (k + 1) (Nat.le_succ k))
  · rw [ENNReal.coe_toNNReal (hfin N le_rfl)]; exact hN
