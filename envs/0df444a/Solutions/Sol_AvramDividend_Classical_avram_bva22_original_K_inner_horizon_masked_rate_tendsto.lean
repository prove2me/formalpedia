-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva22_original_K_inner_horizon_masked_rate_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T23:53:07.648303+00:00
-- url     : https://prove2.me/submissions/73a635e1-4804-4beb-9871-caccd240e98f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva20_strict_inner_horizon_ruin_mask_eventual_equiv
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original K interior horizon mask converges away from the ruin boundary. -/
theorem solution
    (T : ℝ) (hT : 0 < T) (τ : ℝ≥0∞)
    (t : ℝ) (ht0 : 0 < t) (htT : t < T)
    (hτ : ENNReal.ofReal t ≠ τ) (b : ℝ)
    (C : ℝ≥0∞) (v : ℝ) :
    Tendsto (fun n : ℕ =>
      if 0 < t ∧ t < T - T / ((n : ℝ) + 2) ∧
        ENNReal.ofReal t ≤ τ ∧
        0 ≤ b ∧ ENNReal.ofReal b ≤ C then v else 0)
      atTop (𝓝 (if 0 < t ∧ ENNReal.ofReal t < τ ∧
        0 ≤ b ∧ ENNReal.ofReal b ≤ C then v else 0)) := by
  have hEventually :=
    avram_bva20_strict_inner_horizon_ruin_mask_eventual_equiv
      T hT τ t ht0 htT hτ
  have hEq : ∀ᶠ n : ℕ in atTop,
      (if 0 < t ∧ t < T - T / ((n : ℝ) + 2) ∧
         ENNReal.ofReal t ≤ τ ∧
         0 ≤ b ∧ ENNReal.ofReal b ≤ C then v else 0) =
      (if 0 < t ∧ ENNReal.ofReal t < τ ∧
         0 ≤ b ∧ ENNReal.ofReal b ≤ C then v else 0) := by
    filter_upwards [hEventually] with n hn
    have hiff :
        (0 < t ∧ t < T - T / ((n : ℝ) + 2) ∧
          ENNReal.ofReal t ≤ τ ∧ 0 ≤ b ∧ ENNReal.ofReal b ≤ C) ↔
        (0 < t ∧ ENNReal.ofReal t < τ ∧
          0 ≤ b ∧ ENNReal.ofReal b ≤ C) := by
      constructor
      · rintro ⟨ha, hb, hc, hd, he⟩
        have hf := hn.mp ⟨ha, hb, hc⟩
        exact ⟨hf.1, hf.2, hd, he⟩
      · rintro ⟨ha, hb, hc, hd⟩
        have hf := hn.mpr ⟨ha, hb⟩
        exact ⟨hf.1, hf.2.1, hf.2.2, hc, hd⟩
    by_cases hp : 0 < t ∧ t < T - T / ((n : ℝ) + 2) ∧
      ENNReal.ofReal t ≤ τ ∧ 0 ≤ b ∧ ENNReal.ofReal b ≤ C
    · have hq := hiff.mp hp
      simp [hp, hq]
    · have hq : ¬ (0 < t ∧ ENNReal.ofReal t < τ ∧
          0 ≤ b ∧ ENNReal.ofReal b ≤ C) := fun h => hp (hiff.mpr h)
      simp [hp, hq]
  exact (tendsto_congr' hEq).2 tendsto_const_nhds
