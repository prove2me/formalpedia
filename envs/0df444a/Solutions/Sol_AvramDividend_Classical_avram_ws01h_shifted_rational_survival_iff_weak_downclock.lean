-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_shifted_rational_survival_iff_weak_downclock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T15:26:46.541192+00:00
-- url     : https://prove2.me/submissions/fc487a30-1316-4ba9-9dcf-62c501664fbd

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_lower_before_horizon_grid_iff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The stopped shifted Lévy path's countable rational tests detect its
source-defined strict first lower passage with the weak horizon inequality. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (ω : Ω) (b T : ℝ≥0) :
    (∀ n : ℕ, 0 < n → ∀ k : ℕ,
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T →
        0 ≤ x + (X.X (b + (k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω - X.X b ω)) ↔
    (T : ℝ≥0∞) ≤
      (⨅ (s : ℝ≥0)
        (_ : x + (X.X (b + s) ω - X.X b ω) < 0), (s : ℝ≥0∞)) := by
  classical
  have hGrid :
      (∀ n : ℕ, 0 < n → ∀ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T →
          0 ≤ x + (X.X (b + (k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω - X.X b ω)) ↔
      (∀ s : ℝ≥0, s < T →
        0 ≤ x + (X.X (b + s) ω - X.X b ω)) := by
    constructor
    · intro hg s hst
      by_contra hn
      have hbad : x + (X.X (b + s) ω - X.X b ω) < 0 :=
        lt_of_not_ge hn
      obtain ⟨n, hn, k, hk, hcross⟩ :=
        (chat04_random_reserve_shifted_lower_before_horizon_grid_iff
          X (fun _ : Ω => x) ω b T).mp ⟨s, hst, hbad⟩
      exact (not_lt_of_ge (hg n hn k hk)) hcross
    · intro hs n hn k hk
      exact hs _ hk
  rw [hGrid]
  constructor
  · intro hSurvive
    refine le_iInf fun s => le_iInf fun hs => ?_
    have hTs : T ≤ s := by
      by_contra hn
      have hst : s < T := lt_of_not_ge hn
      have hp := hSurvive s hst
      linarith
    exact ENNReal.coe_le_coe.mpr hTs
  · intro hLower s hst
    by_contra hn
    have hCross : x + (X.X (b + s) ω - X.X b ω) < 0 :=
      lt_of_not_ge hn
    have hDownLe :
        (⨅ (u : ℝ≥0)
          (_ : x + (X.X (b + u) ω - X.X b ω) < 0),
          (u : ℝ≥0∞)) ≤ (s : ℝ≥0∞) := by
      exact iInf_le_of_le s (iInf_le_of_le hCross le_rfl)
    have hTs : T ≤ s :=
      ENNReal.coe_le_coe.mp (hLower.trans hDownLe)
    exact (not_lt_of_ge hTs) hst
