-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_finite_strict_cash_prefix_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T09:17:38.977117+00:00
-- url     : https://prove2.me/submissions/c5e07422-f426-44c2-9f00-4022618c69e8

import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- A monotone strict cash prefix converges under a finite nonnegative physical cash integral. -/
theorem solution
    (m : Measure ℝ) (f : ℝ → ℝ≥0∞) (hf : AEMeasurable f m)
    (u : ℕ → ℝ) (t : ℝ) (hm : Monotone u)
    (hu : ∀ n, u n < t) (hl : Tendsto u atTop (nhds t))
    (hfinite : (∫⁻ y in Ico 0 t, f y ∂m) ≠ ⊤) :
    Tendsto (fun n => (∫⁻ y in Ico 0 (u n), f y ∂m).toReal) atTop
      (nhds (∫⁻ y in Ico 0 t, f y ∂m).toReal) := by
  have hmeas (n : ℕ) :
      AEMeasurable ((Ico (0 : ℝ) (u n)).indicator f) m :=
    hf.indicator measurableSet_Ico
  have hbound (n : ℕ) :
      (Ico (0 : ℝ) (u n)).indicator f ≤ᵐ[m] (Ico 0 t).indicator f := by
    apply Filter.Eventually.of_forall
    intro y
    by_cases hy : y ∈ Ico (0 : ℝ) (u n)
    · have hyt : y ∈ Ico (0 : ℝ) t := ⟨hy.1, hy.2.trans (hu n)⟩
      simp [Set.indicator, hy, hyt]
    · simp [Set.indicator, hy]
  have hpoint (y : ℝ) :
      Tendsto (fun n => (Ico (0 : ℝ) (u n)).indicator f y)
        atTop (𝓝 ((Ico 0 t).indicator f y)) := by
    have heventually :
        ∀ᶠ n in atTop,
          (Ico (0 : ℝ) (u n)).indicator f y =
            (Ico 0 t).indicator f y := by
      by_cases hy : y ∈ Ico (0 : ℝ) t
      · filter_upwards [hl.eventually (Ioi_mem_nhds hy.2)] with n hn
        have hmem : y ∈ Ico (0 : ℝ) (u n) := ⟨hy.1, hn⟩
        simp [Set.indicator, hmem, hy]
      · apply Filter.Eventually.of_forall
        intro n
        have hnot : y ∉ Ico (0 : ℝ) (u n) := by
          intro h
          exact hy ⟨h.1, h.2.trans (hu n)⟩
        simp [Set.indicator, hnot, hy]
    exact (tendsto_congr' heventually).2 tendsto_const_nhds
  have hfin :
      (∫⁻ y, (Ico (0 : ℝ) t).indicator f y ∂m) ≠ ⊤ := by
    simpa only [lintegral_indicator measurableSet_Ico] using hfinite
  have hlim := tendsto_lintegral_of_dominated_convergence'
    ((Ico (0 : ℝ) t).indicator f) hmeas hbound hfin
    (Filter.Eventually.of_forall hpoint)
  have hreal := (ENNReal.tendsto_toReal hfin).comp hlim
  simpa only [Function.comp_def, lintegral_indicator measurableSet_Ico] using hreal
