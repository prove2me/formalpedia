-- Prove2me | solution 1 for AvramDividend.Classical.nonnegative_time_horizon_lintegral_iSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:57:45.25407+00:00
-- url     : https://prove2.me/submissions/e683a869-bd54-404f-80d3-3a7108fce759

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped Classical ENNReal

/-- The lower integral over nonnegative times is the supremum of its finite-horizon restrictions. -/
theorem solution
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ t in Ici (0 : ℝ), f t ∂μ) =
      ⨆ n : ℕ, (∫⁻ t in Icc (0 : ℝ) (n : ℝ), f t ∂μ) := by
  let g : ℕ → ℝ → ℝ≥0∞ := fun n t =>
    if 0 ≤ t ∧ t ≤ (n : ℝ) then f t else 0
  have hgMeas : ∀ n, Measurable (g n) := by
    intro n
    have hs : MeasurableSet {t : ℝ | 0 ≤ t ∧ t ≤ (n : ℝ)} :=
      (measurableSet_Ici.inter measurableSet_Iic)
    exact Measurable.ite hs hf measurable_const
  have hgmono : Monotone g := by
    intro n m hnm t
    by_cases hn : 0 ≤ t ∧ t ≤ (n : ℝ)
    · have hm : 0 ≤ t ∧ t ≤ (m : ℝ) :=
        ⟨hn.1, le_trans hn.2 (by exact_mod_cast hnm)⟩
      simp [g, hn, hm]
    · simp [g, hn]
  have hpoint : ∀ t : ℝ, (⨆ n, g n t) =
      if 0 ≤ t then f t else 0 := by
    intro t
    by_cases ht : 0 ≤ t
    · obtain ⟨n, hn⟩ := exists_nat_ge t
      have hn' : 0 ≤ t ∧ t ≤ (n : ℝ) := ⟨ht, hn⟩
      apply le_antisymm
      · refine iSup_le fun k => ?_
        by_cases hk : 0 ≤ t ∧ t ≤ (k : ℝ)
        · simp [g, ht, hk]
        · have hnot : ¬ t ≤ (k : ℝ) := by
            intro hle
            exact hk ⟨ht, hle⟩
          simp [g, ht, hnot]
      · calc
          (if 0 ≤ t then f t else 0) = g n t := by
            simp [g, ht, hn']
          _ ≤ ⨆ k, g k t := le_iSup (fun k => g k t) n
    · have hzero : ∀ n, g n t = 0 := by
        intro n
        have hn : ¬(0 ≤ t ∧ t ≤ (n : ℝ)) := by
          intro hh
          exact ht hh.1
        simp [g, hn]
      simp [ht, hzero]
  calc
    (∫⁻ t in Ici (0 : ℝ), f t ∂μ) =
        (∫⁻ t, if 0 ≤ t then f t else 0 ∂μ) := by
          simpa [Set.indicator, Set.mem_Ici] using
            (lintegral_indicator (μ := μ) (s := Ici (0 : ℝ))
              measurableSet_Ici f).symm
    _ = ∫⁻ t, ⨆ n, g n t ∂μ := by
      simp_rw [hpoint]
    _ = ⨆ n, ∫⁻ t, g n t ∂μ := lintegral_iSup hgMeas hgmono
    _ = ⨆ n : ℕ, (∫⁻ t in Icc (0 : ℝ) (n : ℝ), f t ∂μ) := by
      apply iSup_congr
      intro n
      calc
        (∫⁻ t, g n t ∂μ) =
            ∫⁻ t, (Icc (0 : ℝ) (n : ℝ)).indicator f t ∂μ := by
              simp [g, Set.indicator, Set.mem_Icc]
        _ = _ := lintegral_indicator measurableSet_Icc f
