-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_conditional_fourier_representation_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:18:53.040793+00:00
-- url     : https://prove2.me/submissions/6538fc62-6ca1-49fe-b586-48aa83afb7e3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_zero_grid_conditional_fourier_20261111
import Theorems.Thm_AvramDividend_Classical_avram_a06_one_grid_conditional_fourier_case_split_20261111
import Theorems.Thm_AvramDividend_Classical_avram_a06_conditional_fourier_two_or_more_20261111
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory Finset
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (N : Fin (n + 1) → Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hN : Measurable (fun ω => fun i => N i ω))
    (hY : Measurable (fun ω => fun j => Y j ω))
    (hNmono : ∀ ω, Monotone (fun i => N i ω))
    (hSameLaw : ∀ j k, IdentDistrib (Y j) (Y k) P P)
    (hSeparate : IndepFun (fun ω => fun i => N i ω)
      (fun ω => fun j => Y j ω) P)
    (hFixed : ∀ (m : Fin (n + 1) → ℕ), Monotone m →
      ∀ t : WithLp 2 (Fin n → ℝ),
        MeasureTheory.charFun
          (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
            ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω)) P) t =
          ∏ i : Fin n, MeasureTheory.charFun
            (Measure.map (fun ω : Ω =>
              ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω) P)
              (t.ofLp i)) :
    ∀ t : WithLp 2 (Fin n → ℝ), ∃ φ : Fin n → ℕ → ℂ,
      MeasureTheory.charFun
        (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
          ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω)) P) t =
          ∫ ω, ∏ i : Fin n, φ i (N i.succ ω - N i.castSucc ω) ∂P
      ∧ ∀ i : Fin n, MeasureTheory.charFun
          (Measure.map (fun ω : Ω =>
            ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω) P)
          (t.ofLp i) =
          ∫ ω, φ i (N i.succ ω - N i.castSucc ω) ∂P := by
  intro t
  by_cases hn0 : n = 0
  · subst n
    exact AvramDividend.Classical.avram_a06_zero_grid_conditional_fourier_20261111
      P N Y t
  by_cases hn1 : n = 1
  · subst n
    exact AvramDividend.Classical.avram_a06_one_grid_conditional_fourier_case_split_20261111
      P N Y hN hY t
  have hn : 2 ≤ n := by omega
  exact AvramDividend.Classical.avram_a06_conditional_fourier_two_or_more_20261111
    P n hn N Y hN hY hNmono hSameLaw hSeparate hFixed t
