-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_conditional_fourier_two_or_more_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:21:08.095279+00:00
-- url     : https://prove2.me/submissions/cab93102-852f-425f-af7a-25a86e903c2e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_random_grid_joint_charfun_mix_20261111
import Theorems.Thm_AvramDividend_Classical_avram_a06_random_grid_marginal_charfun_mix_20261111
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory Finset
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 2 ≤ n)
    (N : Fin (n + 1) → Ω → ℕ) (Y : ℕ → Ω → ℝ)
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
          ∫ ω, φ i (N i.succ ω - N i.castSucc ω) ∂P  := by
  intro t
  refine ⟨fun i k => MeasureTheory.charFun
    (Measure.map (Y 0) P) (t.ofLp i) ^ k, ?_, ?_⟩
  · exact AvramDividend.Classical.avram_a06_random_grid_joint_charfun_mix_20261111
      P n hn N Y hN hY hNmono hSameLaw hSeparate hFixed t
  · intro i
    exact AvramDividend.Classical.avram_a06_random_grid_marginal_charfun_mix_20261111
      P n hn N Y hN hY hNmono hSameLaw hSeparate hFixed t i
