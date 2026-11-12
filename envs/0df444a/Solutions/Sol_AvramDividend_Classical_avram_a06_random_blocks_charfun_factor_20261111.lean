-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_random_blocks_charfun_factor_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:52:00.481097+00:00
-- url     : https://prove2.me/submissions/fca7de11-a0c9-49a0-a71c-b29be7085026

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.IdentDistrib
import Theorems.Thm_AvramDividend_Classical_avram_a06_fixed_blocks_charfun_factor_20261111
import Theorems.Thm_AvramDividend_Classical_avram_a06_random_count_fourier_mixing_given_fixed_20261111
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory Finset
open scoped NNReal ENNReal
noncomputable section

/-- Reduce random-grid Fourier factorisation to fixed-grid factorisation and mixing. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (N : Fin (n + 1) → Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hN : Measurable (fun ω => fun i => N i ω))
    (hY : Measurable (fun ω => fun j => Y j ω))
    (hNmono : ∀ ω, Monotone (fun i => N i ω))
    (hCount : iIndepFun (fun (i : Fin n) ω =>
      N i.succ ω - N i.castSucc ω) P)
    (hMarks : iIndepFun Y P)
    (hSameLaw : ∀ j k, IdentDistrib (Y j) (Y k) P P)
    (hSeparate : IndepFun (fun ω => fun i => N i ω)
      (fun ω => fun j => Y j ω) P) :
    ∀ t : WithLp 2 (Fin n → ℝ),
      MeasureTheory.charFun
        (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
          ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω)) P) t =
        ∏ i : Fin n, MeasureTheory.charFun
          (Measure.map (fun ω : Ω =>
            ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω) P)
          (t.ofLp i) := by
  have hYcoord : ∀ k, Measurable (Y k) := by
    intro k
    exact measurable_pi_iff.mp hY k
  have hFixed : ∀ (m : Fin (n + 1) → ℕ), Monotone m →
      ∀ t : WithLp 2 (Fin n → ℝ),
        MeasureTheory.charFun
          (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
            ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω)) P) t =
          ∏ i : Fin n, MeasureTheory.charFun
            (Measure.map (fun ω : Ω =>
              ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω) P)
            (t.ofLp i) := by
    intro m hm
    exact AvramDividend.Classical.avram_a06_fixed_blocks_charfun_factor_20261111
      P n m hm Y hYcoord hMarks
  exact AvramDividend.Classical.avram_a06_random_count_fourier_mixing_given_fixed_20261111
    P n N Y hN hY hNmono hCount hSameLaw hSeparate hFixed
