-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_fixed_fourier_factor_implies_block_independence_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:27:17.750985+00:00
-- url     : https://prove2.me/submissions/799e3b44-d5e4-4db6-b939-b8859fcfdf6e

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Finset
noncomputable section

/-- The exact fixed-grid Fourier identity is finite-family independence. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (n : ℕ) (Y : ℕ → Ω → ℝ) (hY : ∀ j, Measurable (Y j))
    (hFixed : ∀ (m : Fin (n + 1) → ℕ), Monotone m →
      ∀ t : WithLp 2 (Fin n → ℝ),
        MeasureTheory.charFun
          (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
            ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω)) P) t =
          ∏ i : Fin n, MeasureTheory.charFun
            (Measure.map (fun ω : Ω =>
              ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω) P)
            (t.ofLp i))
    (m : Fin (n + 1) → ℕ) (hm : Monotone m) :
    iIndepFun (fun i : Fin n => fun ω : Ω =>
      ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω) P := by
  apply (ProbabilityTheory.iIndepFun_iff_charFun_pi (fun i =>
    (Finset.measurable_sum _ (fun j hj => hY j)).aemeasurable)).2
  exact hFixed m hm
