-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_random_grid_fixed_fibre_charfun_power_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:35:45.403208+00:00
-- url     : https://prove2.me/submissions/eddf5b2f-7f08-4044-b4eb-3309b06c93eb

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_fixed_grid_joint_charfun_mark_power_20261111
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Finset
noncomputable section

/-- Specialise fixed-grid Fourier power to the realised monotone count grid. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 2 ≤ n)
    (N : Fin (n + 1) → Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hY : Measurable (fun ω => fun j => Y j ω))
    (hNmono : ∀ ω, Monotone (fun i => N i ω))
    (hSameLaw : ∀ j k, IdentDistrib (Y j) (Y k) P P)
    (hFixed : ∀ (m : Fin (n + 1) → ℕ), Monotone m →
      ∀ t : WithLp 2 (Fin n → ℝ),
        MeasureTheory.charFun
          (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
            ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω)) P) t =
          ∏ i : Fin n, MeasureTheory.charFun
            (Measure.map (fun ω : Ω =>
              ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω) P)
              (t.ofLp i))
    (ω : Ω) (t : WithLp 2 (Fin n → ℝ)) :
    MeasureTheory.charFun
      (Measure.map (fun ω' : Ω => WithLp.toLp 2 (fun i : Fin n =>
        ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω')) P) t =
    ∏ i : Fin n, (MeasureTheory.charFun (Measure.map (Y 0) P) (t.ofLp i)) ^
      (N i.succ ω - N i.castSucc ω) := by
  exact AvramDividend.Classical.avram_a06_fixed_grid_joint_charfun_mark_power_20261111
    P n hn Y (fun j => (measurable_pi_iff.mp hY) j)
    hSameLaw hFixed (fun i => N i ω) (hNmono ω) t
