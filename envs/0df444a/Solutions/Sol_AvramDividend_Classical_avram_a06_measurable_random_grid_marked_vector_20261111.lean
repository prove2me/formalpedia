-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_measurable_random_grid_marked_vector_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:13:07.441904+00:00
-- url     : https://prove2.me/submissions/b111e3c0-e830-4829-9eba-781b370bcbb8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_measurable_random_mark_interval_20261111
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Finset
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (N : Fin (n + 1) → Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hN : Measurable (fun ω => fun i => N i ω))
    (hY : Measurable (fun ω => fun j => Y j ω)) :
    Measurable (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
      ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω)) := by
  have hCoord (i : Fin n) : Measurable
      (fun ω : Ω => ∑ j ∈ Finset.Ico (N i.castSucc ω)
        (N i.succ ω), Y j ω) :=
    AvramDividend.Classical.avram_a06_measurable_random_mark_interval_20261111
      (N i.castSucc) (N i.succ) Y
      ((measurable_pi_apply i.castSucc).comp hN)
      ((measurable_pi_apply i.succ).comp hN)
      (fun j => (measurable_pi_apply j).comp hY)
  have hPi : Measurable (fun ω : Ω => fun i : Fin n =>
      ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω) :=
    measurable_pi_iff.mpr hCoord
  exact (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp hPi
