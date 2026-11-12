-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_fixed_grid_joint_charfun_mark_power_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:08:09.866225+00:00
-- url     : https://prove2.me/submissions/b27f9aa8-6fe8-4c6c-931b-99b919b213fb

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_fixed_fourier_interval_charfun_power_20261111
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Finset
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 2 ≤ n) (Y : ℕ → Ω → ℝ)
    (hY : ∀ j, Measurable (Y j))
    (hSame : ∀ j k, IdentDistrib (Y j) (Y k) P P)
    (hFixed : ∀ (m : Fin (n + 1) → ℕ), Monotone m →
      ∀ t : WithLp 2 (Fin n → ℝ),
        MeasureTheory.charFun
          (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
            ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω)) P) t =
          ∏ i : Fin n, MeasureTheory.charFun
            (Measure.map (fun ω : Ω =>
              ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω) P)
              (t.ofLp i))
    (m : Fin (n + 1) → ℕ) (hm : Monotone m)
    (t : WithLp 2 (Fin n → ℝ)) :
    MeasureTheory.charFun
      (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
        ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω)) P) t =
    ∏ i : Fin n, (MeasureTheory.charFun (Measure.map (Y 0) P) (t.ofLp i)) ^
      (m i.succ - m i.castSucc) := by
  rw [hFixed m hm t]
  apply Finset.prod_congr rfl
  intro i hi
  have hmi : m i.castSucc ≤ m i.succ :=
    hm (Fin.castSucc_le_succ i)
  have hLen : m i.castSucc + (m i.succ - m i.castSucc) = m i.succ :=
    Nat.add_sub_of_le hmi
  have hPower :=
    AvramDividend.Classical.avram_a06_fixed_fourier_interval_charfun_power_20261111
      P n hn Y hY hSame hFixed (m i.castSucc)
        (m i.succ - m i.castSucc) (t.ofLp i)
  simpa only [hLen] using hPower
