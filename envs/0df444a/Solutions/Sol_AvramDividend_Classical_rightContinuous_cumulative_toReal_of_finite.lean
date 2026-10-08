-- Prove2me | solution 1 for AvramDividend.Classical.rightContinuous_cumulative_toReal_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T23:11:25.278983+00:00
-- url     : https://prove2.me/submissions/4a193cfa-bfce-49e5-b97f-721b34e06d0f

import Mathlib

open MeasureTheory Filter Set Topology
open scoped ENNReal

theorem solution
    (β : Measure ℝ)
    (hfin : ∀ x : ℝ, β (Iic x) ≠ ∞) :
    ∀ x : ℝ,
      ContinuousWithinAt (fun y : ℝ => (β (Iic y)).toReal) (Ici x) x := by
  intro x
  have hinter : (⋂ r > x, Iic r) = Iic x := by
    ext y
    simp only [mem_iInter, mem_Iic]
    constructor
    · intro h
      by_contra hnot
      have hxy : x < y := lt_of_not_ge hnot
      let r : ℝ := (x + y) / 2
      have hxr : x < r := by
        dsimp [r]
        linarith
      have hry : r < y := by
        dsimp [r]
        linarith
      have hyr : y ≤ r := h r hxr
      exact (not_lt_of_ge hyr) hry
    · intro hy r hxr
      exact hy.trans hxr.le
  have hβ :
      Tendsto (fun y : ℝ => β (Iic y))
        (𝓝[Ioi x] x) (𝓝 (β (Iic x))) := by
    have h :=
      tendsto_measure_biInter_gt
        (μ := β) (s := fun y : ℝ => Iic y) (a := x)
        (fun _ _ => measurableSet_Iic.nullMeasurableSet)
        (fun _ _ _ hij => Iic_subset_Iic.mpr hij)
        ⟨x + 1, by linarith, hfin (x + 1)⟩
    change
      Tendsto (fun y : ℝ => β (Iic y))
        (𝓝[Ioi x] x) (𝓝 (β (⋂ r > x, Iic r))) at h
    rw [hinter] at h
    exact h
  have hreal :
      Tendsto (fun y : ℝ => (β (Iic y)).toReal)
        (𝓝[Ioi x] x) (𝓝 ((β (Iic x)).toReal)) :=
    (ENNReal.tendsto_toReal (hfin x)).comp hβ
  exact continuousWithinAt_Ioi_iff_Ici.mp hreal
