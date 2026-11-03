-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:09:01.461727+00:00
-- url     : https://prove2.me/submissions/7cc6fdf9-f95b-438a-b365-51c8055fc919

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal
noncomputable section

/-- Canonical positive-cap C1 gradient controls all two-point payment jumps up to and including cap equality. -/
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (b : ℝ) (hb : 0 ≤ b) (hbC : ENNReal.ofReal b ≤ C) :
    ∀ y ∈ Icc (0 : ℝ) b, ∀ z ∈ Icc (0 : ℝ) b,
      y ≤ z → z - y ≤ w z - w y := by
  have hSub : Ioo (0 : ℝ) b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro z hz
    have hzReal : ENNReal.ofReal z < ENNReal.ofReal b := by
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hz.1.le).2 hz.2
    exact ⟨hz.1, hzReal.trans_le hbC⟩
  have hDiff : DifferentiableOn ℝ w (interior (Icc (0 : ℝ) b)) := by
    have hC1 : ContDiffOn ℝ 1 w (Ioo (0 : ℝ) b) :=
      hw_smooth.mono hSub
    have hD := hC1.differentiableOn (by norm_num)
    exact hD.mono (by
      intro z hz
      simpa only [interior_Icc] using hz)
  have hCont : ContinuousOn (fun z : ℝ => w z - z) (Icc (0 : ℝ) b) := by
    exact (hw_cont.mono (by
      intro z hz
      exact hz.1)).sub continuousOn_id
  have hDiffG : DifferentiableOn ℝ (fun z : ℝ => w z - z)
      (interior (Icc (0 : ℝ) b)) := by
    exact hDiff.sub differentiableOn_id
  have hDeriv : ∀ z ∈ interior (Icc (0 : ℝ) b),
      0 ≤ deriv (fun t : ℝ => w t - t) z := by
    intro z hz
    have hzIoo : z ∈ Ioo (0 : ℝ) b := by
      simpa only [interior_Icc] using hz
    have hwAt : DifferentiableAt ℝ w z :=
      hDiff.differentiableAt (isOpen_interior.mem_nhds hz)
    have hD : deriv (fun t : ℝ => w t - t) z = deriv w z - 1 := by
      calc
        deriv (fun t : ℝ => w t - t) z =
            deriv w z - deriv (fun t : ℝ => t) z := by
          exact deriv_sub hwAt differentiableAt_id
        _ = deriv w z - 1 := by
          simp
    rw [hD]
    linarith only [hw_grad z hzIoo.1 (hSub hzIoo).2]
  have hMono : MonotoneOn (fun z : ℝ => w z - z)
      (Icc (0 : ℝ) b) :=
    monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) b) hCont hDiffG hDeriv
  intro y hy z hz hyz
  have hAt := hMono hy hz hyz
  dsimp at hAt
  linarith only [hAt]