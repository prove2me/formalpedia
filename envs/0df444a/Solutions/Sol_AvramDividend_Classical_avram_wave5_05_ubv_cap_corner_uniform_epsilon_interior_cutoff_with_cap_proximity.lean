-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_cap_corner_uniform_epsilon_interior_cutoff_with_cap_proximity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:17:47.128585+00:00
-- url     : https://prove2.me/submissions/62fc7fb4-5a59-45f5-bdc8-bb0674ab9eb9

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_cap_corner_uniform_interior_cutoff_secant_defect_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-!
For every accuracy ε, choose a slope-one cutoff b strictly inside
the genuine C2 domain AND within ε of the true cap. This adds an
explicit cap-proximity condition to the global uniform approximation.
-/

/-- Uniform cap approximation with a quantified interior proximity. -/
theorem solution
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c → 1 ≤ deriv w y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ b : ℝ, 0 < b ∧ b < c ∧ c - b < ε ∧
      ∀ y : ℝ, 0 ≤ y →
        0 ≤ (if y ≤ c then w y else w c + (y - c)) -
          (if y ≤ b then w y else w b + (y - b)) ∧
        (if y ≤ c then w y else w c + (y - c)) -
          (if y ≤ b then w y else w b + (y - b)) < ε := by
  have hOpen : Ici (0 : ℝ) ∈ 𝓝 c := Ici_mem_nhds hc
  have hW : ContinuousAt w c := hw_cont.continuousAt hOpen
  obtain ⟨δ, hδ, hNear⟩ :=
    (Metric.continuousAt_iff.mp hW) (ε / 2) (half_pos hε)
  let η : ℝ := min (min (δ / 2) (c / 2)) (ε / 2)
  have hη0 : 0 < η :=
    lt_min (lt_min (half_pos hδ) (half_pos hc)) (half_pos hε)
  have hηδ : η < δ :=
    lt_of_le_of_lt
      (le_trans (min_le_left _ _) (min_le_left _ _))
      (half_lt_self hδ)
  have hηc : η < c :=
    lt_of_le_of_lt
      (le_trans (min_le_left _ _) (min_le_right _ _))
      (half_lt_self hc)
  have hηε : η < ε :=
    lt_of_le_of_lt (min_le_right _ _) (half_lt_self hε)
  let b : ℝ := c - η
  have hbpos : 0 < b := by dsimp [b]; linarith
  have hblt : b < c := by dsimp [b]; linarith
  have hProx : c - b < ε := by dsimp [b]; linarith
  have hb0 : 0 ≤ b := le_of_lt hbpos
  have hbc : b ≤ c := le_of_lt hblt
  have hDist : dist b c = η := by
    rw [Real.dist_eq]
    have hDiff : b - c = -η := by dsimp [b]; ring
    rw [hDiff, abs_neg, abs_of_pos hη0]
  have hClose : dist (w b) (w c) < ε / 2 :=
    hNear (by simpa only [hDist] using hηδ)
  have hAbs : |w b - w c| < ε / 2 := by
    simpa only [Real.dist_eq] using hClose
  have hGap : w c - w b < ε := by
    have hLower := (abs_lt.mp hAbs).1
    linarith
  refine ⟨b, hbpos, hblt, hProx, ?_⟩
  intro y hy
  have hBound :=
    avram_wave5_05_ubv_cap_corner_uniform_interior_cutoff_secant_defect_bound
      w c hc hw_cont hw_smooth hw_grad b hb0 hbc y hy
  constructor
  · exact hBound.1
  · linarith [hBound.2]
