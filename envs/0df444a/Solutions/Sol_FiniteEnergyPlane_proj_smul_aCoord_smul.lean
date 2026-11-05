-- Prove2me | solution 1 for FiniteEnergyPlane.proj_smul_aCoord_smul
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T19:51:20.856743+00:00
-- url     : https://prove2.me/submissions/957dd49a-4ad6-4464-b58e-a064c4f3b712

import Definitions.Def_FiniteEnergyPlane_Setting



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- On a strictly star-shaped level, scaling `y ≠ 0` by `c > 0` leaves the radial projection
unchanged and shifts the symplectization coordinate by `log c / 2`. -/
theorem proj_smul_aCoord_smul {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (y : V n) (hy : y ≠ 0) (c : ℝ) (hc : 0 < c) :
    proj H (c • y) = proj H y ∧ aCoord H (c • y) = aCoord H y + Real.log c / 2 := by
  have spec : ∀ y : V n, y ≠ 0 → 0 < scaleToS H y ∧ H (scaleToS H y • y) = 1 := by
    intro y hy
    have hex : ∃ r : ℝ, 0 < r ∧ H (r • y) = 1 := (hH.2.1 y hy).exists
    unfold scaleToS
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  obtain ⟨hs, h1⟩ := spec y hy
  have hcy : c • y ≠ 0 := smul_ne_zero hc.ne' hy
  have heq : scaleToS H (c • y) = scaleToS H y / c := by
    refine (hH.2.1 _ hcy).unique (spec _ hcy) ⟨div_pos hs hc, ?_⟩
    rw [smul_smul, div_mul_cancel₀ _ hc.ne']
    exact h1
  refine ⟨?_, ?_⟩
  · simp only [proj, heq, smul_smul, div_mul_cancel₀ _ hc.ne']
  · simp only [aCoord, heq, Real.log_div hs.ne' hc.ne']
    ring

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (y : V n) (hy : y ≠ 0) (c : ℝ) (hc : 0 < c) :
    proj H (c • y) = proj H y ∧ aCoord H (c • y) = aCoord H y + Real.log c / 2 :=
  proj_smul_aCoord_smul H hH y hy c hc
