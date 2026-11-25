-- Prove2me | solution 1 for FiniteEnergyPlane.proj_smul_eq_of_mem_energySurface
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-25T12:00:59.349608+00:00
-- url     : https://prove2.me/submissions/1c0fabd8-0f75-4873-a67a-1e33e8e8ff7d

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem proj_smul_eq_of_mem_energySurface_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (x : V n) (hx : x ∈ energySurface H) (r : ℝ) (hr : 0 < r) :
    proj H (r • x) = x := by
  have h0 : x ≠ 0 := by
    rintro rfl
    have := hH.2.2 0 hx
    simp at this
  have hne : r • x ≠ 0 := smul_ne_zero hr.ne' h0
  have hex : ∃ s : ℝ, 0 < s ∧ H (s • r • x) = 1 := (hH.2.1 _ hne).exists
  unfold proj scaleToS
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := Classical.choose_spec hex
  rw [smul_smul] at h2 ⊢
  have hx' : H ((1 : ℝ) • x) = 1 := by rw [one_smul]; exact hx
  rw [(hH.2.1 x h0).unique ⟨mul_pos h1 hr, h2⟩ ⟨one_pos, hx'⟩, one_smul]

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (x : V n) (hx : x ∈ energySurface H) (r : ℝ) (hr : 0 < r) :
    proj H (r • x) = x :=
  proj_smul_eq_of_mem_energySurface_aux H hH x hx r hr
