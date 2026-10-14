-- Prove2me | solution 1 for DbarRegularity.maximalFunction_lowerSemicontinuous
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T22:30:40.573447+00:00
-- url     : https://prove2.me/submissions/01834898-2b5c-44b1-97f0-d69fb4cca07d

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Topology.Semicontinuity.Basic



namespace DbarRegularity

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

/-- The Hardy–Littlewood maximal function is lower semicontinuous. -/
theorem maximalFunction_lowerSemicontinuous (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ) :
    LowerSemicontinuous (maximalFunction f) := by
  intro x α hx
  obtain ⟨r, hr⟩ := lt_iSup_iff.1 hx
  obtain ⟨hr0, hr⟩ := lt_iSup_iff.1 hr
  set c := volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)
  have hct : c ≠ ⊤ := measure_ball_lt_top.ne
  have hV : ∀ (y : EuclideanSpace ℝ (Fin d)) (s : ℝ), 0 < s →
      volume (ball y s) = ENNReal.ofReal (s ^ d) * c := fun y s hs => by
    rw [Measure.addHaar_ball_of_pos _ _ hs, finrank_euclideanSpace_fin]
  set I := ∫⁻ y in ball x r, ‖f y‖ₑ
  have hαt : α ≠ ⊤ := ne_top_of_lt hx
  have h1 : α * volume (ball x r) < I := by
    have h0 : volume (ball x r) ≠ 0 := (measure_ball_pos _ _ hr0).ne'
    have ht : volume (ball x r) ≠ ⊤ := measure_ball_lt_top.ne
    rw [← ENNReal.div_eq_inv_mul] at hr
    exact (ENNReal.lt_div_iff_mul_lt (Or.inl h0) (Or.inl ht)).1 hr
  have hid : ∀ s : ℝ, 0 ≤ s →
      α * (ENNReal.ofReal (s ^ d) * c) = ENNReal.ofReal ((α * c).toReal * s ^ d) := by
    intro s hs
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (ENNReal.mul_ne_top hαt hct)]
    ring
  have h2 : ∃ s, r < s ∧ α * (ENNReal.ofReal (s ^ d) * c) < I := by
    by_cases hI : I = ⊤
    · refine ⟨r + 1, by linarith, ?_⟩
      rw [hI]
      exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hαt)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hct))
    · have hcont : ContinuousAt (fun s : ℝ => (α * c).toReal * s ^ d) r := by fun_prop
      have hlt : (α * c).toReal * r ^ d < I.toReal := by
        rw [hV x r hr0, hid r hr0.le, ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hI] at h1
        exact h1
      obtain ⟨s, hs, hs'⟩ := (hcont.eventually_lt continuousAt_const hlt).exists_gt
      refine ⟨s, hs, ?_⟩
      have hs0 : 0 ≤ s := hr0.le.trans hs.le
      rw [hid s hs0, ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hI]
      exact hs'
  obtain ⟨s, hrs, hs⟩ := h2
  have hs0 : 0 < s := hr0.trans hrs
  filter_upwards [ball_mem_nhds x (sub_pos.2 hrs)] with y hy
  have hsub : ball x r ⊆ ball y s := by
    intro z hz
    rw [mem_ball] at hz hy ⊢
    calc dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
      _ < r + (s - r) := add_lt_add hz (by rwa [dist_comm])
      _ = s := by ring
  have h0 : volume (ball y s) ≠ 0 := (measure_ball_pos _ _ hs0).ne'
  have ht : volume (ball y s) ≠ ⊤ := measure_ball_lt_top.ne
  have key : α < (volume (ball y s))⁻¹ * ∫⁻ z in ball y s, ‖f z‖ₑ := by
    rw [← ENNReal.div_eq_inv_mul, ENNReal.lt_div_iff_mul_lt (Or.inl h0) (Or.inl ht), hV y s hs0]
    exact hs.trans_le (lintegral_mono_set hsub)
  exact key.trans_le (le_iSup₂_of_le (f := fun (r : ℝ) (_ : 0 < r) =>
    (volume (ball y r))⁻¹ * ∫⁻ z in ball y r, ‖f z‖ₑ) s hs0 le_rfl)

end DbarRegularity

open DbarRegularity

open MeasureTheory

theorem solution (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ) :
    LowerSemicontinuous (maximalFunction f) :=
  maximalFunction_lowerSemicontinuous d f
