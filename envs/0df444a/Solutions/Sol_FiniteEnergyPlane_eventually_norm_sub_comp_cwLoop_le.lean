-- Prove2me | solution 1 for FiniteEnergyPlane.eventually_norm_sub_comp_cwLoop_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:18:00.156217+00:00
-- url     : https://prove2.me/submissions/21e2b649-6712-4480-93a3-5a80b9f8e9f4

import Definitions.Def_FiniteEnergyPlane_Setting

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

namespace S177CW
open FiniteEnergyPlane

lemma norm_cw (z₀ : ℂ) (ρ t : ℝ) : ‖cwLoop z₀ ρ t - z₀‖ = |ρ| := by
  unfold cwLoop
  have : (-(2 * π * t : ℝ) : ℂ) = ((-(2 * π * t) : ℝ) : ℂ) := by push_cast; ring
  rw [add_sub_cancel_left, norm_mul, this, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]

lemma dist_cw (z₀ : ℂ) (r s t : ℝ) : dist (cwLoop z₀ r t) (cwLoop z₀ s t) = |r - s| := by
  have h := norm_cw 0 (r - s) t
  unfold cwLoop at h ⊢
  rw [dist_eq_norm]
  rw [sub_zero, zero_add] at h
  rw [← h]; congr 1; push_cast; ring

end S177CW

open FiniteEnergyPlane in
theorem solution {E : Type*} [NormedAddCommGroup E] (F : ℂ → E)
    (z₀ : ℂ) (R : ℝ) (hF : ContinuousOn F (ball z₀ R \ {z₀})) (r₀ : ℝ) (hr₀ : r₀ ∈ Set.Ioo 0 R)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r in 𝓝 r₀, ∀ t : ℝ, ‖F (cwLoop z₀ r t) - F (cwLoop z₀ r₀ t)‖ ≤ ε := by
  obtain ⟨h0, hR⟩ := hr₀
  set r₁ := (r₀ + R) / 2
  set r₂ := r₀ / 2
  have e1 : r₁ = (r₀ + R) / 2 := rfl
  have e2 : r₂ = r₀ / 2 := rfl
  set A : Set ℂ := closedBall z₀ r₁ \ ball z₀ r₂
  have hAc : IsCompact A := (isCompact_closedBall z₀ r₁).diff isOpen_ball
  have hAs : A ⊆ ball z₀ R \ {z₀} := by
    intro z ⟨h1, h2⟩
    rw [mem_closedBall] at h1
    rw [mem_ball, not_lt] at h2
    refine ⟨mem_ball.2 (by linarith), fun hz => ?_⟩
    rw [Set.mem_singleton_iff] at hz
    subst hz; simp at h2; linarith
  have huc := hAc.uniformContinuousOn_of_continuous (hF.mono hAs)
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδ'⟩ := huc ε hε
  have hmem : Set.Ioo (max r₂ (r₀ - δ)) (min r₁ (r₀ + δ)) ∈ 𝓝 r₀ :=
    Ioo_mem_nhds (max_lt (by linarith) (by linarith)) (lt_min (by linarith) (by linarith))
  filter_upwards [hmem] with r hr t
  obtain ⟨hr1, hr2⟩ := hr
  rw [max_lt_iff] at hr1; rw [lt_min_iff] at hr2
  have mA : ∀ ρ, r₂ ≤ ρ → ρ ≤ r₁ → cwLoop z₀ ρ t ∈ A := by
    intro ρ h1 h2
    have hρ : |ρ| = ρ := abs_of_pos (by linarith)
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm, S177CW.norm_cw, hρ]; exact h2
    · rw [mem_ball, dist_eq_norm, S177CW.norm_cw, hρ, not_lt]; exact h1
  have := hδ' _ (mA r hr1.1.le hr2.1.le) _ (mA r₀ (by linarith) (by linarith))
    (by rw [S177CW.dist_cw, abs_lt]; constructor <;> linarith)
  rw [← dist_eq_norm]; exact this.le
