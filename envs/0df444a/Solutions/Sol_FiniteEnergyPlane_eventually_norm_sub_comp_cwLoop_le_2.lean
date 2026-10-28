-- Prove2me | solution 2 for FiniteEnergyPlane.eventually_norm_sub_comp_cwLoop_le
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-25T23:44:15.401342+00:00
-- url     : https://prove2.me/submissions/5d6296ef-a088-4b6a-acfc-39e6daca34d1

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_FiniteEnergyPlane_Setting

open FiniteEnergyPlane MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {E : Type*} [NormedAddCommGroup E] (F : ℂ → E)
    (z₀ : ℂ) (R : ℝ) (hF : ContinuousOn F (ball z₀ R \ {z₀})) (r₀ : ℝ) (hr₀ : r₀ ∈ Set.Ioo 0 R)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r in 𝓝 r₀, ∀ t : ℝ, ‖F (cwLoop z₀ r t) - F (cwLoop z₀ r₀ t)‖ ≤ ε := by
  obtain ⟨hr0, hrR⟩ := hr₀
  set K : Set ℂ := {z | r₀ / 2 ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ (r₀ + R) / 2} with hK
  have hKc : IsCompact K := by
    have : K = closedBall z₀ ((r₀ + R) / 2) \ ball z₀ (r₀ / 2) := by
      ext z; simp [K, dist_eq_norm, not_lt, and_comm]
    rw [this]; exact (isCompact_closedBall _ _).diff isOpen_ball
  have hKs : K ⊆ ball z₀ R \ {z₀} := by
    rintro z ⟨h1, h2⟩
    refine ⟨by rw [mem_ball, dist_eq_norm]; linarith, ?_⟩
    rintro rfl
    simp at h1
    linarith
  obtain ⟨δ, hδ, hδF⟩ :=
    Metric.uniformContinuousOn_iff.1 (hKc.uniformContinuousOn_of_continuous (hF.mono hKs)) ε hε
  have hη : 0 < min δ (min (r₀ / 2) ((R - r₀) / 2)) :=
    lt_min hδ (lt_min (half_pos hr0) (half_pos (sub_pos.2 hrR)))
  filter_upwards [Metric.ball_mem_nhds r₀ hη] with r hr
  rw [mem_ball, Real.dist_eq] at hr
  intro t
  have he : ‖Complex.exp (-((2 * π * t : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    rw [← Complex.ofReal_neg]; exact Complex.norm_exp_ofReal_mul_I _
  have hmem : ∀ s : ℝ, |s - r₀| < min (r₀ / 2) ((R - r₀) / 2) → cwLoop z₀ s t ∈ K := by
    intro s hs
    rw [lt_min_iff, abs_lt, abs_lt] at hs
    have hn : ‖cwLoop z₀ s t - z₀‖ = s := by
      rw [cwLoop, add_sub_cancel_left, norm_mul, he, Complex.norm_real, Real.norm_eq_abs,
        mul_one, abs_of_pos (by linarith)]
    rw [hK, Set.mem_ofPred_eq, hn]
    constructor <;> linarith
  have h1 := hmem r (lt_of_lt_of_le hr (min_le_right _ _))
  have h2 := hmem r₀ (by rw [sub_self, abs_zero]; exact lt_min (half_pos hr0) (half_pos (sub_pos.2 hrR)))
  have hd : dist (cwLoop z₀ r t) (cwLoop z₀ r₀ t) < δ := by
    rw [dist_eq_norm, show cwLoop z₀ r t - cwLoop z₀ r₀ t =
      ((r : ℂ) - r₀) * Complex.exp (-((2 * π * t : ℝ) : ℂ) * Complex.I) by simp only [cwLoop]; ring,
      norm_mul, he, mul_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact lt_of_lt_of_le hr (min_le_left _ _)
  rw [← dist_eq_norm]
  exact (hδF _ h1 _ h2 hd).le
