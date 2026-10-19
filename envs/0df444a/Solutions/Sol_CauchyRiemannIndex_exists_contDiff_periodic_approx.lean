-- Prove2me | solution 1 for CauchyRiemannIndex.exists_contDiff_periodic_approx
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T16:39:10.001305+00:00
-- url     : https://prove2.me/submissions/50292250-6075-44f0-80b0-55a2ab95fce6

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Topology.Instances.Real.Lemmas



/-!
# Smooth periodic approximation of a continuous periodic function
-/

namespace CauchyRiemannIndex

open MeasureTheory Metric
open scoped ContDiff Convolution

noncomputable section

lemma crw_unif (f : ℝ → ℝ) (hf : Continuous f) (hper : Function.Periodic f 1) (ε : ℝ)
    (hε : 0 < ε) : ∃ δ > 0, ∀ x₀ x : ℝ, dist x x₀ < δ → dist (f x) (f x₀) ≤ ε := by
  have hK : IsCompact (Set.Icc (-1 : ℝ) 2) := isCompact_Icc
  have hu := hK.uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨δ, hδ, h⟩ := hu ε hε
  refine ⟨min δ 1, lt_min hδ one_pos, fun x₀ x hx => ?_⟩
  have hx1 : dist x x₀ < δ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx2 : dist x x₀ < 1 := lt_of_lt_of_le hx (min_le_right _ _)
  set k : ℤ := ⌊x₀⌋
  have e1 : f x = f (x - k * 1) := (hper.sub_int_mul_eq k).symm
  have e2 : f x₀ = f (x₀ - k * 1) := (hper.sub_int_mul_eq k).symm
  rw [e1, e2]
  have hk1 : (k : ℝ) ≤ x₀ := Int.floor_le x₀
  have hk2 : x₀ < k + 1 := Int.lt_floor_add_one x₀
  rw [Real.dist_eq, abs_lt] at hx2
  refine le_of_lt (h _ ⟨by linarith, by linarith⟩ _ ⟨by linarith, by linarith⟩ ?_)
  rw [Real.dist_eq] at hx1 ⊢
  rwa [show x - k * 1 - (x₀ - k * 1) = x - x₀ by ring]

/-- A continuous `1`-periodic real function is uniformly approximated, to any `ε > 0`, by a
smooth `1`-periodic function. -/
theorem exists_contDiff_periodic_approx_aux (f : ℝ → ℝ) (hf : Continuous f)
    (hper : Function.Periodic f 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ Function.Periodic g 1 ∧ ∀ t, |g t - f t| ≤ ε := by
  obtain ⟨δ, hδ, hδf⟩ := crw_unif f hf hper ε hε
  let φ : ContDiffBump (0 : ℝ) := ⟨δ / 2, δ, by linarith, by linarith⟩
  refine ⟨φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f, ?_, ?_, ?_⟩
  · exact φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      hf.locallyIntegrable
  · intro x
    simp only [convolution_def]
    congr 1
    funext y
    rw [show x + 1 - y = (x - y) + 1 by ring, hper]
  · intro t
    rw [← Real.dist_eq]
    exact φ.dist_normed_convolution_le hf.aestronglyMeasurable
      (fun x hx => hδf t x (mem_ball.1 hx))

end

end CauchyRiemannIndex

open CauchyRiemannIndex

open scoped ContDiff

theorem solution (f : ℝ → ℝ) (hf : Continuous f)
    (hper : Function.Periodic f 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ Function.Periodic g 1 ∧ ∀ t, |g t - f t| ≤ ε :=
  CauchyRiemannIndex.exists_contDiff_periodic_approx_aux f hf hper ε hε
