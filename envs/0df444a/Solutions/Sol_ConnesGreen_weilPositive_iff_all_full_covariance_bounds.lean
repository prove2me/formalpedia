-- Prove2me | solution 1 for ConnesGreen.weilPositive_iff_all_full_covariance_bounds
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T17:17:17.978127+00:00
-- url     : https://prove2.me/submissions/60ad891a-9810-4d50-a652-7474cc1b3d22

import Theorems.Thm_ConnesGreen_canonical_signed_actor_arithmetic
import Theorems.Thm_ConnesGreen_covariance_le_iff_original_tests
import Definitions.Def_ConnesGreen_RG0_original_actors
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
private theorem support_radius_helper (g : ℝ → ℂ) (hg : IsTest g) :
    ∃ t : ℝ, 0 < t ∧ SupportedTest t g := by
  obtain ⟨t, ht, hs⟩ := hg.2.isBounded.subset_ball_lt 0 (0 : ℝ)
  refine ⟨t, ht, hg, ?_⟩
  intro x hx
  have hb := hs hx
  have hab : |x| < t := by simpa [Metric.mem_ball, Real.dist_eq] using hb
  exact abs_lt.mp hab


theorem solution :
    (∀ g : ℝ → ℂ, ConnesRZ.IsTest g →
      0 ≤ (ConnesRZ.weilDistribution (ConnesRZ.conv g (ConnesRZ.starInv g))).re) ↔ ∀ t : ℝ, ∀ ht : 0 < t,
      canonicalNegativeSynthesis t ht ∘L (canonicalNegativeSynthesis t ht).adjoint ≤
        canonicalPositiveCovariance t ht := by
  have positive (t : ℝ) (ht : 0 < t) (g : ℝ → ℂ) :
      RCLike.re ⟪(canonicalPositiveSynthesis t ht ∘L (canonicalPositiveSynthesis t ht).adjoint) (sourceEmbed t (problemOneL g)),
        sourceEmbed t (problemOneL g)⟫_ℂ =
      ‖(canonicalPositiveSynthesis t ht).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 := by
    have hp := (canonicalPositiveSynthesis t ht).adjoint.apply_norm_sq_eq_inner_adjoint_left
      (sourceEmbed t (problemOneL g))
    simp only [ContinuousLinearMap.adjoint_adjoint] at hp
    exact hp.symm
  constructor
  · intro h t ht
    apply (covariance_le_iff_original_tests t ht _
      (ContinuousLinearMap.isPositive_self_comp_adjoint
        (canonicalPositiveSynthesis t ht)).isSelfAdjoint _).mpr
    intro g hg
    rw [positive]
    have ha := ConnesGreen.canonical_signed_actor_arithmetic t ht g hg
    have hw := h g hg.1
    linarith
  · intro h g hg
    obtain ⟨t, ht, hgt⟩ := support_radius_helper g hg
    have hb := (covariance_le_iff_original_tests t ht _
      (ContinuousLinearMap.isPositive_self_comp_adjoint
        (canonicalPositiveSynthesis t ht)).isSelfAdjoint _).mp (h t ht) g hgt
    rw [positive] at hb
    have ha := ConnesGreen.canonical_signed_actor_arithmetic t ht g hgt
    linarith
