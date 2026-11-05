-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_negative_exp_fourth_weighted_source_measure_ext
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:57:41.484312+00:00
-- url     : https://prove2.me/submissions/2d104712-9b37-46fe-9fcf-b30a3709724a

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- Equality of fourth-weighted exponential images on strictly negative
real marks identifies the original Borel source measures, with no moment,
finite-mass, stationary-count or rate assumption. -/
theorem solution
    (μ ν : Measure ℝ)
    (hnegμ : ∀ᵐ y ∂μ, y < 0)
    (hnegν : ∀ᵐ y ∂ν, y < 0)
    (himage :
      (μ.withDensity (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp =
      (ν.withDensity (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp) :
    μ = ν := by
  let w : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4)
  have hw : Measurable w := by
    dsimp [w]
    fun_prop
  have hzero (σ : Measure ℝ) (hneg : ∀ᵐ y ∂σ, y < 0) :
      ∀ᵐ y ∂σ, w y ≠ 0 := by
    filter_upwards [hneg] with y hy
    have he : Real.exp y < 1 := (Real.exp_lt_one_iff).mpr hy
    have hp : 0 < 1 - Real.exp y := sub_pos.mpr he
    have hpow : 0 < (Real.exp y - 1) ^ 4 := by
      have heq : (Real.exp y - 1) ^ 4 = (1 - Real.exp y) ^ 4 := by ring
      rw [heq]
      exact pow_pos hp 4
    change ENNReal.ofReal ((Real.exp y - 1) ^ 4) ≠ 0
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hpow)
  have htop (σ : Measure ℝ) : ∀ᵐ y ∂σ, w y ≠ ⊤ := by
    filter_upwards [] with y
    simp [w]
  have hf : MeasurableEmbedding (Real.exp : ℝ → ℝ) :=
    Real.continuous_exp.measurableEmbedding Real.exp_injective
  have hweighted : μ.withDensity w = ν.withDensity w := by
    apply hf.map_injective
    exact himage
  have hinv := congrArg
    (fun ξ : Measure ℝ => ξ.withDensity (fun y => (w y)⁻¹)) hweighted
  rw [withDensity_inv_same hw (hzero μ hnegμ) (htop μ),
      withDensity_inv_same hw (hzero ν hnegν) (htop ν)] at hinv
  exact hinv
