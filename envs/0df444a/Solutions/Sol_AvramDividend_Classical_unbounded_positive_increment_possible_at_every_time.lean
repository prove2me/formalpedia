-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_positive_increment_possible_at_every_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T08:14:01.964184+00:00
-- url     : https://prove2.me/submissions/35aaf4ce-76ca-4181-8369-cf2f6eba8539

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_psi_eventually_gt_of_unbounded_variation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- A positive-time Lévy increment has a genuine chance to be positive
    whenever unbounded variation forces the Laplace exponent above zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (t : ℝ≥0) (ht : 0 < t) :
    ¬ (∀ᵐ ω ∂P, X.X t ω ≤ 0) := by
  intro hNonpos
  haveI := X.isProbability
  obtain ⟨β, hβ0, hβ⟩ :=
    chat04_psi_eventually_gt_of_unbounded_variation X 1 (by norm_num) hnbv
  obtain ⟨hint, heq⟩ := X.laplace t β hβ0
  have hle : ∫ ω, Real.exp (β * X.X t ω) ∂P ≤
      ∫ _ω, (1 : ℝ) ∂P := by
    refine integral_mono_ae hint (integrable_const _) ?_
    filter_upwards [hNonpos] with ω hω
    exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos hβ0 hω)
  rw [heq, integral_const, probReal_univ, one_smul] at hle
  have hψ : 0 < X.ψ β := lt_trans (by norm_num) (hβ β le_rfl)
  have hExponent : 0 < (t : ℝ) *
      laplaceExponent X.c X.σ X.ν β := by
    apply mul_pos
    · exact_mod_cast ht
    · simpa [SpectrallyNegativeLevy.ψ] using hψ
  have hStrict := Real.add_one_lt_exp hExponent.ne'
  linarith
