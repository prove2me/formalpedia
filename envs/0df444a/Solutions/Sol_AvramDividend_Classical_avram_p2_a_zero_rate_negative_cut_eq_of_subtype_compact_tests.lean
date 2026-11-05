-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_negative_cut_eq_of_subtype_compact_tests
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:05:41.592197+00:00
-- url     : https://prove2.me/submissions/eaa94916-e85e-4920-901c-3631ef6f2e69

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Theorems.Thm_AvramDividend_Classical_avram_p2_g_radon_negative_band_compact_test_ext
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal

/-- Transport compact-test uniqueness from the negative subtype to real cuts. -/
theorem solution
    (μ ν : Measure ℝ)
    (hμ : ∀ δ : ℝ, 0 < δ → μ (Iic (-δ)) < ⊤)
    (hν : ∀ δ : ℝ, 0 < δ → ν (Iic (-δ)) < ⊤)
    (hTests : ∀ f : CompactlySupportedContinuousMap {x : ℝ // x < 0} ℝ,
      (∫ x, f x ∂(Measure.comap (Subtype.val : {x : ℝ // x < 0} → ℝ) μ)) =
      (∫ x, f x ∂(Measure.comap (Subtype.val : {x : ℝ // x < 0} → ℝ) ν)))
    (ε : ℝ) (hε : 0 < ε) :
    μ (Iic (-ε)) = ν (Iic (-ε)) := by
  let e : MeasurableEmbedding (Subtype.val : {x : ℝ // x < 0} → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Iio
  have hcut (δ : ℝ) (hδ : 0 < δ) :
      Subtype.val '' {x : {x : ℝ // x < 0} | (x : ℝ) ≤ -δ} = Iic (-δ) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, lt_of_le_of_lt hx (neg_lt_zero.mpr hδ)⟩, hx, rfl⟩
  have hμ' : ∀ δ : ℝ, 0 < δ →
      (Measure.comap (Subtype.val : {x : ℝ // x < 0} → ℝ) μ)
        {x : {x : ℝ // x < 0} | (x : ℝ) ≤ -δ} < ⊤ := by
    intro δ hδ
    rw [e.comap_apply, hcut δ hδ]
    exact hμ δ hδ
  have hν' : ∀ δ : ℝ, 0 < δ →
      (Measure.comap (Subtype.val : {x : ℝ // x < 0} → ℝ) ν)
        {x : {x : ℝ // x < 0} | (x : ℝ) ≤ -δ} < ⊤ := by
    intro δ hδ
    rw [e.comap_apply, hcut δ hδ]
    exact hν δ hδ
  have heq := avram_p2_g_radon_negative_band_compact_test_ext
    _ _ hμ' hν' hTests
  have hval := congrArg (fun q : Measure {x : ℝ // x < 0} =>
    q {x : {x : ℝ // x < 0} | (x : ℝ) ≤ -ε}) heq
  simpa only [e.comap_apply, hcut ε hε] using hval
