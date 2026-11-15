-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_integrable_norm_series_integrable_total_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:48:16.216204+00:00
-- url     : https://prove2.me/submissions/17372013-19ff-4248-afde-f67e7e56dd56

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (H : ℕ → Ω → ℝ)
    (hHI : ∀ k, Integrable (H k) P)
    (hSum : Summable (fun k => ∫ ω, ‖H k ω‖ ∂P)) :
    ∃ (B : Ω → ℝ),
      Integrable B P ∧
      (∀ᵐ ω ∂P, Summable (fun k => ‖H k ω‖) ∧ (∑' k, ‖H k ω‖) ≤ B ω) ∧
      (∀ k, ∀ᵐ ω ∂P, ‖H k ω‖ ≤ B ω) := by
  let f : ℕ → Ω → ℝ≥0∞ := fun k ω => ENNReal.ofReal (‖H k ω‖)
  have hf (k : ℕ) : AEMeasurable (f k) P :=
    (hHI k).norm.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hfm : AEMeasurable (fun ω => ∑' k, f k ω) P :=
    AEMeasurable.ennreal_tsum hf
  have hnonneg (k : ℕ) : 0 ≤ ∫ ω, ‖H k ω‖ ∂P :=
    integral_nonneg (fun ω => norm_nonneg (H k ω))
  have htotal :
      (∫⁻ ω, ∑' k, f k ω ∂P) =
      ENNReal.ofReal (∑' k, ∫ ω, ‖H k ω‖ ∂P) := by
    rw [lintegral_tsum hf]
    have hi (k : ℕ) :
        (∫⁻ ω, f k ω ∂P) = ENNReal.ofReal (∫ ω, ‖H k ω‖ ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal
        (hHI k).norm (Filter.Eventually.of_forall
          (fun ω => norm_nonneg (H k ω)))).symm
    simp_rw [hi]
    exact (ENNReal.ofReal_tsum_of_nonneg hnonneg hSum).symm
  have hfinite : (∫⁻ ω, ∑' k, f k ω ∂P) ≠ ∞ := by
    rw [htotal]
    exact ENNReal.ofReal_ne_top
  let B : Ω → ℝ := fun ω => (∑' k, f k ω).toReal
  have hBI : Integrable B P :=
    integrable_toReal_of_lintegral_ne_top hfm hfinite
  have hgood : ∀ᵐ ω ∂P,
      Summable (fun k => ‖H k ω‖) ∧
      (∑' k, ‖H k ω‖) ≤ B ω := by
    filter_upwards [ae_lt_top' hfm hfinite] with ω hω
    let v : ℕ → ℝ≥0 := fun k => NNReal.mk (‖H k ω‖) (norm_nonneg (H k ω))
    have hs : Summable (fun k => (v k : ℝ)) :=
      ENNReal.tsum_coe_ne_top_iff_summable_coe.mp (by
        convert ne_of_lt hω using 1
        apply tsum_congr
        intro k
        simpa only [v, f] using
          (ENNReal.ofReal_eq_coe_nnreal (norm_nonneg (H k ω))).symm)
    have hs' : Summable (fun k => ‖H k ω‖) := by
      simpa [v] using hs
    refine ⟨hs', le_of_eq ?_⟩
    change (∑' k, ‖H k ω‖) =
      (∑' k, ENNReal.ofReal (‖H k ω‖)).toReal
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun k => norm_nonneg (H k ω)) hs',
      ENNReal.toReal_ofReal
        (tsum_nonneg (fun k => norm_nonneg (H k ω)))]
  refine ⟨B, hBI, hgood, ?_⟩
  intro k
  filter_upwards [hgood] with ω ⟨hs, hle⟩
  calc
    ‖H k ω‖ = ∑ i ∈ ({k} : Finset ℕ), ‖H i ω‖ := by simp
    _ ≤ ∑' i, ‖H i ω‖ :=
      hs.sum_le_tsum {k} (fun i _ => norm_nonneg (H i ω))
    _ ≤ B ω := hle
