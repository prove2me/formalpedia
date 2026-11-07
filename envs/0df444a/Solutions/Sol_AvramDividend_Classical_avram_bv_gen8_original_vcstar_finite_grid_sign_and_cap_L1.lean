-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_gen8_original_vcstar_finite_grid_sign_and_cap_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:24:42.700514+00:00
-- url     : https://prove2.me/submissions/763d507a-80a1-421a-a4cb-da2e6fe59518

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_vcstar_full_positive_cell_sign_and_cap_zero
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_vcstar_closed_prebarrier_uniform_grid_L1_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Finite stopped generator sums have the required one-sided sign. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, u n i ≤ u n (i + 1)) :
    let H : ℕ → ℕ → Ω → ℝ := fun n i ω =>
      let Z : ℝ := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator (vcstar W) Z - q * vcstar W Z) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    (∀ n ω, (∑ i ∈ Finset.range (n + 1), H n i ω) ≤ 0) ∧
      let G : ℕ → ℕ → Ω → ℝ := fun n i ω =>
        let Z : ℝ := Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z ∧ Z ≤ (cstar W).toReal then
          Real.exp (-(q * (u n i : ℝ))) *
            (X.generator (vcstar W) Z - q * vcstar W Z) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0
      ∀ n : ℕ,
        (∀ ω, (∑ i ∈ Finset.range (n + 1), G n i ω) = 0) ∧
        Integrable (fun ω => ∑ i ∈ Finset.range (n + 1), G n i ω) P := by
  let H : ℕ → ℕ → Ω → ℝ := fun n i ω =>
    let Z : ℝ := Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z then
      Real.exp (-(q * (u n i : ℝ))) *
        (X.generator (vcstar W) Z - q * vcstar W Z) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))
    else 0
  change (∀ n ω, (∑ i ∈ Finset.range (n + 1), H n i ω) ≤ 0) ∧
    (let G : ℕ → ℕ → Ω → ℝ := fun n i ω =>
      let Z : ℝ := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z ∧ Z ≤ (cstar W).toReal then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator (vcstar W) Z - q * vcstar W Z) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    ∀ n : ℕ,
      (∀ ω, (∑ i ∈ Finset.range (n + 1), G n i ω) = 0) ∧
      Integrable (fun ω => ∑ i ∈ Finset.range (n + 1), G n i ω) P)
  constructor
  · intro n ω
    have hcell := (avram_bv_gen8_original_vcstar_full_positive_cell_sign_and_cap_zero
      X hX hBV q hq W hW hc hcpos hgen x D u hmono).1
    exact Finset.sum_nonpos (fun i hi => hcell n i ω)
  · exact avram_bv_gen8_vcstar_closed_prebarrier_uniform_grid_L1_zero
      X hX hBV q hq W hW hc hcpos hgen x D u
