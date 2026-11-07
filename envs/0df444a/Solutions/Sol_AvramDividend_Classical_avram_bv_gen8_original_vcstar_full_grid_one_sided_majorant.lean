-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_gen8_original_vcstar_full_grid_one_sided_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:33:15.12932+00:00
-- url     : https://prove2.me/submissions/79418de2-9791-4d9c-a77c-c1e25aae2aa0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_vcstar_full_positive_cell_sign_and_cap_zero
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_vcstar_clipped_finite_grid_integrable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The full original candidate generator is one-sidedly dominated by integrable clipping. -/
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
    (∀ n, AEStronglyMeasurable
      (fun ω => ∑ i ∈ Finset.range (n + 1), H n i ω) P) →
    ∀ (K : ℝ), 0 ≤ K →
      ∀ n, (Integrable (fun ω =>
        max (-K) (∑ i ∈ Finset.range (n + 1), H n i ω)) P ∧
      (∫ ω, max (-K) (∑ i ∈ Finset.range (n + 1), H n i ω) ∂P) ≤ 0) ∧
      ∀ ω, (∑ i ∈ Finset.range (n + 1), H n i ω) ≤
        max (-K) (∑ i ∈ Finset.range (n + 1), H n i ω) := by
  let H : ℕ → ℕ → Ω → ℝ := fun n i ω =>
    let Z : ℝ := Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z then
      Real.exp (-(q * (u n i : ℝ))) *
        (X.generator (vcstar W) Z - q * vcstar W Z) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))
    else 0
  change (∀ n, AEStronglyMeasurable
      (fun ω => ∑ i ∈ Finset.range (n + 1), H n i ω) P) →
    ∀ (K : ℝ), 0 ≤ K →
      ∀ n, (Integrable (fun ω =>
        max (-K) (∑ i ∈ Finset.range (n + 1), H n i ω)) P ∧
      (∫ ω, max (-K) (∑ i ∈ Finset.range (n + 1), H n i ω) ∂P) ≤ 0) ∧
      ∀ ω, (∑ i ∈ Finset.range (n + 1), H n i ω) ≤
        max (-K) (∑ i ∈ Finset.range (n + 1), H n i ω)
  intro hMeas K hK n
  have hcell := (avram_bv_gen8_original_vcstar_full_positive_cell_sign_and_cap_zero
    X hX hBV q hq W hW hc hcpos hgen x D u hmono).1
  have hNonpos : ∀ ω, (∑ i ∈ Finset.range (n + 1), H n i ω) ≤ 0 := by
    intro ω
    exact Finset.sum_nonpos (fun i hi => hcell n i ω)
  have hInt : Integrable (fun ω =>
      max (-K) (∑ i ∈ Finset.range (n + 1), H n i ω)) P :=
    avram_bv_gen8_original_vcstar_clipped_finite_grid_integrable
      X hX hBV q hq W hW hc hcpos hgen x D u hmono hMeas K hK n
  constructor
  · constructor
    · exact hInt
    · apply integral_nonpos_of_ae
      exact Filter.Eventually.of_forall (fun ω =>
        max_le (neg_nonpos.mpr hK) (hNonpos ω))
  · intro ω
    exact le_max_right _ _
