-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_gen8_original_vcstar_clipped_finite_grid_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:20:29.347208+00:00
-- url     : https://prove2.me/submissions/54241820-a529-4300-8163-941574340883

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_vcstar_full_positive_cell_sign_and_cap_zero
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Nonpositive original generator sums admit integrable bounded clipping. -/
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
      ∀ n, Integrable (fun ω =>
        max (-K) (∑ i ∈ Finset.range (n + 1), H n i ω)) P := by
  letI : IsProbabilityMeasure P := X.isProbability
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
      ∀ n, Integrable (fun ω =>
        max (-K) (∑ i ∈ Finset.range (n + 1), H n i ω)) P
  intro hMeas K hK n
  let F : Ω → ℝ := fun ω => ∑ i ∈ Finset.range (n + 1), H n i ω
  change Integrable (fun ω => max (-K) (F ω)) P
  have hcell := (avram_bv_gen8_original_vcstar_full_positive_cell_sign_and_cap_zero
    X hX hBV q hq W hW hc hcpos hgen x D u hmono).1
  have hNonpos : ∀ ω, F ω ≤ 0 := by
    intro ω
    exact Finset.sum_nonpos (fun i hi => hcell n i ω)
  have hcont : Continuous (fun z : ℝ => max (-K) z) :=
    continuous_const.max continuous_id
  have hClip : AEStronglyMeasurable (fun ω => max (-K) (F ω)) P :=
    hcont.comp_aestronglyMeasurable (hMeas n)
  have hBound : ∀ ω, ‖max (-K) (F ω)‖ ≤ K := by
    intro ω
    have hLower : -K ≤ max (-K) (F ω) := le_max_left _ _
    have hUpper : max (-K) (F ω) ≤ 0 :=
      max_le (neg_nonpos.mpr hK) (hNonpos ω)
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨hLower, le_trans hUpper hK⟩
  exact Integrable.of_bound hClip K (Filter.Eventually.of_forall hBound)
