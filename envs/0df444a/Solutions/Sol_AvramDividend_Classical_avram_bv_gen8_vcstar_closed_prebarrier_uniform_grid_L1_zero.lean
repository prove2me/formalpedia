-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_gen8_vcstar_closed_prebarrier_uniform_grid_L1_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:08:42.007256+00:00
-- url     : https://prove2.me/submissions/961005d9-8495-4305-ad0d-0d3fbe7dc049

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_vcstar_closed_prebarrier_original_generator_cell_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Original positive-BV cap-and-interior losses vanish on every finite grid. -/
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
    (u : ℕ → ℕ → ℝ≥0) :
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
  let G : ℕ → ℕ → Ω → ℝ := fun n i ω =>
    let Z : ℝ := Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
        0 < Z ∧ Z ≤ (cstar W).toReal then
      Real.exp (-(q * (u n i : ℝ))) *
        (X.generator (vcstar W) Z - q * vcstar W Z) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))
    else 0
  change ∀ n : ℕ,
    (∀ ω, (∑ i ∈ Finset.range (n + 1), G n i ω) = 0) ∧
    Integrable (fun ω => ∑ i ∈ Finset.range (n + 1), G n i ω) P
  intro n
  have hcell : ∀ (i : ℕ) (ω : Ω), G n i ω = 0 := by
    intro i ω
    exact avram_bv_gen8_vcstar_closed_prebarrier_original_generator_cell_zero
      X hX hBV q hq W hW hc hcpos hgen x D u n i ω
  have hsum : ∀ ω, (∑ i ∈ Finset.range (n + 1), G n i ω) = 0 := by
    intro ω
    simp [hcell]
  refine ⟨hsum, ?_⟩
  have hfun : (fun ω => ∑ i ∈ Finset.range (n + 1), G n i ω) =
      (fun _ : Ω => (0 : ℝ)) := funext hsum
  rw [hfun]
  exact integrable_zero _ _ _
