-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_gen8_original_interior_vcstar_full_uniform_grid_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:49:17.103985+00:00
-- url     : https://prove2.me/submissions/c662572f-4744-442d-be59-f6fcad4cb3af

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_vcstar_generator_interior_cell_L1_any_grid
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact finite-grid assembly from original strict-interior generator cells. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (u : ℕ → ℕ → ℝ≥0) :
    let H : ℕ → ℕ → Ω → ℝ := fun n i ω =>
      let Z : ℝ := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z ∧ ENNReal.ofReal Z < cstar W then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator (vcstar W) Z - q * vcstar W Z) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    ∀ n, (∀ ω, (∑ i ∈ Finset.range (n + 1), H n i ω) = 0) ∧
      Integrable (fun ω => ∑ i ∈ Finset.range (n + 1), H n i ω) P := by
  let H : ℕ → ℕ → Ω → ℝ := fun n i ω =>
    let Z : ℝ := Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
        0 < Z ∧ ENNReal.ofReal Z < cstar W then
      Real.exp (-(q * (u n i : ℝ))) *
        (X.generator (vcstar W) Z - q * vcstar W Z) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))
    else 0
  change ∀ n, (∀ ω, (∑ i ∈ Finset.range (n + 1), H n i ω) = 0) ∧
    Integrable (fun ω => ∑ i ∈ Finset.range (n + 1), H n i ω) P
  have hcell : ∀ n i ω, H n i ω = 0 := by
    intro n i ω
    exact (avram_bv_gen8_original_vcstar_generator_interior_cell_L1_any_grid
      X hX hBV q hq W hW hc hcpos x D u n i).1 ω
  have hs : ∀ n ω, (∑ i ∈ Finset.range (n + 1), H n i ω) = 0 := by
    intro n ω
    apply Finset.sum_eq_zero
    intro i hi
    exact hcell n i ω
  intro n
  refine ⟨hs n, ?_⟩
  have heq : (fun ω => ∑ i ∈ Finset.range (n + 1), H n i ω) =
    (fun _ : Ω => (0 : ℝ)) := by
    funext ω
    exact hs n ω
  rw [heq]
  exact integrable_zero Ω ℝ P
