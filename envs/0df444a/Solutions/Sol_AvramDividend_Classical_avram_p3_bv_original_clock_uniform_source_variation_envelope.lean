-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_clock_uniform_source_variation_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:00:54.444963+00:00
-- url     : https://prove2.me/submissions/fdd81662-a047-433e-a043-8e0927671937

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_raw_J_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- The original positive source-jump variation and the residual removed
from physical drift are both monotone on the original probability space.
Their total variation on any finite clock has one random finite bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (τ : ℝ≥0) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      ∀ (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ)
        (hEnd : ∀ k, (u k) (n k) ≤ τ),
        ∃ M : ℝ, 0 ≤ M ∧ ∀ k,
          |X.drift| * (((u k) (n k) : ℝ) - ((u k) 0 : ℝ)) +
            (R ((u k) (n k)) - R ((u k) 0)) +
            (J ((u k) (n k)) - J ((u k) 0)) ≤ M := by
  filter_upwards
    [avram_p3_a_bvdrift_original_raw_removed_residual_monotone X hBV,
     avram_p3_f_chainlimit_original_raw_J_monotone X hBV]
    with ω hR hJ
  dsimp only
  intro u n hEnd
  let J : ℝ≥0 → ℝ := fun t =>
    ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
    else 0
  let R : ℝ≥0 → ℝ := fun t =>
    ((t : ℝ) * X.drift - X.X t ω) - J t
  have hRm : Monotone R := hR
  have hJm : Monotone J := by
    intro s t hst
    exact hJ s t hst
  have hR0 : R 0 ≤ R τ := hRm (by positivity)
  have hJ0 : J 0 ≤ J τ := hJm (by positivity)
  have hτ0 : 0 ≤ (τ : ℝ) := NNReal.coe_nonneg _
  have hM0 : 0 ≤ |X.drift| * (τ : ℝ) +
      (R τ - R 0) + (J τ - J 0) := by
    nlinarith [mul_nonneg (abs_nonneg X.drift) hτ0]
  refine ⟨|X.drift| * (τ : ℝ) +
    (R τ - R 0) + (J τ - J 0), hM0, ?_⟩
  intro k
  have hRstart := hRm (by positivity : (0 : ℝ≥0) ≤ (u k) 0)
  have hRend := hRm (hEnd k)
  have hJstart := hJm (by positivity : (0 : ℝ≥0) ≤ (u k) 0)
  have hJend := hJm (hEnd k)
  have hu0 : 0 ≤ (((u k) 0 : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  have huEnd : (((u k) (n k) : ℝ≥0) : ℝ) ≤ (τ : ℝ) :=
    NNReal.coe_le_coe.mpr (hEnd k)
  have hDle : |X.drift| *
      (((u k) (n k) : ℝ) - ((u k) 0 : ℝ)) ≤
      |X.drift| * (τ : ℝ) := by
    apply mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    linarith
  have hRle : R ((u k) (n k)) - R ((u k) 0) ≤
      R τ - R 0 := sub_le_sub hRend hRstart
  have hJle : J ((u k) (n k)) - J ((u k) 0) ≤
      J τ - J 0 := sub_le_sub hJend hJstart
  exact add_le_add (add_le_add hDle hRle) hJle
