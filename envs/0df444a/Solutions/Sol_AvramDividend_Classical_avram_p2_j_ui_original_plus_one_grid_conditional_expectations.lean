-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_original_plus_one_grid_conditional_expectations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:57:39.527376+00:00
-- url     : https://prove2.me/submissions/eddcced4-4af1-4a13-b5bf-fe6d46c4190f

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_bounded_negative_test_grid_l2_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_eventual_finite_envelope_expectations

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-! The original Lévy uniform-grid (n+1)-interval convention of P2-A and P2-H. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) (T : ℝ) (hT : 0 ≤ T)
    (f : ℝ → ENNReal) (M : ENNReal) (hM : M ≠ ⊤)
    (hf : ∀ y : ℝ, f y ≤ if y ≤ -ε then M else 0)
    (h : ℕ → ℝ) (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hmesh : Tendsto h atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hhor : ∀ᶠ n : ℕ in atTop, ((n + 1 : ℕ) : ℝ) * h n ≤ T)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hdom : ∀ n, ∀ᵐ ω ∂P, ‖Y n ω‖ₑ ≤
      ∑ i ∈ Finset.range (n + 1),
        f (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (h n)) ω -
          X.X ((i : ℝ≥0) * Real.toNNReal (h n)) ω))
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (nhds (∫ ω, Z ω ∂P)) := by
  obtain ⟨C, hC, hgrid⟩ :=
    avram_p2_original_bounded_negative_test_grid_l2_bound
      X ε hε T hT f M hM hf
  let K : ENNReal :=
    M ^ 2 * (ENNReal.ofReal (C * T) + (ENNReal.ofReal (C * T)) ^ 2)
  have hK : K ≠ ⊤ := by
    have hct : ENNReal.ofReal (C * T) ≠ ⊤ := ENNReal.ofReal_ne_top
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top hM)
      (ENNReal.add_ne_top.mpr ⟨hct, ENNReal.pow_ne_top hct⟩)
  let G : ℕ → Ω → ENNReal := fun n ω =>
    ∑ i ∈ Finset.range (n + 1),
      f (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (h n)) ω -
        X.X ((i : ℝ≥0) * Real.toNNReal (h n)) ω)
  have hEventual : ∀ᶠ n : ℕ in atTop,
      (∫⁻ ω, (G n ω) ^ 2 ∂P) ≤ K := by
    filter_upwards [hmesh.eventually hgrid, hhor] with n hsmall htime
    exact hsmall (n + 1) htime
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hEventual
  apply avram_p2_j_ui_eventual_finite_envelope_expectations
    P Y Z G K N hK hm
  · intro n
    simpa only [G] using hdom n
  · intro n hn
    simpa [ENNReal.rpow_natCast] using hN n hn
  · exact hae
