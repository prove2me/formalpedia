-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_canonical_source_remainder_stopped_C1_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:37:05.421885+00:00
-- url     : https://prove2.me/submissions/e013e879-e7b6-480b-b83f-a5cd807cfcf3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_canonical_remainder_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- One canonical monotone actual BV source remainder path has a nonpositive
derivative-weighted finite-variation contribution at every stopped controlled
partition. Source left jumps and chronological right payments stay distinct. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (u : ℝ≥0),
            if 0 < u ∧ u ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω)
        (hgrad : ∀ i : Fin n,
          0 ≤ deriv w (riskProcess X x D (u i) ω)),
        (∑ i : Fin n,
          -(deriv w (riskProcess X x D (u i) ω)) *
            (R (u (i + 1)) - R (u i))) ≤ 0 := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_canonical_remainder_monotone X hBV]
    with ω hmono
  let R (t : ℝ≥0) : ℝ :=
    ((t : ℝ) * X.drift - X.X t ω) -
      (∑' (u : ℝ≥0),
        if 0 < u ∧ u ≤ t then
          ENNReal.ofReal (Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
        else 0).toReal
  refine ⟨R, ?_, ?_, ?_⟩
  · intro t
    rfl
  · exact hmono
  intro τ u hu n hstop hgrad
  apply Finset.sum_nonpos
  intro i hi
  have hinc : 0 ≤ R (u (i + 1)) - R (u i) :=
    sub_nonneg.mpr (hmono (hu (Nat.le_succ _)))
  have hnonneg :
      0 ≤ deriv w (riskProcess X x D (u i) ω) *
        (R (u (i + 1)) - R (u i)) :=
    mul_nonneg (hgrad i) hinc
  nlinarith only [hnonneg]
