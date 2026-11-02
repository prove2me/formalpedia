-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_source_remainder_local_gradient_weighted_stopped_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:51:59.409107+00:00
-- url     : https://prove2.me/submissions/d1273aff-d16f-455d-b82a-dc435173c616

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_canonical_remainder_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Original BV source residual sign needs derivatives nonnegative only
at sampled stopped reserves, not global monotonicity of the HJB candidate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω)
        (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
        (hderiv : ∀ i : Fin n,
          0 ≤ deriv w (riskProcess X x D (u i) ω)),
        (∑ i : Fin n,
          -(a i * deriv w (riskProcess X x D (u i) ω)) *
            (R (u (i + 1)) - R (u i))) ≤ 0 := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_canonical_remainder_monotone X hBV]
    with ω hmono
  let R (t : ℝ≥0) : ℝ :=
    ((t : ℝ) * X.drift - X.X t ω) -
      (∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ t then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal
  refine ⟨R, ?_, hmono, ?_⟩
  · intro t
    rfl
  intro τ u hu n hstop a ha hderiv
  apply Finset.sum_nonpos
  intro i hi
  have hincr : 0 ≤ R (u (i + 1)) - R (u i) :=
    sub_nonneg.mpr (hmono (hu (Nat.le_succ (i : ℕ))))
  have hcoeff : 0 ≤ a i * deriv w (riskProcess X x D (u i) ω) :=
    mul_nonneg (ha i) (hderiv i)
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcoeff) hincr
