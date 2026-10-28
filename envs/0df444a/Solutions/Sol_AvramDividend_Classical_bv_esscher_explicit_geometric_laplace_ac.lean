-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_explicit_geometric_laplace_ac
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:26:15.519478+00:00
-- url     : https://prove2.me/submissions/0ea10184-ae6c-47ee-8951-a92818f37aa4

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_root_discounted_tail_kernel_ac_package
import Theorems.Thm_AvramDividend_Classical_geometric_renewal_explicit_powers_laplace_ac
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Expose the discounted BV Esscher kernel and its complete geometric renewal witness. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (φ : ℝ) (hφ : 0 < φ)
    (hroot : X.ψ φ = q) :
    ∃ (κ : Measure ℝ) (m : ℕ → Measure ℝ) (β : Measure ℝ),
      SFinite κ ∧ κ ≪ volume ∧ κ (Iio (0 : ℝ)) = 0 ∧
      κ Set.univ < ENNReal.ofReal X.drift ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂κ) =
        (∫⁻ z : ℝ≥0,
          ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) *
            ENNReal.ofReal
              ((1 - Real.exp (-(s * (z : ℝ)))) / s)
            ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y))))) ∧
      m 0 = Measure.dirac (0 : ℝ) ∧
      (∀ n : ℕ, m (n + 1) = κ.conv (m n)) ∧
      (∀ n : ℕ, SFinite (m n)) ∧
      β = Measure.sum (fun n : ℕ =>
        (ENNReal.ofReal X.drift)⁻¹ ^ (n + 1) • m n) ∧
      0 < β Set.univ ∧ β Set.univ ≠ ⊤ ∧
      β (Iio (0 : ℝ)) = 0 ∧
      β.restrict (Ioi (0 : ℝ)) ≪ (volume : Measure ℝ) ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ x : ℝ in Ioi 0,
          ENNReal.ofReal (Real.exp (-s * x)) * β (Iic x)) =
        ENNReal.ofReal (1 / s) *
          ((ENNReal.ofReal X.drift)⁻¹ *
            (1 - (ENNReal.ofReal X.drift)⁻¹ *
              (∫⁻ z : ℝ,
                ENNReal.ofReal (Real.exp (-s * z)) ∂κ))⁻¹))  := by
  have hδ : 0 < X.drift := (bv_standing_drift_pos X hX hbv).1
  obtain ⟨κ, hκsf, hκac, hκsupp, hκmass, hκLap⟩ :=
    bv_root_discounted_tail_kernel_ac_package X hbv q hq φ hφ hroot hδ
  letI : SFinite κ := hκsf
  obtain ⟨m, β, hm0, hmsucc, hsf, hβeq, hβpos, hβfin,
      hβsupp, hβac, hβlocal, hβLap⟩ :=
    geometric_renewal_explicit_powers_laplace_ac
      κ hκsupp hκac (ENNReal.ofReal X.drift)
      (ENNReal.ofReal_pos.mpr hδ) ENNReal.ofReal_ne_top hκmass
  exact ⟨κ, m, β, hκsf, hκac, hκsupp, hκmass, hκLap,
    hm0, hmsucc, hsf, hβeq, hβpos, hβfin,
    hβsupp, hβac, hβlocal, hβLap⟩
