-- Prove2me | solution 2 for AvramDividend.Classical.bv_esscher_explicit_geometric_laplace_ac
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:26:27.116809+00:00
-- url     : https://prove2.me/submissions/e7bb989a-280d-42d3-a55a-bb7e09e199b5

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_root_discounted_tail_kernel_ac_package
import Theorems.Thm_AvramDividend_Classical_geometric_renewal_explicit_powers_laplace_ac
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
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
                ENNReal.ofReal (Real.exp (-s * z)) ∂κ))⁻¹)) := by
  obtain ⟨hδ, -⟩ := AvramDividend.Classical.bv_standing_drift_pos X hX hbv
  obtain ⟨κ, hsf, hac, hsupp, hgap, hlap⟩ :=
    AvramDividend.Classical.bv_root_discounted_tail_kernel_ac_package X hbv q hq φ hφ hroot hδ
  haveI := hsf
  obtain ⟨m, β, h1⟩ := AvramDividend.Classical.geometric_renewal_explicit_powers_laplace_ac κ hsupp hac
    (ENNReal.ofReal X.drift) (ENNReal.ofReal_pos.2 hδ) ENNReal.ofReal_ne_top hgap
  exact ⟨κ, m, β, hsf, hac, hsupp, hgap, hlap, h1⟩
