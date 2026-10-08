-- Prove2me | solution 1 for AvramDividend.Classical.bv_geometric_factor_scale_denominator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T09:58:34.95053+00:00
-- url     : https://prove2.me/submissions/832d0448-7b70-4853-945c-6ad16d09b5ed

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_laplace_exponent_positive_magnitude_exact
import Theorems.Thm_AvramDividend_Classical_bv_positive_magnitude_exponential_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hbv : X.BoundedVariation) (s : ℝ) (hs : 0 < s)
    (hθ : 1 ≤ s + q / X.drift)
    (hgap : (∫⁻ z : ℝ≥0, ENNReal.ofReal
      ((1 - Real.exp (-(s + q / X.drift) * (z : ℝ))) / s)
      ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))) < ENNReal.ofReal X.drift) :
    q < X.ψ (s + q / X.drift) ∧
      ENNReal.ofReal (1 / s) * ((ENNReal.ofReal X.drift)⁻¹ *
        (1 - (ENNReal.ofReal X.drift)⁻¹ * (∫⁻ z : ℝ≥0, ENNReal.ofReal
          ((1 - Real.exp (-(s + q / X.drift) * (z : ℝ))) / s)
          ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))))⁻¹) =
        ENNReal.ofReal ((X.ψ (s + q / X.drift) - q)⁻¹) := by
  have hδ : 0 < X.drift := (bv_standing_drift_pos X hX hbv).1
  let θ : ℝ := s + q / X.drift
  let μ : Measure ℝ≥0 := X.ν.map (fun y : ℝ => Real.toNNReal (-y))
  let f : ℝ≥0 → ℝ := fun z => 1 - Real.exp (-θ * (z : ℝ))
  have hfInt : Integrable f μ := by
    simpa [f, μ, θ] using bv_positive_magnitude_exponential_integrable X hbv θ hθ
  have hfPos : 0 ≤ᵐ[μ] f := by
    filter_upwards with z
    have hz : 0 ≤ (z : ℝ) := z.2
    have harg : -θ * (z : ℝ) ≤ 0 := by
      have : 0 ≤ θ := le_trans zero_le_one hθ
      nlinarith
    dsimp [f]
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr harg)
  let J : ℝ := ∫ z : ℝ≥0, f z ∂μ
  have hJ0 : 0 ≤ J := integral_nonneg_of_ae hfPos
  have hgInt : Integrable (fun z : ℝ≥0 => f z / s) μ := hfInt.div_const s
  have hgPos : 0 ≤ᵐ[μ] fun z : ℝ≥0 => f z / s := by
    filter_upwards [hfPos] with z hz
    exact div_nonneg hz hs.le
  have hK : (∫⁻ z : ℝ≥0, ENNReal.ofReal (f z / s) ∂μ) =
      ENNReal.ofReal (J / s) := by
    have h := ofReal_integral_eq_lintegral_ofReal hgInt hgPos
    rw [integral_div] at h
    exact h.symm
  have hgapReal : J / s < X.drift := by
    apply (ENNReal.ofReal_lt_ofReal_iff hδ).mp
    rw [← hK]
    simpa [f, μ, θ] using hgap
  have hJlt : J < X.drift * s := (div_lt_iff₀ hs).mp hgapReal
  have hψ0 : X.ψ θ = X.drift * θ - J := by
    simpa [J, f, μ] using bv_laplace_exponent_positive_magnitude_exact X hbv θ hθ
  have hδφ : X.drift * (q / X.drift) = q := by field_simp [ne_of_gt hδ]
  have hdiff : X.ψ θ - q = X.drift * s - J := by
    rw [hψ0]
    dsimp [θ]
    rw [mul_add, hδφ]
    ring
  have hdiffPos : 0 < X.ψ θ - q := by rw [hdiff]; exact sub_pos.mpr hJlt
  have hψ : q < X.ψ θ := sub_pos.mp hdiffPos
  let k : ℝ := J / s
  have hk0 : 0 ≤ k := div_nonneg hJ0 hs.le
  have hdinv0 : 0 ≤ X.drift⁻¹ := (inv_pos.mpr hδ).le
  have hratio : X.drift⁻¹ * k < 1 := by
    have hdv : k / X.drift < 1 := (div_lt_one hδ).2 hgapReal
    simpa [div_eq_mul_inv, mul_comm] using hdv
  have hden : 0 < 1 - X.drift⁻¹ * k := sub_pos.mpr hratio
  have hdsj : 0 < X.drift * s - J := sub_pos.mpr hJlt
  have hreal : (1 / s) * (X.drift⁻¹ * (1 - X.drift⁻¹ * k)⁻¹) =
      (X.drift * s - J)⁻¹ := by
    dsimp [k]
    field_simp [ne_of_gt hs, ne_of_gt hδ, ne_of_gt hden, ne_of_gt hdsj] <;> ring
  have hcE : (ENNReal.ofReal X.drift)⁻¹ = ENNReal.ofReal X.drift⁻¹ :=
    (ENNReal.ofReal_inv_of_pos hδ).symm
  have hpE : (ENNReal.ofReal X.drift)⁻¹ * ENNReal.ofReal k =
      ENNReal.ofReal (X.drift⁻¹ * k) := by
    rw [hcE]
    exact (ENNReal.ofReal_mul hdinv0).symm
  have hsE : 1 - (ENNReal.ofReal X.drift)⁻¹ * ENNReal.ofReal k =
      ENNReal.ofReal (1 - X.drift⁻¹ * k) := by
    rw [hpE]
    simpa using (ENNReal.ofReal_sub (1 : ℝ) (mul_nonneg hdinv0 hk0)).symm
  have hiE : (1 - (ENNReal.ofReal X.drift)⁻¹ * ENNReal.ofReal k)⁻¹ =
      ENNReal.ofReal (1 - X.drift⁻¹ * k)⁻¹ := by
    rw [hsE]
    exact (ENNReal.ofReal_inv_of_pos hden).symm
  have hinnE : (ENNReal.ofReal X.drift)⁻¹ *
      (1 - (ENNReal.ofReal X.drift)⁻¹ * ENNReal.ofReal k)⁻¹ =
      ENNReal.ofReal (X.drift⁻¹ * (1 - X.drift⁻¹ * k)⁻¹) := by
    rw [hiE, hcE]
    exact (ENNReal.ofReal_mul hdinv0).symm
  have hallE : ENNReal.ofReal (1 / s) * ((ENNReal.ofReal X.drift)⁻¹ *
      (1 - (ENNReal.ofReal X.drift)⁻¹ * ENNReal.ofReal k)⁻¹) =
      ENNReal.ofReal ((1 / s) * (X.drift⁻¹ * (1 - X.drift⁻¹ * k)⁻¹)) := by
    rw [hinnE]
    exact (ENNReal.ofReal_mul (one_div_pos.mpr hs).le).symm
  refine ⟨by simpa [θ] using hψ, ?_⟩
  rw [show (∫⁻ z : ℝ≥0, ENNReal.ofReal
      ((1 - Real.exp (-(s + q / X.drift) * (z : ℝ))) / s) ∂
      (X.ν.map (fun y : ℝ => Real.toNNReal (-y)))) = ENNReal.ofReal k by
        simpa [k, f, μ, θ] using hK]
  rw [hallE, hreal]
  simpa [θ] using congrArg ENNReal.ofReal (congrArg Inv.inv hdiff.symm)
