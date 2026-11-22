-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_root_esscher_denominator_identity_no_standing_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T04:58:07.206319+00:00
-- url     : https://prove2.me/submissions/3eafb7f2-2950-4354-921e-78d62611f5b5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_laplace_denominator_identity
import Theorems.Thm_AvramDividend_Classical_bv_esscher_discounted_jump_product_integrable
import Theorems.Thm_AvramDividend_Classical_esscher_root_real_positive_geometric_factor

open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (φ : ℝ) (hφ : 0 < φ)
    (hroot : X.ψ φ = q) (hδ : 0 < X.drift) (κ : Measure ℝ) (hκsf : SFinite κ)
    (hκsupp : κ (Iio (0 : ℝ)) = 0)
    (hκmass : κ Set.univ < ENNReal.ofReal X.drift)
    (hκLap : ∀ s : ℝ, 0 < s →
      (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-(s * z))) ∂κ) =
      (∫⁻ z : ℝ≥0, ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) *
        ENNReal.ofReal ((1 - Real.exp (-(s * (z : ℝ)))) / s)
        ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y))))) :
    ∀ θ : ℝ, max 0 (1 - φ) < θ →
      q < X.ψ (θ + φ) ∧
      ENNReal.ofReal ((X.ψ (θ + φ) - q)⁻¹) =
        ENNReal.ofReal (1 / θ) *
          ((ENNReal.ofReal X.drift)⁻¹ *
            (1 - (ENNReal.ofReal X.drift)⁻¹ *
              (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-θ * z)) ∂κ))⁻¹) := by
  haveI : SFinite κ := hκsf
  let μ : Measure ℝ≥0 := X.ν.map (fun y : ℝ => Real.toNNReal (-y))
  intro θ hθ
  have hθpos : 0 < θ := lt_of_le_of_lt (le_max_left _ _) hθ
  have hJint := bv_esscher_discounted_jump_product_integrable
    X hbv φ θ hφ.le hθpos.le
  let r : ℝ≥0∞ := ∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-θ * z)) ∂κ
  have hr : r = ∫⁻ z : ℝ≥0,
      ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) *
        ENNReal.ofReal ((1 - Real.exp (-(θ * (z : ℝ)))) / θ) ∂μ := by
    simpa only [r, neg_mul] using (hκLap θ hθpos)
  have hκset : κ {x : ℝ | ¬ 0 ≤ x} = 0 := by
    have hs : {x : ℝ | ¬ 0 ≤ x} = Iio (0 : ℝ) := by
      ext x
      simp
    rw [hs]
    exact hκsupp
  have hκae : ∀ᵐ x : ℝ ∂κ, 0 ≤ x := (ae_iff).2 hκset
  have hKle : r ≤ κ Set.univ := by
    dsimp [r]
    calc
      _ ≤ ∫⁻ z : ℝ, (1 : ℝ≥0∞) ∂κ := by
        apply lintegral_mono_ae
        filter_upwards [hκae] with z hz
        apply ENNReal.ofReal_le_one.mpr
        exact Real.exp_le_one_iff.mpr (by nlinarith)
      _ = κ Set.univ := by simp
  have hKgap : r < ENNReal.ofReal X.drift := lt_of_le_of_lt hKle hκmass
  have hdiff := bv_esscher_root_laplace_denominator_identity
    X hbv q hq φ θ hφ hθpos hroot
  have hsc := esscher_root_real_positive_geometric_factor
    μ φ X.drift θ q (X.ψ (φ + θ)) hδ hθpos hJint hdiff r hr hKgap
  have hψ : q < X.ψ (θ + φ) := by simpa [add_comm] using hsc.1
  exact ⟨hψ, by simpa only [r, add_comm] using hsc.2.symm⟩
