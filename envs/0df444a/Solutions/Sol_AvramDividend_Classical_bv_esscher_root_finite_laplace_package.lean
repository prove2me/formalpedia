-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_root_finite_laplace_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T19:19:42.942284+00:00
-- url     : https://prove2.me/submissions/04a1385f-fdf6-4f83-98c5-287c067bb15b

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_root_discounted_tail_kernel_package
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_laplace_denominator_identity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_lintegral
import Theorems.Thm_AvramDividend_Classical_bv_esscher_discounted_jump_product_integrable
import Theorems.Thm_AvramDividend_Classical_positive_finite_supported_geometric_renewal_uniform
import Theorems.Thm_AvramDividend_Classical_esscher_root_real_positive_geometric_factor
import Theorems.Thm_AvramDividend_Classical_positive_cumulative_laplace_real_integral_bridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-!
Exact bounded-variation Esscher-root finite-Laplace package, using
the remotely Proved noncircular kernel, renewal and integral bridges.
-/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (φ : ℝ) (hφ : 0 < φ)
    (hroot : X.ψ φ = q) :
    ∃ (β : Measure ℝ) (b : ℝ),
      0 < β Set.univ ∧ β Set.univ ≠ ⊤ ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ θ : ℝ, b < θ →
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (Real.exp (-(φ * x)) * W x)) (Ioi 0) ∧
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (β (Iic x)).toReal) (Ioi 0) ∧
        (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
          (Real.exp (-(φ * x)) * W x)) =
        (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
          (β (Iic x)).toReal)) := by
  have hδ : 0 < X.drift := (bv_standing_drift_pos X hX hbv).1
  obtain ⟨κ, hκsf, hκsupp, hκmass, hκLap⟩ :=
    bv_root_discounted_tail_kernel_package X hbv q hq φ hφ hroot hδ
  letI : SFinite κ := hκsf
  let δe : ℝ≥0∞ := ENNReal.ofReal X.drift
  obtain ⟨β, hβpos, hβfin, hβsupp, hβlocal, hβLap⟩ :=
    positive_finite_supported_geometric_renewal_uniform κ hκsupp δe
      (ENNReal.ofReal_pos.mpr hδ) ENNReal.ofReal_ne_top hκmass
  let μ : Measure ℝ≥0 := X.ν.map (fun y : ℝ => Real.toNNReal (-y))
  let b : ℝ := max 0 (1 - φ)
  refine ⟨β, b, hβpos, hβfin, hβlocal, ?_⟩
  intro θ hθ
  have hθpos : 0 < θ := lt_of_le_of_lt (le_max_left _ _) hθ
  have hθplus : 0 ≤ φ + θ := by linarith
  have hθsum : 0 ≤ θ + φ := by linarith
  have hJint := bv_esscher_discounted_jump_product_integrable
    X hbv φ θ hφ.le hθpos.le
  let r : ℝ≥0∞ := ∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-θ * z)) ∂κ
  have hr : r = ∫⁻ z : ℝ≥0,
      ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) *
        ENNReal.ofReal ((1 - Real.exp (-(θ * (z : ℝ)))) / θ) ∂μ :=
    by simpa only [r, neg_mul] using (hκLap θ hθpos)
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
  have hKgap : r < δe := lt_of_le_of_lt hKle hκmass
  have hdiff := bv_esscher_root_laplace_denominator_identity
    X hbv q hq φ θ hφ hθpos hroot
  have hsc := esscher_root_real_positive_geometric_factor
    μ φ X.drift θ q (X.ψ (φ + θ)) hδ hθpos hJint hdiff r hr hKgap
  have hψ : q < X.ψ (θ + φ) := by simpa [add_comm] using hsc.1
  let fs : ℝ → ℝ := fun x =>
    Real.exp (-θ * x) * (Real.exp (-(φ * x)) * W x)
  let gs : ℝ → ℝ := fun x => Real.exp (-((θ + φ) * x)) * W x
  have hfsgs : fs = gs := by
    funext x
    dsimp [fs, gs]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hfsInt : IntegrableOn fs (Ioi (0 : ℝ)) := by
    rw [hfsgs]
    exact (hW.2.2.2.2 (θ + φ) hθsum hψ).1
  have hfsPos : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fs := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hWx : 0 ≤ W x := hW.2.1 x (le_of_lt hx)
    dsimp [fs]
    positivity
  have hscale := scaleFunction_tilted_positive_lintegral
    X q W hW θ φ hθsum hψ
  have hscale' : (∫⁻ x : ℝ in Ioi 0, ENNReal.ofReal (fs x)) =
      ENNReal.ofReal ((X.ψ (θ + φ) - q)⁻¹) := by
    simpa only [fs, neg_mul] using hscale
  have hβEq := hβLap θ hθpos
  have hlin : (∫⁻ x : ℝ in Ioi 0, ENNReal.ofReal (fs x)) =
      (∫⁻ x : ℝ in Ioi 0,
        ENNReal.ofReal (Real.exp (-θ * x)) * β (Iic x)) := by
    calc
      _ = ENNReal.ofReal ((X.ψ (θ + φ) - q)⁻¹) := hscale'
      _ = ENNReal.ofReal (1 / θ) *
            (δe⁻¹ * (1 - δe⁻¹ * r)⁻¹) := by
              simpa only [δe, add_comm] using hsc.2.symm
      _ = _ := by simpa only [r] using hβEq.symm
  obtain ⟨hgbInt, hRealEq⟩ :=
    positive_cumulative_laplace_real_integral_bridge
      β hβlocal θ fs hfsInt hfsPos hlin
  exact ⟨by simpa [fs] using hfsInt, hgbInt,
    by simpa [fs] using hRealEq⟩
