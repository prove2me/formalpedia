-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb35_original_finitecap_BV_closedband_physical_grid_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:16:51.119031+00:00
-- url     : https://prove2.me/submissions/269819f5-c661-4e91-beca-ccd83613be9b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb34_original_finitecap_BV_allclosed_physical_generator_sign
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hStanding : X.Standing)
    (hBV : X.BoundedVariation) (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hwCont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwSmooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i ≤ n → u n i ≤ u n (i + 1))
    (hReserve : ∀ i : ℕ, i ≤ n →
      let z := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      0 ≤ z ∧ z ≤ C.toReal) :
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    (∑ i ∈ Finset.range (n + 1),
      Real.exp (-(q * (u n i : ℝ))) *
        (X.drift * (if Z i = 0 ∨ Z i = C.toReal then 1 else deriv w (Z i)) +
          (∫ z in Iio (0 : ℝ), w (Z i + z) - w (Z i) ∂X.ν) -
          q * w (Z i)) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))) ≤ 0  := by
  let Z : ℕ → ℝ := fun i => Function.leftLim
    (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
  have hSource :=
    avram_bvb34_original_finitecap_BV_allclosed_physical_generator_sign
      X hStanding hBV hActivity q w C hC hFinite
      hwCont hw0 hwNeg hwSmooth hwGen hwGrad
  dsimp only
  apply Finset.sum_nonpos
  intro i hi
  have hiN : i ≤ n := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
  obtain ⟨h0, hC'⟩ := hReserve i hiN
  have hGenLe :=
    hSource (Z i) h0 hC'
  have hStep : 0 ≤ (u n (i + 1) : ℝ) - (u n i : ℝ) :=
    sub_nonneg.mpr (by exact_mod_cast hGrid i hiN)
  have hWeight : 0 ≤ Real.exp (-(q * (u n i : ℝ))) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ)) :=
    mul_nonneg (Real.exp_nonneg _) hStep
  calc
    Real.exp (-(q * (u n i : ℝ))) *
        (X.drift *
          (if Z i = 0 ∨ Z i = C.toReal then 1 else deriv w (Z i)) +
            (∫ z in Iio (0 : ℝ), w (Z i + z) - w (Z i) ∂X.ν) -
            q * w (Z i)) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ)) =
        (Real.exp (-(q * (u n i : ℝ))) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))) *
        (X.drift *
          (if Z i = 0 ∨ Z i = C.toReal then 1 else deriv w (Z i)) +
            (∫ z in Iio (0 : ℝ), w (Z i + z) - w (Z i) ∂X.ν) -
            q * w (Z i)) := by ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hWeight hGenLe
