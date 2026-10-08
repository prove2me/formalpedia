-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_tilted_positive_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T10:10:11.179414+00:00
-- url     : https://prove2.me/submissions/9ddc19e4-bcca-4d4b-be80-5988ee61ee07

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (s φ : ℝ) (hθ0 : 0 ≤ s + φ) (hψ : q < X.ψ (s + φ)) :
    (∫⁻ x : ℝ in Ioi 0,
      ENNReal.ofReal
        (Real.exp (-s * x) * (Real.exp (-φ * x) * W x))) =
      ENNReal.ofReal ((X.ψ (s + φ) - q)⁻¹) := by
  let f : ℝ → ℝ :=
    fun x => Real.exp (-s * x) * (Real.exp (-φ * x) * W x)
  let g : ℝ → ℝ := fun x => Real.exp (-((s + φ) * x)) * W x
  have hfg : f = g := by
    funext x
    dsimp [f, g]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hLap := hW.2.2.2.2 (s + φ) hθ0 hψ
  obtain ⟨hgInt, hgVal⟩ := hLap
  have hfInt : IntegrableOn f (Ioi (0 : ℝ)) := by
    rw [hfg]
    exact hgInt
  have hfPos :
      0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hWx : 0 ≤ W x := hW.2.1 x (le_of_lt hx)
    dsimp [f]
    positivity
  have hOf :=
    ofReal_integral_eq_lintegral_ofReal hfInt hfPos
  have hfVal :
      ∫ x in Ioi (0 : ℝ), f x = (X.ψ (s + φ) - q)⁻¹ := by
    rw [hfg]
    exact hgVal
  rw [← hOf, hfVal]
