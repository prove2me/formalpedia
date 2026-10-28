-- Prove2me | solution 3 for AvramDividend.Classical.reflectedSup_finite_excursion_height_level_null_under_P_of_regular
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T00:04:38.50531+00:00
-- url     : https://prove2.me/submissions/3ef2d5c4-b3bc-4e24-b8f1-aa31afe3e73a

import Mathlib.MeasureTheory.OuterMeasure.AE
import Theorems.Thm_AvramDividend_Classical_reflectedSup_finite_excursion_capped_first_hit_geometry
import Theorems.Thm_AvramDividend_Classical_reflectedSup_capped_firstClosedHit_posthit_negative_of_regular_source
import Theorems.Thm_AvramDividend_Classical_reflectedSup_height_level_null_of_ae_posthit_negative
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0) (hH : 0 < H)
    (Height : Ω → ℝ≥0) (x : ℝ≥0) (hx : 0 < x)
    (hHeight : ∀ ω : Ω, Height ω = x →
      reflectedSup X H ω = 0 ∧
      sSup ((fun u : ℝ≥0 => reflectedSup X u ω) '' Icc 0 H) = (x : ℝ))
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε → ∃ n : ℕ, horizons n ≤ ε)
    (hRegular : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0) :
    P {ω : Ω | Height ω = x} = 0 := by
  have hPost :=
    reflectedSup_capped_firstClosedHit_posthit_negative_of_regular_source
      X H (x : ℝ) times horizons hdense hpos hcofinal hRegular
  apply reflectedSup_height_level_null_of_ae_posthit_negative
    X P
    (fun ω : Ω => sInf ((Icc (0 : ℝ≥0) H ∩
      (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici (x : ℝ)) ∪ {H}))
    (fun _ => H) Height x
  · intro ω hLevel
    obtain ⟨hEnd, hSup⟩ := hHeight ω hLevel
    have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
    exact reflectedSup_finite_excursion_capped_first_hit_geometry
      X ω H hH hEnd (x : ℝ) hxR hSup
  · filter_upwards [hPost] with ω hω
    intro _ ε hε
    obtain ⟨s, hs, hneg⟩ := hω ε hε
    exact ⟨s, hs, sub_neg.mp hneg⟩
