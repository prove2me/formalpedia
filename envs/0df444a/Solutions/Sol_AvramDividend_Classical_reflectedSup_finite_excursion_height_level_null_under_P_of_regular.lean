-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_finite_excursion_height_level_null_under_P_of_regular
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:04:19.636999+00:00
-- url     : https://prove2.me/submissions/dfb83974-c5a6-41da-b0ca-1f6f9edacaad

import Mathlib.MeasureTheory.OuterMeasure.AE
import Theorems.Thm_AvramDividend_Classical_reflectedSup_finite_excursion_capped_first_hit_geometry
import Theorems.Thm_AvramDividend_Classical_reflectedSup_capped_firstClosedHit_posthit_negative_of_regular_source
import Theorems.Thm_AvramDividend_Classical_reflectedSup_height_level_null_of_ae_posthit_negative

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
  have hx' : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  refine reflectedSup_height_level_null_of_ae_posthit_negative X P
    (fun ω => sInf ((Icc (0 : ℝ≥0) H ∩
      (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici (x : ℝ)) ∪ {H})) (fun _ => H) Height x
    (fun ω hω => ?_) ?_
  · obtain ⟨hE, hS⟩ := hHeight ω hω
    exact reflectedSup_finite_excursion_capped_first_hit_geometry X ω H hH hE (x : ℝ) hx' hS
  · filter_upwards [reflectedSup_capped_firstClosedHit_posthit_negative_of_regular_source X H (x : ℝ)
      times horizons hdense hpos hcofinal hRegular] with ω h _ ε hε
    obtain ⟨s, hs, h'⟩ := h ε hε
    exact ⟨s, hs, by linarith⟩
