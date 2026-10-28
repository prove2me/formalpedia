-- Prove2me | solution 2 for AvramDividend.Classical.reflectedSup_finite_horizon_max_no_positive_atom_below_terminal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:56:14.53748+00:00
-- url     : https://prove2.me/submissions/4804f48f-df7e-4531-884a-ffaa51abc0ea

import Mathlib.MeasureTheory.OuterMeasure.AE
import Theorems.Thm_AvramDividend_Classical_reflectedSup_terminal_below_max_capped_first_hit_geometry
import Theorems.Thm_AvramDividend_Classical_reflectedSup_capped_firstClosedHit_posthit_negative_of_regular_source
import Theorems.Thm_AvramDividend_Classical_reflectedSup_exceeds_hit_height_of_negative_posthit
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
    (H : ℝ≥0) (x : ℝ≥0) (hx : 0 < x)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε → ∃ n : ℕ, horizons n ≤ ε)
    (hRegular : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0) :
    P {ω : Ω |
      sSup ((fun u : ℝ≥0 => reflectedSup X u ω) '' Icc 0 H) = (x : ℝ) ∧
      reflectedSup X H ω < (x : ℝ)} = 0 := by
  have hPost :=
    reflectedSup_capped_firstClosedHit_posthit_negative_of_regular_source
      X H (x : ℝ) times horizons hdense hpos hcofinal hRegular
  have hNo : ∀ᵐ ω ∂P,
      ¬ (sSup ((fun u : ℝ≥0 => reflectedSup X u ω) '' Icc 0 H) = (x : ℝ) ∧
        reflectedSup X H ω < (x : ℝ)) := by
    filter_upwards [hPost] with ω hω
    rintro ⟨hMax, hEnd⟩
    have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
    obtain ⟨hT, hAt, hBelow⟩ :=
      reflectedSup_terminal_below_max_capped_first_hit_geometry
        X ω H (x : ℝ) hxR hMax hEnd
    have hNeg : ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, s < ε ∧
          X.X (sInf ((Icc (0 : ℝ≥0) H ∩
          (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici (x : ℝ)) ∪ {H}) + s) ω < X.X (sInf ((Icc (0 : ℝ≥0) H ∩
          (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici (x : ℝ)) ∪ {H})) ω := by
      intro ε hε
      obtain ⟨s, hs, hsub⟩ := hω ε hε
      exact ⟨s, hs, sub_neg.mp hsub⟩
    obtain ⟨u, _, huH, hAbove⟩ :=
      reflectedSup_exceeds_hit_height_of_negative_posthit
        X ω (sInf ((Icc (0 : ℝ≥0) H ∩
          (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici (x : ℝ)) ∪ {H})) H x hT hAt hNeg
    exact (not_lt_of_ge (hBelow u huH.le)) hAbove
  simpa only [not_not] using (ae_iff.mp hNo)
