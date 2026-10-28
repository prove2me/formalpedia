-- Prove2me | solution 1 for AvramDividend.Classical.finite_reflected_excursion_height_level_null_of_posthit_negative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T20:48:24.274549+00:00
-- url     : https://prove2.me/submissions/cef3458f-5fed-448b-bd6b-6a52f89d297e

import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_reflectedSup_finite_excursion_first_exact_height_hit
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc
import Theorems.Thm_AvramDividend_Classical_reflectedSup_height_level_null_of_ae_posthit_negative
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : Measure Ω) (ζ H : Ω → ℝ≥0) (x : ℝ≥0)
    (hx : 0 < x)
    (hFinite : ∀ ω : Ω, H ω = x →
      0 < ζ ω ∧
      reflectedSup X (ζ ω) ω = 0 ∧
      sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 (ζ ω)) = (x : ℝ))
    (hNeg : ∀ᵐ ω ∂n,
      sInf (Icc (0 : ℝ≥0) (ζ ω) ∩
        (fun t : ℝ≥0 => reflectedSup X t ω) ⁻¹' Ici (x : ℝ)) < ζ ω →
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, s < ε ∧
          X.X (sInf (Icc (0 : ℝ≥0) (ζ ω) ∩
            (fun t : ℝ≥0 => reflectedSup X t ω) ⁻¹' Ici (x : ℝ)) + s) ω <
          X.X (sInf (Icc (0 : ℝ≥0) (ζ ω) ∩
            (fun t : ℝ≥0 => reflectedSup X t ω) ⁻¹' Ici (x : ℝ))) ω) :
    n {ω : Ω | H ω = x} = 0 := by
  let T : Ω → ℝ≥0 := fun ω =>
    sInf (Icc (0 : ℝ≥0) (ζ ω) ∩
      (fun t : ℝ≥0 => reflectedSup X t ω) ⁻¹' Ici (x : ℝ))
  apply reflectedSup_height_level_null_of_ae_posthit_negative X n T ζ H x
  · intro ω hH
    obtain ⟨hζ, hEnd, hSup⟩ := hFinite ω hH
    have hxReal : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
    obtain ⟨t, htDef, htPos, htLt, htHit, _⟩ :=
      reflectedSup_finite_excursion_first_exact_height_hit
        X ω (ζ ω) hζ hEnd (x : ℝ) hxReal hSup
    have hT : T ω = t := htDef.symm
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hT] using htLt
    · simpa only [hT] using htHit
    · intro s hs hsζ
      have hUSC : UpperSemicontinuousOn
          (fun u : ℝ≥0 => reflectedSup X u ω) (Icc 0 (ζ ω)) :=
        reflectedSup_upperSemicontinuousOn_Icc X ω (ζ ω)
      have hbdd : BddAbove
          ((fun u : ℝ≥0 => reflectedSup X u ω) '' Icc 0 (ζ ω)) :=
        UpperSemicontinuousOn.bddAbove_of_isCompact isCompact_Icc hUSC
      have hle : reflectedSup X s ω ≤
          sSup ((fun u : ℝ≥0 => reflectedSup X u ω) '' Icc 0 (ζ ω)) :=
        le_csSup hbdd ⟨s, ⟨(show (0 : ℝ≥0) ≤ s from zero_le), le_of_lt hsζ⟩, rfl⟩
      simpa only [hSup] using hle
  · exact hNeg
