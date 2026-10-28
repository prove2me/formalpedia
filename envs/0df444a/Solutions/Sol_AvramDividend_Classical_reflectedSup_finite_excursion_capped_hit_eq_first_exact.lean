-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_finite_excursion_capped_hit_eq_first_exact
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:44:41.18309+00:00
-- url     : https://prove2.me/submissions/d851db67-989d-4fe3-ac04-6a927724f1ad

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_reflectedSup_finite_excursion_first_exact_height_hit
import Theorems.Thm_AvramDividend_Classical_nnreal_sInf_union_cap_eq_of_early_member

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (ζ : ℝ≥0) (hζ : 0 < ζ)
    (hEnd : reflectedSup X ζ ω = 0)
    (x : ℝ) (hx : 0 < x)
    (hHeight : sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 ζ) = x) :
    sInf ((Icc (0 : ℝ≥0) ζ ∩
      (fun t : ℝ≥0 => reflectedSup X t ω) ⁻¹' Ici x) ∪ {ζ}) =
    sInf (Icc (0 : ℝ≥0) ζ ∩
      (fun t : ℝ≥0 => reflectedSup X t ω) ⁻¹' Ici x) := by
  obtain ⟨T, hT, -, hTζ, hTx, -⟩ :=
    reflectedSup_finite_excursion_first_exact_height_hit X ω ζ hζ hEnd x hx hHeight
  exact nnreal_sInf_union_cap_eq_of_early_member _ ζ
    ⟨T, ⟨⟨zero_le, hTζ.le⟩, by simp [hTx]⟩, hTζ.le⟩
