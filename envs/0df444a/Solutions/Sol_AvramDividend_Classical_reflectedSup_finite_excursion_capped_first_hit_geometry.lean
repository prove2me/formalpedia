-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_finite_excursion_capped_first_hit_geometry
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:55:23.125999+00:00
-- url     : https://prove2.me/submissions/d665d64e-0096-42cb-bcf5-3d9ff5a6d5e8

import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_reflectedSup_finite_excursion_capped_hit_eq_first_exact
import Theorems.Thm_AvramDividend_Classical_reflectedSup_finite_excursion_first_exact_height_hit
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (H : ℝ≥0) (hH : 0 < H)
    (hEnd : reflectedSup X H ω = 0)
    (x : ℝ) (hx : 0 < x)
    (hHeight : sSup ((fun u : ℝ≥0 => reflectedSup X u ω) '' Icc 0 H) = x) :
    sInf ((Icc (0 : ℝ≥0) H ∩
      (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H}) < H ∧
    reflectedSup X (sInf ((Icc (0 : ℝ≥0) H ∩
      (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H})) ω = x ∧
    ∀ t : ℝ≥0, sInf ((Icc (0 : ℝ≥0) H ∩
      (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H}) ≤ t →
      t < H → reflectedSup X t ω ≤ x := by
  rw [reflectedSup_finite_excursion_capped_hit_eq_first_exact X ω H hH hEnd x hx hHeight]
  obtain ⟨T, hT, -, hTH, hTx, -⟩ :=
    reflectedSup_finite_excursion_first_exact_height_hit X ω H hH hEnd x hx hHeight
  rw [← hT]
  refine ⟨hTH, hTx, fun t _ htH => ?_⟩
  have hb : BddAbove ((fun u : ℝ≥0 => reflectedSup X u ω) '' Icc 0 H) := by
    by_contra hnb
    rw [Real.sSup_of_not_bddAbove hnb] at hHeight
    linarith
  rw [← hHeight]
  exact le_csSup hb ⟨t, ⟨zero_le, htH.le⟩, rfl⟩
