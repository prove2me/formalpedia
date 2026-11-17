-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB32_capped_original_lower_hit_strict_pre_floor
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T21:07:57.809309+00:00
-- url     : https://prove2.me/submissions/2bd08d99-4b61-4778-b9e8-a10db2931220

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem AvramDividend.Classical.avram_gbB32_capped_original_lower_hit_strict_pre_floor
    {Ω : Type*} (U : ℝ≥0 → Ω → ℝ)
    (H : ℝ≥0) (b : ℝ) (ω : Ω) (t : ℝ≥0)
    (ht : t < sInf ((Icc (0 : ℝ≥0) H ∩
      (fun u : ℝ≥0 => -(U u ω)) ⁻¹' Ici (-b)) ∪ {H})) :
    b < U t ω := by
  by_contra hcon
  push Not at hcon
  have hbdd : BddBelow ((Icc (0 : ℝ≥0) H ∩
      (fun u : ℝ≥0 => -(U u ω)) ⁻¹' Ici (-b)) ∪ {H}) := OrderBot.bddBelow _
  have htH : t ≤ H := by
    have := csInf_le hbdd (Or.inr rfl : H ∈ ((Icc (0 : ℝ≥0) H ∩
      (fun u : ℝ≥0 => -(U u ω)) ⁻¹' Ici (-b)) ∪ {H}))
    exact (lt_of_lt_of_le ht this).le
  have hmem : t ∈ ((Icc (0 : ℝ≥0) H ∩
      (fun u : ℝ≥0 => -(U u ω)) ⁻¹' Ici (-b)) ∪ {H}) := by
    left
    refine ⟨⟨bot_le, htH⟩, ?_⟩
    simp only [mem_preimage, mem_Ici]
    linarith
  exact absurd (csInf_le hbdd hmem) (not_le.mpr ht)

theorem solution
    {Ω : Type*} (U : ℝ≥0 → Ω → ℝ)
    (H : ℝ≥0) (b : ℝ) (ω : Ω) (t : ℝ≥0)
    (ht : t < sInf ((Icc (0 : ℝ≥0) H ∩
      (fun u : ℝ≥0 => -(U u ω)) ⁻¹' Ici (-b)) ∪ {H})) :
    b < U t ω :=
  AvramDividend.Classical.avram_gbB32_capped_original_lower_hit_strict_pre_floor U H b ω t ht
