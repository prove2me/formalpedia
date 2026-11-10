-- Prove2me | solution 1 for AvramDividend.Classical.avram_gclose15_original_compact_strict_postpayment_uniform_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T18:16:08.081937+00:00
-- url     : https://prove2.me/submissions/11f91faf-6bba-49f3-b24e-5c25792a54a6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gclose15_original_negative_postpayment_usc
import Theorems.Thm_AvramDividend_Classical_usc_compact_prefix_sup_strictly_below_level

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Strict original postpayment solvency on a compact prefix gives a
uniformly positive reserve floor for that path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0)
    (hpos : ∀ s : ℝ≥0, s ≤ T →
      0 < x + X.X s ω - rightLimit D s ω) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ≥0, s ≤ T →
      δ ≤ x + X.X s ω - rightLimit D s ω := by
  let R : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
  let S : Set ℝ := (fun t : ℝ≥0 => -R t) '' Icc (0 : ℝ≥0) T
  have hNoHit : ∀ s : ℝ≥0, s ≤ T → -R s < 0 := by
    intro s hs
    dsimp [R]
    linarith [hpos s hs]
  have hUSC : UpperSemicontinuousOn
      (fun t : ℝ≥0 => -R t) (Icc 0 T) := by
    simpa only [R] using
      (avram_gclose15_original_negative_postpayment_usc X x D hD ω T)
  have hSup : sSup S < 0 := by
    exact usc_compact_prefix_sup_strictly_below_level
      (fun t => -R t) T 0 hUSC hNoHit
  have hBdd : BddAbove S := by
    refine ⟨0, ?_⟩
    rintro y ⟨s, hs, rfl⟩
    exact le_of_lt (hNoHit s hs.2)
  refine ⟨-sSup S, by linarith, ?_⟩
  intro s hs
  have hMem : -R s ∈ S :=
    ⟨s, ⟨zero_le, hs⟩, rfl⟩
  have hLe : -R s ≤ sSup S := le_csSup hBdd hMem
  dsimp [R] at hLe ⊢
  linarith
