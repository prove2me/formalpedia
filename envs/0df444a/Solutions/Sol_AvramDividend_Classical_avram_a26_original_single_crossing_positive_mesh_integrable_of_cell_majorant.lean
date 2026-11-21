-- Prove2me | solution 1 for AvramDividend.Classical.avram_a26_original_single_crossing_positive_mesh_integrable_of_cell_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T10:06:29.779774+00:00
-- url     : https://prove2.me/submissions/30bf922c-99ff-4f28-96a7-2e93d2dbb44d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : Ω → Finset ℕ) (f : ℕ → Ω → ℝ)
    (B : Ω → ℝ)
    (hCard : ∀ᵐ ω ∂P, (S ω).card ≤ 1)
    (hB : ∀ᵐ ω ∂P, 0 ≤ B ω)
    (hBI : Integrable B P)
    (hCell : ∀ᵐ ω ∂P, ∀ i ∈ S ω,
      max (f i ω) 0 ≤ B ω)
    (hMeas : AEStronglyMeasurable
      (fun ω => ∑ i ∈ S ω, max (f i ω) 0) P) :
    Integrable (fun ω => ∑ i ∈ S ω, max (f i ω) 0) P  := by
  have hDom : ∀ᵐ ω ∂P,
      ‖∑ i ∈ S ω, max (f i ω) 0‖ ≤ B ω := by
    filter_upwards [hCard, hB, hCell] with ω hc hb hf
    have hNonneg : 0 ≤ ∑ i ∈ S ω, max (f i ω) 0 :=
      Finset.sum_nonneg (fun i hi => le_max_right _ _)
    rw [Real.norm_eq_abs, abs_of_nonneg hNonneg]
    have hCases : (S ω).card = 0 ∨ (S ω).card = 1 := by
      omega
    rcases hCases with hz | ho
    · have hempty : S ω = ∅ := Finset.card_eq_zero.mp hz
      simp [hempty, hb]
    · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp ho
      rw [hi]
      simpa using hf i (by simp [hi])
  exact Integrable.mono' hBI hMeas hDom
