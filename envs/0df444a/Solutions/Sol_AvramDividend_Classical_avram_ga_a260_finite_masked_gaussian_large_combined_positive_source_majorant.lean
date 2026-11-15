-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a260_finite_masked_gaussian_large_combined_positive_source_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:06:35.622475+00:00
-- url     : https://prove2.me/submissions/c40d9657-edfa-4071-b4a1-dbc8926398df

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a258_large_positive_combined_discounted_gaussian_source_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} (S : Finset ℕ)
    (A : ℕ → Ω → Prop) [∀ i, DecidablePred (A i)]
    (e0 e1 w0 w1 d h r z T : ℕ → Ω → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hCell : ∀ i ω, A i ω →
      0 ≤ e0 i ω ∧ e0 i ω ≤ 1 ∧
      0 ≤ e1 i ω ∧ e1 i ω ≤ 1 ∧
      0 ≤ T i ω ∧ |w0 i ω| ≤ B ∧
      |d i ω| ≤ B ∧ |h i ω| ≤ B ∧
      w1 i ω ≤ T i ω)
    (ω : Ω) :
    max (∑ i ∈ S, if A i ω then
      e1 i ω*(w1 i ω-w0 i ω) -
        e0 i ω*(d i ω*r i ω+h i ω/2*(z i ω)^2)
      else 0) 0 ≤
    ∑ i ∈ S, if A i ω then
      T i ω+B*(1+|r i ω|+(z i ω)^2/2)
      else 0 := by
  have hEach (i : ℕ) :
      (if A i ω then
        e1 i ω*(w1 i ω-w0 i ω) -
          e0 i ω*(d i ω*r i ω+h i ω/2*(z i ω)^2)
        else 0) ≤
      (if A i ω then
        T i ω+B*(1+|r i ω|+(z i ω)^2/2)
        else 0) := by
    by_cases hAi : A i ω
    · simp only [if_pos hAi]
      obtain ⟨h0,h01,h1,h11,hT,hw0,hd,hh,hw1⟩ :=
        hCell i ω hAi
      exact (le_max_left _ _).trans
        (avram_ga_a258_large_positive_combined_discounted_gaussian_source_envelope
          (e0 i ω) (e1 i ω) (w0 i ω) (w1 i ω)
          (d i ω) (h i ω) (r i ω) (z i ω) B (T i ω)
          h0 h01 h1 h11 hB hT hw0 hd hh hw1)
    · simp [hAi]
  have hUpper :
      (∑ i ∈ S, if A i ω then
        e1 i ω*(w1 i ω-w0 i ω) -
          e0 i ω*(d i ω*r i ω+h i ω/2*(z i ω)^2)
        else 0) ≤
      ∑ i ∈ S, if A i ω then
        T i ω+B*(1+|r i ω|+(z i ω)^2/2)
        else 0 := Finset.sum_le_sum (fun i hi => hEach i)
  have hPos : 0 ≤
      (∑ i ∈ S, if A i ω then
        T i ω+B*(1+|r i ω|+(z i ω)^2/2)
        else 0) := by
    apply Finset.sum_nonneg
    intro i hi
    by_cases hAi : A i ω
    · simp only [if_pos hAi]
      have hT := (hCell i ω hAi).2.2.2.2.1
      have hQ : 0 ≤ 1+|r i ω|+(z i ω)^2/2 := by positivity
      positivity
    · simp [hAi]
  exact max_le hUpper hPos
