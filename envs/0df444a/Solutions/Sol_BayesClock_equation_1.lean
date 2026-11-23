-- Prove2me | solution 1 for BayesClock.equation_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T00:13:01.250107+00:00
-- url     : https://prove2.me/submissions/734f1b9a-4679-4da7-ae0b-ff7f593de98d

import Mathlib
import Definitions.Def_BayesClock_IsDownwardClosed
import Definitions.Def_BayesClock_maximalSets
import Definitions.Def_BayesClock_OPT
import Definitions.Def_BayesClock_LowHighTerms

set_option autoImplicit false

open MeasureTheory BayesClock
open scoped NNReal ENNReal

namespace BayesClock.Eq1Proof

theorem exists_maximal {N : Type*} [DecidableEq N] (𝓕 : Finset (Finset N)) {F : Finset N}
    (hF : F ∈ 𝓕) : ∃ S ∈ maximalSets 𝓕, F ⊆ S := by
  classical
  have hne : (𝓕.filter (fun S => F ⊆ S)).Nonempty := ⟨F, Finset.mem_filter.mpr ⟨hF, le_rfl⟩⟩
  obtain ⟨S, hSA, hmax⟩ := Finset.exists_max_image _ Finset.card hne
  rw [Finset.mem_filter] at hSA
  refine ⟨S, ?_, hSA.2⟩
  unfold maximalSets
  rw [Finset.mem_filter]
  refine ⟨hSA.1, ?_⟩
  rintro ⟨F', hF', hSF'⟩
  have h1 := hmax F' (Finset.mem_filter.mpr ⟨hF', hSA.2.trans hSF'.subset⟩)
  have h2 := Finset.card_lt_card hSF'
  omega

end BayesClock.Eq1Proof

open BayesClock.Eq1Proof in
theorem solution {N : Type*} [Fintype N] [DecidableEq N] (𝓕 : Finset (Finset N))
    (h𝓕 : IsDownwardClosed 𝓕) (ν : N → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (ν i)]
    (t : Finset N → ℝ≥0) :
    OPT 𝓕 ν = ∫⁻ v, ⨆ S ∈ maximalSets 𝓕, ∑ i ∈ S, (v i : ℝ≥0∞) ∂Measure.pi ν ∧
      OPT 𝓕 ν ≤ LOW 𝓕 ν t + HIGH 𝓕 ν t := by
  have hpt : ∀ v : N → ℝ≥0, (⨆ F ∈ 𝓕, ∑ i ∈ F, (v i : ℝ≥0∞)) =
      ⨆ S ∈ maximalSets 𝓕, ∑ i ∈ S, (v i : ℝ≥0∞) := by
    intro v
    apply le_antisymm
    · apply iSup₂_le
      intro F hF
      obtain ⟨S, hS, hFS⟩ := exists_maximal 𝓕 hF
      exact (Finset.sum_le_sum_of_subset hFS).trans (le_iSup₂ (f := fun S _ =>
        ∑ i ∈ S, (v i : ℝ≥0∞)) S hS)
    · apply iSup₂_le
      intro S hS
      have hS' : S ∈ 𝓕 := (Finset.mem_filter.mp hS).1
      exact le_iSup₂ (f := fun F _ => ∑ i ∈ F, (v i : ℝ≥0∞)) S hS'
  have h1 : OPT 𝓕 ν = ∫⁻ v, ⨆ S ∈ maximalSets 𝓕, ∑ i ∈ S, (v i : ℝ≥0∞) ∂Measure.pi ν := by
    unfold OPT
    congr 1
    funext v
    exact hpt v
  refine ⟨h1, ?_⟩
  rw [h1]
  have hmeas : Measurable (fun v : N → ℝ≥0 =>
      ⨆ S ∈ maximalSets 𝓕, ∑ i ∈ S, ((min (v i) (t S) : ℝ≥0) : ℝ≥0∞)) := by
    apply Measurable.iSup
    intro S
    apply Measurable.iSup_Prop
    exact Finset.measurable_sum S (fun i _ =>
      ((measurable_pi_apply i).min measurable_const).coe_nnreal_ennreal)
  unfold LOW HIGH
  rw [← lintegral_add_left hmeas]
  apply lintegral_mono
  intro v
  apply iSup₂_le
  intro S hS
  calc ∑ i ∈ S, (v i : ℝ≥0∞)
      ≤ ∑ i ∈ S, (((min (v i) (t S) : ℝ≥0) : ℝ≥0∞) + (highPart (t S) (v i) : ℝ≥0∞)) := by
        apply Finset.sum_le_sum
        intro i _
        unfold highPart
        split_ifs with h
        · exact le_add_self
        · push Not at h
          rw [min_eq_left h]
          simp
    _ = ∑ i ∈ S, ((min (v i) (t S) : ℝ≥0) : ℝ≥0∞) + ∑ i ∈ S, (highPart (t S) (v i) : ℝ≥0∞) :=
        Finset.sum_add_distrib
    _ ≤ (⨆ S ∈ maximalSets 𝓕, ∑ i ∈ S, ((min (v i) (t S) : ℝ≥0) : ℝ≥0∞)) +
          ⨆ S ∈ maximalSets 𝓕, ∑ i ∈ S, (highPart (t S) (v i) : ℝ≥0∞) :=
        add_le_add (le_iSup₂ (f := fun S _ => ∑ i ∈ S, ((min (v i) (t S) : ℝ≥0) : ℝ≥0∞)) S hS)
          (le_iSup₂ (f := fun S _ => ∑ i ∈ S, (highPart (t S) (v i) : ℝ≥0∞)) S hS)
