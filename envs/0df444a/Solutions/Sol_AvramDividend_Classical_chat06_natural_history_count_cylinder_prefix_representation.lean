-- Prove2me | solution 1 for AvramDividend.Classical.chat06_natural_history_count_cylinder_prefix_representation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T07:48:20.965149+00:00
-- url     : https://prove2.me/submissions/53a2f6a2-c2f7-4059-aed1-42ac25aa04a6

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Theorems.Thm_AvramDividend_Classical_chat06_history_comap_prefix_representation
import Theorems.Thm_AvramDividend_Classical_chat06_prefix_observed_count_history_measurable
import Theorems.Thm_AvramDividend_Classical_chat06_arrival_prefix_reconstructs_past_count

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- On a fixed renewal-count cylinder, every measurable event of the
complete observed counting history is determined by the finite
interarrival prefix. The renewal threshold identity supplies the
pathwise factorisation, including all real times up to the horizon. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (τ Z : Ω → ℕ → ℝ) (N : Ω → ℝ → ℕ)
    (clock : ℝ) (n : ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔
        (∑ i ∈ Finset.range (k + 1), τ ω i) ≤ u)
    (hZ : ∀ ω i, Z ω i = if i < n then τ ω i else 0)
    (H : Set Ω)
    (hH : MeasurableSet[
      MeasurableSpace.comap
        (fun ω : Ω => fun s : Set.Iic clock => N ω (s : ℝ))
        (inferInstance : MeasurableSpace (Set.Iic clock → ℕ))] H) :
    ∃ Q : Set (ℕ → ℝ), MeasurableSet Q ∧
      (fun ω : Ω => ω ∈ H ∧ N ω clock = n) =ᵐ[P]
        (fun ω : Ω => Z ω ∈ Q ∧ N ω clock = n) := by
  classical
  let φ : (ℕ → ℝ) → (Set.Iic clock → ℕ) :=
    fun z s => ((Finset.range n).filter (fun k =>
      (∑ i ∈ Finset.range (k + 1), z i) ≤ (s : ℝ))).card
  have hφ : Measurable φ :=
    AvramDividend.Classical.chat06_prefix_observed_count_history_measurable n clock
  have hPath : ∀ᵐ ω ∂P, N ω clock = n →
      (fun s : Set.Iic clock => N ω (s : ℝ)) = φ (Z ω) := by
    filter_upwards [] with ω
    intro hn
    funext s
    have hs : (s : ℝ) ≤ clock := s.property
    exact (AvramDividend.Classical.chat06_arrival_prefix_reconstructs_past_count
      (τ ω) (Z ω) (N ω) clock (s : ℝ) hs n hn
      (hThreshold ω) (hZ ω)).symm
  exact AvramDividend.Classical.chat06_history_comap_prefix_representation
    P (fun ω => N ω clock) n Z
    (fun ω => fun s : Set.Iic clock => N ω (s : ℝ))
    φ hφ hPath H hH
