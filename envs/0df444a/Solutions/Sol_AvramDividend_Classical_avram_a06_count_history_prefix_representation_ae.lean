-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_count_history_prefix_representation_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:00:23.27553+00:00
-- url     : https://prove2.me/submissions/62ec45c3-827f-4735-8b94-80054a05258d

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Theorems.Thm_AvramDividend_Classical_chat06_history_comap_prefix_representation
import Theorems.Thm_AvramDividend_Classical_chat06_prefix_observed_count_history_measurable
import Theorems.Thm_AvramDividend_Classical_chat06_arrival_prefix_reconstructs_past_count
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

/-- A single joint full-measure threshold event suffices for finite-prefix history reconstruction. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (τ Z : Ω → ℕ → ℝ) (N : Ω → ℝ → ℕ)
    (clock : ℝ) (n : ℕ)
    (hThresholdAE : ∀ᵐ ω ∂P, ∀ u k,
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
    filter_upwards [hThresholdAE] with ω hThreshold
    intro hn
    funext s
    have hs : (s : ℝ) ≤ clock := s.property
    exact (AvramDividend.Classical.chat06_arrival_prefix_reconstructs_past_count
      (τ ω) (Z ω) (N ω) clock (s : ℝ) hs n hn
      hThreshold (hZ ω)).symm
  exact AvramDividend.Classical.chat06_history_comap_prefix_representation
    P (fun ω => N ω clock) n Z
    (fun ω => fun s : Set.Iic clock => N ω (s : ℝ))
    φ hφ hPath H hH
