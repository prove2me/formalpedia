-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_generic_original_chronological_pairs_monotone_grid_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T12:46:11.136128+00:00
-- url     : https://prove2.me/submissions/603252e1-6572-4096-b7f1-b72ddc3ad4cf

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (F : Ω → Finset ℝ≥0)
    (G : ℕ → Ω → Finset (ℝ≥0 × ℝ≥0))
    (hSub : ∀ m ω, G m ω ⊆
      (F ω ×ˢ F ω).filter (fun p => p.1 < p.2))
    (hMono : ∀ m k, m ≤ k → ∀ ω, G m ω ⊆ G k ω)
    (hStop : ∀ ω, ∃ N, ∀ m ≥ N,
      G m ω = (F ω ×ˢ F ω).filter (fun p => p.1 < p.2))
    (hMeas : ∀ m, Measurable
      (fun ω => ((G m ω).card : ℝ≥0∞)))
    (A : ℕ → ℝ≥0∞)
    (hMean : ∀ m, (∫⁻ ω, ((G m ω).card : ℝ≥0∞) ∂P) = A m) :
    (∫⁻ ω, (((F ω ×ˢ F ω).filter
      (fun p => p.1 < p.2)).card : ℝ≥0∞) ∂P) =
      ⨆ m, A m := by
  classical
  let R : Ω → Finset (ℝ≥0 × ℝ≥0) := fun ω =>
    (F ω ×ˢ F ω).filter (fun p => p.1 < p.2)
  have hCountMono :
      Monotone (fun m : ℕ => fun ω : Ω =>
        ((G m ω).card : ℝ≥0∞)) := by
    intro m k hmk ω
    exact Nat.cast_le.mpr (Finset.card_le_card (hMono m k hmk ω))
  have hSup (ω : Ω) :
      (⨆ m, ((G m ω).card : ℝ≥0∞)) =
        ((R ω).card : ℝ≥0∞) := by
    apply le_antisymm
    · apply iSup_le
      intro m
      exact Nat.cast_le.mpr (Finset.card_le_card (hSub m ω))
    · obtain ⟨N, hN⟩ := hStop ω
      calc
        ((R ω).card : ℝ≥0∞) =
            ((G N ω).card : ℝ≥0∞) := by
              rw [hN N le_rfl]
        _ ≤ ⨆ m, ((G m ω).card : ℝ≥0∞) :=
          le_iSup (fun m => ((G m ω).card : ℝ≥0∞)) N
  calc
    (∫⁻ ω, ((R ω).card : ℝ≥0∞) ∂P) =
        (∫⁻ ω, ⨆ m, ((G m ω).card : ℝ≥0∞) ∂P) := by
          congr 1
          funext ω
          exact (hSup ω).symm
    _ = ⨆ m, (∫⁻ ω, ((G m ω).card : ℝ≥0∞) ∂P) :=
          lintegral_iSup hMeas hCountMono
    _ = ⨆ m, A m := by
          congr 1
          funext m
          exact hMean m
