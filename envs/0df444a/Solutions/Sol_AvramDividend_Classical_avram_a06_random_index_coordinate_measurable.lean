-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_random_index_coordinate_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:27:33.931033+00:00
-- url     : https://prove2.me/submissions/30bb2678-4e79-4dfa-971a-833fbeadd0ab

import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

/-- A measurable natural-valued selector of measurable random coordinates
    retains measurability on the original probability space. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ n, Measurable (τ n))
    (K : Ω → ℕ) (hK : Measurable K) :
    Measurable (fun ω => τ (K ω) ω) := by
  classical
  have hPiece (n : ℕ) :
      Measurable (fun ω => if n = K ω then τ n ω else (0 : ℝ)) := by
    have hs : MeasurableSet {ω | n = K ω} := by
      simpa [Set.preimage, eq_comm] using
        ((measurableSet_singleton n).preimage hK)
    exact (hτ n).ite hs measurable_const
  have hSum :
      Measurable (fun ω => ∑' n : ℕ,
        if n = K ω then τ n ω else (0 : ℝ)) :=
    Measurable.tsum hPiece
  convert hSum using 1
  funext ω
  exact (tsum_ite_eq (K ω) (fun n : ℕ => τ n ω)).symm
