-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_first_ceiling_clock_mesh_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:31:39.208866+00:00
-- url     : https://prove2.me/submissions/e68b597f-9cd6-4e2c-ad7f-4575b55816a6

import Mathlib
import Mathlib.Data.Nat.Find
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The first original ruin-clock grid ceiling overshoots by at most one time mesh. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (N : ℕ) (hN : ∀ ω, τ ω ≤ e N)
    (δ : ℝ≥0) (h0 : e 0 = 0)
    (hStep : ∀ i, e (i + 1) ≤ e i + δ) :
    let cover : ∀ ω, ∃ j : ℕ, τ ω ≤ e j := fun ω => ⟨N, hN ω⟩
    let K : Ω → ℕ := fun ω =>
      @Nat.find (fun j : ℕ => τ ω ≤ e j) (Classical.decPred (fun j : ℕ => τ ω ≤ e j)) (cover ω)
    ∀ ω, τ ω ≤ e (K ω) ∧ e (K ω) ≤ τ ω + δ := by
  classical
  let cover : ∀ ω, ∃ j : ℕ, τ ω ≤ e j := fun ω => ⟨N, hN ω⟩
  let K : Ω → ℕ := fun ω =>
    @Nat.find (fun j : ℕ => τ ω ≤ e j) (Classical.decPred (fun j : ℕ => τ ω ≤ e j)) (cover ω)
  change ∀ ω, τ ω ≤ e (K ω) ∧ e (K ω) ≤ τ ω + δ
  intro ω
  have hLower : τ ω ≤ e (K ω) := Nat.find_spec (cover ω)
  refine ⟨hLower, ?_⟩
  cases hIndex : K ω with
  | zero =>
      simp [hIndex, h0]
  | succ i =>
      have hi : i < K ω := by
        simpa [hIndex] using Nat.lt_succ_self i
      have hnot : ¬ τ ω ≤ e i := Nat.find_min (cover ω) hi
      have hl : e i ≤ τ ω := le_of_lt (lt_of_not_ge hnot)
      have hs : e (i + 1) ≤ e i + δ := hStep i
      have hz : e (i + 1) ≤ τ ω + δ :=
        hs.trans (add_le_add hl (le_refl δ))
      simpa [hIndex, Nat.succ_eq_add_one] using hz
