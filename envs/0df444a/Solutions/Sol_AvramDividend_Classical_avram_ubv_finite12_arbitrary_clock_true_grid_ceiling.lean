-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite12_arbitrary_clock_true_grid_ceiling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T11:16:13.984221+00:00
-- url     : https://prove2.me/submissions/a7197547-325d-4b37-a9c2-582bc1846940

import Mathlib
import Mathlib.Data.Nat.Find
import Mathlib.Probability.Process.Stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal
noncomputable section

/-- A bounded original right-continuous stopping clock has a genuine
sampled-filtration upper stopping ceiling within one time mesh. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0)))
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (N : ℕ) (hN : ∀ ω, σ ω ≤ e N)
    (δ : ℝ≥0) (h0 : e 0 = 0)
    (hStep : ∀ i, e (i + 1) ≤ e i + δ)
    (𝓖 : Filtration ℕ mΩ)
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (e i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (he hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (e i) } : Filtration ℕ mΩ)) :
    ∃ K : Ω → ℕ,
      IsStoppingTime 𝓖 (fun ω => (K ω : WithTop ℕ)) ∧
      (∀ ω, (K ω : WithTop ℕ) ≤ (N : WithTop ℕ)) ∧
      (∀ ω, σ ω ≤ e (K ω) ∧ e (K ω) ≤ σ ω + δ) := by
  classical
  let cover : ∀ ω, ∃ j : ℕ, σ ω ≤ e j := fun ω => ⟨N, hN ω⟩
  let K : Ω → ℕ := fun ω =>
    @Nat.find (fun j : ℕ => σ ω ≤ e j)
      (Classical.decPred (fun j : ℕ => σ ω ≤ e j)) (cover ω)
  have hKiff (ω : Ω) (i : ℕ) : K ω ≤ i ↔ σ ω ≤ e i := by
    constructor
    · intro hi
      exact (Nat.find_spec (cover ω)).trans (he hi)
    · intro hi
      exact (Nat.find_le_iff (cover ω) i).2 ⟨i, le_rfl, hi⟩
  refine ⟨K, ?_, ?_, ?_⟩
  · intro i
    have hFil : 𝓖 i = 𝓕.rightCont (e i) := by rw [h𝓖]
    have hevent : MeasurableSet[𝓖 i] {ω : Ω | K ω ≤ i} := by
      rw [hFil]
      have hs : {ω : Ω | K ω ≤ i} = {ω : Ω | σ ω ≤ e i} := by
        ext ω
        exact hKiff ω i
      rw [hs]
      simpa only [WithTop.coe_le_coe] using hσ (e i)
    simpa using hevent
  · intro ω
    exact_mod_cast (hKiff ω N).2 (hN ω)
  · intro ω
    have hlower : σ ω ≤ e (K ω) := Nat.find_spec (cover ω)
    refine ⟨hlower, ?_⟩
    cases hIndex : K ω with
    | zero =>
        simp [hIndex, h0]
    | succ i =>
        have hi : i < K ω := by
          simpa [hIndex] using Nat.lt_succ_self i
        have hnot : ¬ σ ω ≤ e i := Nat.find_min (cover ω) hi
        have hprev : e i ≤ σ ω := le_of_lt (lt_of_not_ge hnot)
        have hs : e (i + 1) ≤ e i + δ := hStep i
        have hz : e (i + 1) ≤ σ ω + δ :=
          hs.trans (add_le_add hprev (le_refl δ))
        simpa [hIndex, Nat.succ_eq_add_one] using hz
