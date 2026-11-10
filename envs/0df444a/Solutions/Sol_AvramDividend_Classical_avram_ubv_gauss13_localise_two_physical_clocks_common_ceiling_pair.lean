-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_localise_two_physical_clocks_common_ceiling_pair
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:33:58.158193+00:00
-- url     : https://prove2.me/submissions/9d2c7d90-9120-4d40-9e25-6e45e01d2b62

import Mathlib.Probability.Process.Stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓖 : Filtration ℕ mΩ)
    (τ ρ : Ω → ℝ≥0) (hτρ : ∀ ω, τ ω ≤ ρ ω)
    (ε : ℝ≥0) (hGap : ∀ ω, ρ ω ≤ τ ω + ε)
    (grid : ℕ → ℝ≥0) (hgrid : Monotone grid)
    (Kτ Kρ : Ω → ℕ)
    (hKτ : IsStoppingTime 𝓖 (fun ω => (Kτ ω : WithTop ℕ)))
    (hKρ : IsStoppingTime 𝓖 (fun ω => (Kρ ω : WithTop ℕ)))
    (δ : ℝ≥0)
    (hCeilτ : ∀ ω, τ ω ≤ grid (Kτ ω) ∧
      grid (Kτ ω) ≤ τ ω + δ)
    (hCeilρ : ∀ ω, ρ ω ≤ grid (Kρ ω) ∧
      grid (Kρ ω) ≤ ρ ω + δ) :
    IsStoppingTime 𝓖
      (fun ω => ((min (Kτ ω) (Kρ ω)) : WithTop ℕ)) ∧
    IsStoppingTime 𝓖
      (fun ω => ((max (Kτ ω) (Kρ ω)) : WithTop ℕ)) ∧
    (∀ ω, τ ω ≤ grid (min (Kτ ω) (Kρ ω)) ∧
      grid (min (Kτ ω) (Kρ ω)) ≤ τ ω + δ) ∧
    (∀ ω, ρ ω ≤ grid (max (Kτ ω) (Kρ ω)) ∧
      grid (max (Kτ ω) (Kρ ω)) ≤ ρ ω + δ) ∧
    (∀ ω, (grid (max (Kτ ω) (Kρ ω)) : ℝ) -
      (grid (min (Kτ ω) (Kρ ω)) : ℝ) ≤
        (ε : ℝ) + (δ : ℝ)) := by
  have hMinStop : IsStoppingTime 𝓖
      (fun ω => ((min (Kτ ω) (Kρ ω)) : WithTop ℕ)) := by
    simpa only [WithTop.coe_min] using hKτ.min hKρ
  have hMaxStop : IsStoppingTime 𝓖
      (fun ω => ((max (Kτ ω) (Kρ ω)) : WithTop ℕ)) := by
    simpa only [WithTop.coe_max] using hKτ.max hKρ
  have hMin (ω : Ω) :
      τ ω ≤ grid (min (Kτ ω) (Kρ ω)) ∧
      grid (min (Kτ ω) (Kρ ω)) ≤ τ ω + δ := by
    rcases le_total (Kτ ω) (Kρ ω) with h | h
    · simpa [min_eq_left h] using hCeilτ ω
    · have hEq : min (Kτ ω) (Kρ ω) = Kρ ω := min_eq_right h
      rw [hEq]
      refine ⟨(hτρ ω).trans (hCeilρ ω).1, ?_⟩
      exact (hgrid h).trans (hCeilτ ω).2
  have hMax (ω : Ω) :
      ρ ω ≤ grid (max (Kτ ω) (Kρ ω)) ∧
      grid (max (Kτ ω) (Kρ ω)) ≤ ρ ω + δ := by
    rcases le_total (Kτ ω) (Kρ ω) with h | h
    · simpa [max_eq_right h] using hCeilρ ω
    · have hEq : max (Kτ ω) (Kρ ω) = Kτ ω := max_eq_left h
      rw [hEq]
      refine ⟨(hCeilρ ω).1.trans (hgrid h), ?_⟩
      have hAdd : τ ω + δ ≤ ρ ω + δ := by
        simpa [add_comm] using (add_le_add_right (hτρ ω) δ)
      exact (hCeilτ ω).2.trans hAdd
  refine ⟨hMinStop, hMaxStop, hMin, hMax, ?_⟩
  intro ω
  have hTop : grid (max (Kτ ω) (Kρ ω)) ≤
      grid (min (Kτ ω) (Kρ ω)) + ε + δ := by
    calc
      grid (max (Kτ ω) (Kρ ω)) ≤ ρ ω + δ := (hMax ω).2
      _ ≤ τ ω + ε + δ := by
        simpa [add_comm, add_left_comm, add_assoc] using
          (add_le_add_right (hGap ω) δ)
      _ ≤ grid (min (Kτ ω) (Kρ ω)) + ε + δ := by
        gcongr
        exact (hMin ω).1
  have hTopReal : (grid (max (Kτ ω) (Kρ ω)) : ℝ) ≤
      (grid (min (Kτ ω) (Kρ ω)) : ℝ) +
        (ε : ℝ) + (δ : ℝ) := by
    exact_mod_cast hTop
  linarith
