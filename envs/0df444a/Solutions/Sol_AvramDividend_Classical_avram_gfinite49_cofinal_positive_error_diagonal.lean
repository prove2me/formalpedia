-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite49_cofinal_positive_error_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T18:04:05.009369+00:00
-- url     : https://prove2.me/submissions/a6dfdae0-6ea4-4c85-8317-306ace22e19e

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (F : Ω → ℝ) (a : ℝ) (M : ℕ → ℕ → Ω → ℝ)
    (theta eps : ℕ → ℝ)
    (hTheta : Tendsto theta atTop (𝓝 (0 : ℝ)))
    (hEps : Tendsto eps atTop (𝓝 (0 : ℝ)))
    (hLocal : ∀ j K : ℕ, ∃ m : ℕ, K < m ∧
      ∃ E : Ω → ℝ,
        IntegrableOn E A P ∧
        (∀ᵐ ω ∂(P.restrict A), F ω ≤ a + M j m ω + E ω) ∧
        (∫ ω in A, max (E ω) 0 ∂P) ≤ theta j + eps j) :
    ∃ N : ℕ → ℕ, StrictMono N ∧
      ∃ E : ℕ → Ω → ℝ,
        (∀ j, IntegrableOn (E j) A P) ∧
        Tendsto (fun j => ∫ ω in A, max (E j ω) 0 ∂P)
          atTop (𝓝 (0 : ℝ)) ∧
        (∀ j, ∀ᵐ ω ∂(P.restrict A),
          F ω ≤ a + M j (N j) ω + E j ω) := by
  classical
  let pickN (j K : ℕ) : ℕ := Classical.choose (hLocal j K)
  let pickE (j K : ℕ) : Ω → ℝ :=
    Classical.choose ((Classical.choose_spec (hLocal j K)).2)
  let R : ℕ → ℕ × (Ω → ℝ) :=
    Nat.rec (pickN 0 0, pickE 0 0)
      (fun j p => (pickN (j + 1) p.1, pickE (j + 1) p.1))
  let N : ℕ → ℕ := fun j => (R j).1
  let E : ℕ → Ω → ℝ := fun j => (R j).2
  have hMono : StrictMono N := strictMono_nat_of_lt_succ (fun j => by
    change (R j).1 < pickN (j + 1) (R j).1
    exact (Classical.choose_spec (hLocal (j + 1) (R j).1)).1)
  have hEInt (j : ℕ) : IntegrableOn (E j) A P := by
    cases j with
    | zero =>
        simpa [R, E] using
          (Classical.choose_spec ((Classical.choose_spec (hLocal 0 0)).2)).1
    | succ j =>
        simpa [R, E] using
          (Classical.choose_spec
            ((Classical.choose_spec (hLocal (j + 1) (R j).1)).2)).1
  have hUpper (j : ℕ) :
      ∀ᵐ ω ∂(P.restrict A), F ω ≤ a + M j (N j) ω + E j ω := by
    cases j with
    | zero =>
        simpa [R, E, N] using
          (Classical.choose_spec ((Classical.choose_spec (hLocal 0 0)).2)).2.1
    | succ j =>
        simpa [R, E, N] using
          (Classical.choose_spec
            ((Classical.choose_spec (hLocal (j + 1) (R j).1)).2)).2.1
  have hBound (j : ℕ) :
      (∫ ω in A, max (E j ω) 0 ∂P) ≤ theta j + eps j := by
    cases j with
    | zero =>
        simpa [R, E] using
          (Classical.choose_spec ((Classical.choose_spec (hLocal 0 0)).2)).2.2
    | succ j =>
        simpa [R, E] using
          (Classical.choose_spec
            ((Classical.choose_spec (hLocal (j + 1) (R j).1)).2)).2.2
  have hSum : Tendsto (fun j => theta j + eps j) atTop (𝓝 (0 : ℝ)) := by
    simpa using hTheta.add hEps
  have hMean : Tendsto
      (fun j => ∫ ω in A, max (E j ω) 0 ∂P) atTop (𝓝 (0 : ℝ)) := by
    apply Filter.Tendsto.squeeze tendsto_const_nhds hSum
    · intro j
      exact integral_nonneg (fun ω => le_max_right _ _)
    · exact hBound
  exact ⟨N, hMono, E, hEInt, hMean, hUpper⟩
