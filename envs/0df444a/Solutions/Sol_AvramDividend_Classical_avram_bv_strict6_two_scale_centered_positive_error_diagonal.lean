-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict6_two_scale_centered_positive_error_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:02:36.247701+00:00
-- url     : https://prove2.me/submissions/317f40bd-d4f1-4072-bd82-8bc70c3b737a

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
noncomputable section

/-- Select spatial localisations along the physical time grid while preserving centred
compensated source terms and vanishing expected positive errors. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F B : ℕ → Ω → ℝ) (c : ℝ)
    (M Err : ℕ → ℕ → Ω → ℝ) (η : ℕ → ℝ)
    (hηpos : ∀ n, 0 < η n)
    (hηzero : Tendsto η atTop (nhds (0 : ℝ)))
    (hM : ∀ n k, Integrable (M n k) P ∧
      (∫ ω, M n k ω ∂P) = 0)
    (hErr : ∀ n k,
      Integrable (fun ω => max (Err n k ω) 0) P)
    (hApprox : ∀ n (ε : ℝ), 0 < ε →
      ∃ k,
        (∫ ω, max (Err n k ω) 0 ∂P) ≤ η n + ε ∧
        (∀ᵐ ω ∂P, F n ω ≤
          c + (M n k ω + B n ω) + max (Err n k ω) 0)) :
    ∃ M' Err' : ℕ → Ω → ℝ,
      (∀ n, Integrable (M' n) P ∧
        (∫ ω, M' n ω ∂P) = 0) ∧
      (∀ n, Integrable (fun ω => max (Err' n ω) 0) P) ∧
      Tendsto (fun n => ∫ ω, max (Err' n ω) 0 ∂P)
        atTop (nhds (0 : ℝ)) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F n ω ≤ c + (M' n ω + B n ω) + max (Err' n ω) 0) := by
  classical
  have hPick (n : ℕ) :
      ∃ k,
        (∫ ω, max (Err n k ω) 0 ∂P) ≤ η n + η n ∧
        (∀ᵐ ω ∂P, F n ω ≤
          c + (M n k ω + B n ω) + max (Err n k ω) 0) :=
    hApprox n (η n) (hηpos n)
  let k : ℕ → ℕ := fun n => Classical.choose (hPick n)
  have hk (n : ℕ) :
      (∫ ω, max (Err n (k n) ω) 0 ∂P) ≤ η n + η n ∧
      (∀ᵐ ω ∂P, F n ω ≤
        c + (M n (k n) ω + B n ω) +
          max (Err n (k n) ω) 0) :=
    Classical.choose_spec (hPick n)
  refine ⟨(fun n ω => M n (k n) ω),
    (fun n ω => Err n (k n) ω), ?_, ?_, ?_, ?_⟩
  · intro n
    exact hM n (k n)
  · intro n
    exact hErr n (k n)
  · have hlo : (fun _ : ℕ => (0 : ℝ)) ≤
        (fun n => ∫ ω, max (Err n (k n) ω) 0 ∂P) := by
      intro n
      exact integral_nonneg (fun ω => le_max_right (Err n (k n) ω) 0)
    have hhi :
        (fun n => ∫ ω, max (Err n (k n) ω) 0 ∂P) ≤
        (fun n => 2 * η n) := by
      intro n
      calc
        (∫ ω, max (Err n (k n) ω) 0 ∂P) ≤ η n + η n := (hk n).1
        _ = 2 * η n := by ring
    have htop : Tendsto (fun n => (2 : ℝ) * η n)
        atTop (nhds (0 : ℝ)) := by
      convert tendsto_const_nhds.mul hηzero using 1 <;> simp
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds htop hlo hhi
  · intro n
    exact (hk n).2
