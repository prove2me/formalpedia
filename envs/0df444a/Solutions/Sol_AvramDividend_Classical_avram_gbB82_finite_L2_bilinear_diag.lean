-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB82_finite_L2_bilinear_diag
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:25:05.095212+00:00
-- url     : https://prove2.me/submissions/c5e3b6ec-52f3-49c0-b110-5092fe2c7085

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (N : ℕ)
    (A B : ℕ → Ω → ℝ)
    (hA : ∀ i, MemLp (A i) 2 P)
    (hB : ∀ i, MemLp (B i) 2 P)
    (hCross : ∀ i j, i ≠ j → (∫ ω, A i ω * B j ω ∂P) = 0) :
    (∫ ω, ((Finset.range N).sum (fun i => A i ω)) *
      ((Finset.range N).sum (fun i => B i ω)) ∂P) =
    (Finset.range N).sum (fun i => ∫ ω, A i ω * B i ω ∂P) := by
  have hPair (i j : ℕ) :
      Integrable (fun ω => A i ω * B j ω) P :=
    (hA i).integrable_mul (hB j)
  have hInner (i : ℕ) :
      Integrable (fun ω =>
        (Finset.range N).sum (fun j => A i ω * B j ω)) P :=
    integrable_finset_sum (Finset.range N) (by
      intro j hj
      exact hPair i j)
  calc
    (∫ ω, ((Finset.range N).sum (fun i => A i ω)) *
      ((Finset.range N).sum (fun j => B j ω)) ∂P) =
      (∫ ω, (Finset.range N).sum (fun i =>
        (Finset.range N).sum (fun j => A i ω * B j ω)) ∂P) := by
          apply integral_congr_ae
          filter_upwards with ω
          rw [Finset.sum_mul]
          simp_rw [Finset.mul_sum]
    _ = (Finset.range N).sum (fun i =>
          (Finset.range N).sum (fun j =>
            ∫ ω, A i ω * B j ω ∂P)) := by
          rw [integral_finset_sum (Finset.range N) (by
            intro i hi
            exact hInner i)]
          apply Finset.sum_congr rfl
          intro i hi
          rw [integral_finset_sum (Finset.range N) (by
            intro j hj
            exact hPair i j)]
    _ = (Finset.range N).sum (fun i =>
          ∫ ω, A i ω * B i ω ∂P) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_eq_single i
          · intro j hj hji
            exact hCross i j (Ne.symm hji)
          · intro hn
            exact (hn hi).elim
