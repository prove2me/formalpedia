-- Prove2me | solution 1 for FriendlyShadow.Gaussian.lemma_40
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:22:07.510807+00:00
-- url     : https://prove2.me/submissions/cb542234-a01e-43de-8c33-225427f4b289

import Mathlib

open MeasureTheory

set_option autoImplicit false

open MeasureTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : MemLp X 2 P) (τ : ℝ) (hτ : 0 ≤ τ)
    (hvar : ProbabilityTheory.variance X P = τ ^ 2) :
    (|∫ ω, X ω ∂P| + τ) / 2 * ∫ ω, |X ω| ∂P ≤ ∫ ω, X ω ^ 2 ∂P := by
  have h1 := ProbabilityTheory.variance_eq_sub hX
  have hA : MemLp (fun ω => |X ω|) 2 P := by
    simpa [Real.norm_eq_abs] using hX.norm
  have h2 := ProbabilityTheory.variance_eq_sub hA
  have h3 := ProbabilityTheory.variance_nonneg (fun ω => |X ω|) P
  have e1 : ∫ x, (X ^ 2) x ∂P = ∫ ω, X ω ^ 2 ∂P := by simp only [Pi.pow_apply]
  have e2 : ∫ x, ((fun ω => |X ω|) ^ 2) x ∂P = ∫ ω, X ω ^ 2 ∂P := by simp only [Pi.pow_apply, sq_abs]
  rw [e1] at h1
  rw [e2] at h2
  set S := ∫ ω, X ω ^ 2 ∂P
  set m := ∫ ω, X ω ∂P
  set b := ∫ ω, |X ω| ∂P
  have hb : 0 ≤ b := integral_nonneg (fun ω => abs_nonneg _)
  have hm2 : |m| ^ 2 = m ^ 2 := sq_abs m
  have hmn : 0 ≤ |m| := abs_nonneg m
  nlinarith [sq_nonneg (|m| - τ), sq_nonneg ((|m| + τ) / 2 - b)]
