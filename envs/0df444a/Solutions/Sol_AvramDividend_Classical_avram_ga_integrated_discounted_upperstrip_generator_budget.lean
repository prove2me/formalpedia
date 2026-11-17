-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_integrated_discounted_upperstrip_generator_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T12:40:53.996298+00:00
-- url     : https://prove2.me/submissions/b54e51ec-a28a-4d8c-9594-71f2224ea492

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
theorem solution
    (S : Set ℝ) (q b c : ℝ) (Y G : ℝ → ℝ)
    (hGenI : Integrable (fun t => Real.exp (-(q * t)) * G t)
       (volume.restrict S))
    (hOccI : Integrable (fun t => if b < Y t then (1 : ℝ) else 0)
       (volume.restrict S))
    (hHJB : ∀ᵐ t ∂(volume.restrict S),
       Real.exp (-(q * t)) * G t ≤
         if b < Y t then max c 0 else 0) :
    (∫ t in S, Real.exp (-(q * t)) * G t ∂volume) ≤
      max c 0 * (∫ t in S,
        if b < Y t then (1 : ℝ) else 0 ∂volume) := by
  have hUpperI : Integrable (fun t => max c 0 *
      (if b < Y t then (1 : ℝ) else 0)) (volume.restrict S) :=
    hOccI.const_mul (max c 0)
  have hPoint : ∀ᵐ t ∂(volume.restrict S),
      Real.exp (-(q * t)) * G t ≤
        max c 0 * (if b < Y t then (1 : ℝ) else 0) := by
    filter_upwards [hHJB] with t ht
    simpa only [mul_ite, mul_one, mul_zero] using ht
  calc
    _ ≤ ∫ t in S, max c 0 *
        (if b < Y t then (1 : ℝ) else 0) ∂volume :=
      integral_mono_ae hGenI hUpperI hPoint
    _ = _ := by simp only [integral_const_mul]
