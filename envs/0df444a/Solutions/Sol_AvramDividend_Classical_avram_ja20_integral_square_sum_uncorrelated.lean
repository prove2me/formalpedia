-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja20_integral_square_sum_uncorrelated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:59:39.0091+00:00
-- url     : https://prove2.me/submissions/3a0c9c62-401c-4007-98f6-7456cc08eef9

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (G J : Ω → ℝ) (a b : ℝ)
    (hGsq : Integrable (fun ω => (G ω) ^ 2) P)
    (hJsq : Integrable (fun ω => (J ω) ^ 2) P)
    (hGJ : Integrable (fun ω => G ω * J ω) P)
    (hcross : (∫ ω, G ω * J ω ∂P) = 0)
    (hGa : (∫ ω, (G ω) ^ 2 ∂P) = a)
    (hJb : (∫ ω, (J ω) ^ 2 ∂P) = b) :
    (∫ ω, (G ω + J ω) ^ 2 ∂P) = a + b := by
  have hfun : (fun ω => (G ω + J ω) ^ 2) =
      (fun ω => (G ω) ^ 2 + (J ω) ^ 2 + 2 * (G ω * J ω)) := by
    funext ω
    ring
  rw [hfun]
  have hOuter :
      (∫ ω, (G ω) ^ 2 + (J ω) ^ 2 + 2 * (G ω * J ω) ∂P) =
      (∫ ω, (G ω) ^ 2 + (J ω) ^ 2 ∂P) +
      (∫ ω, 2 * (G ω * J ω) ∂P) := by
    exact integral_add (hGsq.add hJsq) (hGJ.const_mul 2)
  have hInner :
      (∫ ω, (G ω) ^ 2 + (J ω) ^ 2 ∂P) =
      (∫ ω, (G ω) ^ 2 ∂P) + (∫ ω, (J ω) ^ 2 ∂P) := by
    exact integral_add hGsq hJsq
  calc
    (∫ ω, (G ω) ^ 2 + (J ω) ^ 2 + 2 * (G ω * J ω) ∂P) =
        (∫ ω, (G ω) ^ 2 + (J ω) ^ 2 ∂P) +
        (∫ ω, 2 * (G ω * J ω) ∂P) := hOuter
    _ = (∫ ω, (G ω) ^ 2 ∂P) +
        (∫ ω, (J ω) ^ 2 ∂P) +
        2 * (∫ ω, G ω * J ω ∂P) := by
          rw [hInner, integral_const_mul]
    _ = a + b := by
          rw [hGa, hJb, hcross]
          ring
