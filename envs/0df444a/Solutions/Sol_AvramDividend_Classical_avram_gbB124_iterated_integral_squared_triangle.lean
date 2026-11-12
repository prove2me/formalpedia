-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB124_iterated_integral_squared_triangle
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:30:58.962195+00:00
-- url     : https://prove2.me/submissions/a7a2aab5-865d-4376-a542-129ee7ca6f41

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
noncomputable section

theorem solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    (f g h : α → β → ℝ)
    (hfgIn : ∀ a, Integrable
      (fun b => (f a b - g a b) ^ 2) ν)
    (hfhIn : ∀ a, Integrable
      (fun b => (f a b - h a b) ^ 2) ν)
    (hhgIn : ∀ a, Integrable
      (fun b => (h a b - g a b) ^ 2) ν)
    (hfgOut : Integrable
      (fun a => ∫ b, (f a b - g a b) ^ 2 ∂ν) μ)
    (hfhOut : Integrable
      (fun a => ∫ b, (f a b - h a b) ^ 2 ∂ν) μ)
    (hhgOut : Integrable
      (fun a => ∫ b, (h a b - g a b) ^ 2 ∂ν) μ) :
    (∫ a, (∫ b, (f a b - g a b) ^ 2 ∂ν) ∂μ) ≤
      2 * ((∫ a, (∫ b, (f a b - h a b) ^ 2 ∂ν) ∂μ) +
        (∫ a, (∫ b, (h a b - g a b) ^ 2 ∂ν) ∂μ)) := by
  have hInner (a : α) :
      (∫ b, (f a b - g a b) ^ 2 ∂ν) ≤
        2 * ((∫ b, (f a b - h a b) ^ 2 ∂ν) +
          (∫ b, (h a b - g a b) ^ 2 ∂ν)) := by
    have hPt (b : β) :
        (f a b - g a b) ^ 2 ≤
          2 * ((f a b - h a b) ^ 2 +
            (h a b - g a b) ^ 2) := by
      nlinarith [sq_nonneg ((f a b - h a b) +
        (g a b - h a b))]
    calc
      _ ≤ ∫ b, 2 * ((f a b - h a b) ^ 2 +
            (h a b - g a b) ^ 2) ∂ν :=
        integral_mono (hfgIn a)
          (((hfhIn a).add (hhgIn a)).const_mul 2) hPt
      _ = 2 * ((∫ b, (f a b - h a b) ^ 2 ∂ν) +
          (∫ b, (h a b - g a b) ^ 2 ∂ν)) := by
        rw [integral_const_mul,
          integral_add (hfhIn a) (hhgIn a)]
  calc
    _ ≤ ∫ a, 2 * ((∫ b, (f a b - h a b) ^ 2 ∂ν) +
          (∫ b, (h a b - g a b) ^ 2 ∂ν)) ∂μ :=
      integral_mono hfgOut
        ((hfhOut.add hhgOut).const_mul 2) hInner
    _ = 2 * ((∫ a, (∫ b, (f a b - h a b) ^ 2 ∂ν) ∂μ) +
          (∫ a, (∫ b, (h a b - g a b) ^ 2 ∂ν) ∂μ)) := by
      rw [integral_const_mul, integral_add hfhOut hhgOut]
