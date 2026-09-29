-- Prove2me | solution 1 for FamousTheorems.aas_congruence_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:26:48.607897+00:00
-- url     : https://prove2.me/submissions/c115a167-6e2c-4954-a04f-9045c6303e92

import Mathlib

open EuclideanGeometry

theorem solution {V₁ V₂ P₁ P₂ : Type*} [NormedAddCommGroup V₁] [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₁]
    [InnerProductSpace ℝ V₂] [MetricSpace P₁] [MetricSpace P₂] [NormedAddTorsor V₁ P₁] [NormedAddTorsor V₂ P₂]
    {a b c : P₁} {a' b' c' : P₂} (hnd : ¬Collinear ℝ ({a, b, c} : Set P₁)) (h₁ : ∠ a b c = ∠ a' b' c')
    (h₂ : ∠ b c a = ∠ b' c' a') (h₃ : dist c a = dist c' a') : Congruent ![a, b, c] ![a', b', c'] :=
  angle_angle_side hnd h₁ h₂ h₃
