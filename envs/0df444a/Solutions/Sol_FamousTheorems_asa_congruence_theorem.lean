-- Prove2me | solution 1 for FamousTheorems.asa_congruence_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:26:25.945482+00:00
-- url     : https://prove2.me/submissions/6b75f602-a48c-4eac-8fc2-abac8df20e8b

import Mathlib

open EuclideanGeometry

theorem solution {V₁ V₂ P₁ P₂ : Type*} [NormedAddCommGroup V₁] [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₁]
    [InnerProductSpace ℝ V₂] [MetricSpace P₁] [MetricSpace P₂] [NormedAddTorsor V₁ P₁] [NormedAddTorsor V₂ P₂]
    {a b c : P₁} {a' b' c' : P₂} (hnd : ¬Collinear ℝ ({a, b, c} : Set P₁)) (h₁ : ∠ a b c = ∠ a' b' c')
    (h₂ : dist b c = dist b' c') (h₃ : ∠ b c a = ∠ b' c' a') : Congruent ![a, b, c] ![a', b', c'] :=
  angle_side_angle hnd h₁ h₂ h₃
