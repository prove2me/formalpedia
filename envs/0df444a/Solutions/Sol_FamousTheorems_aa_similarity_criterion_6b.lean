-- Prove2me | solution 1 for FamousTheorems.aa_similarity_criterion_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:21:16.680433+00:00
-- url     : https://prove2.me/submissions/c7bd9e3a-3383-4dc5-9f1f-059820e13392

import Mathlib

open EuclideanGeometry

theorem solution {V₁ V₂ P₁ P₂ : Type*} [NormedAddCommGroup V₁] [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₁]
    [InnerProductSpace ℝ V₂] [MetricSpace P₁] [MetricSpace P₂] [NormedAddTorsor V₁ P₁] [NormedAddTorsor V₂ P₂]
    {a b c : P₁} {a' b' c' : P₂} (hnd : ¬Collinear ℝ ({a, b, c} : Set P₁)) (h₁ : ∠ a b c = ∠ a' b' c')
    (h₂ : ∠ b c a = ∠ b' c' a') : Similar ![a, b, c] ![a', b', c'] :=
  similar_of_angle_angle hnd h₁ h₂
