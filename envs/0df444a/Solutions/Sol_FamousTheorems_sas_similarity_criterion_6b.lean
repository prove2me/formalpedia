-- Prove2me | solution 1 for FamousTheorems.sas_similarity_criterion_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:21:36.700169+00:00
-- url     : https://prove2.me/submissions/ec0cc140-9c90-4d53-a9cc-a91c6e1f4b22

import Mathlib

open EuclideanGeometry

theorem solution {V₁ V₂ P₁ P₂ : Type*} [NormedAddCommGroup V₁] [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₁]
    [InnerProductSpace ℝ V₂] [MetricSpace P₁] [MetricSpace P₂] [NormedAddTorsor V₁ P₁] [NormedAddTorsor V₂ P₂]
    {a b c : P₁} {a' b' c' : P₂} (hnd : ¬Collinear ℝ ({a, b, c} : Set P₁))
    (hnd' : ¬Collinear ℝ ({a', b', c'} : Set P₂)) (h₁ : ∠ a b c = ∠ a' b' c')
    (h₂ : dist a b * dist b' c' = dist b c * dist a' b') : Similar ![a, b, c] ![a', b', c'] :=
  similar_of_side_angle_side hnd hnd' h₁ h₂
