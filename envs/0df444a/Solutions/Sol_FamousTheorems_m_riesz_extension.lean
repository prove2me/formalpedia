-- Prove2me | solution 1 for FamousTheorems.m_riesz_extension
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:19:46.282397+00:00
-- url     : https://prove2.me/submissions/155e287c-2002-409b-a2cb-0bec321185d6

import Mathlib

theorem solution {E : Type*} [AddCommGroup E] [Module ℝ E] (s : PointedCone ℝ E) (f : E →ₗ.[ℝ] ℝ)
    (nonneg : ∀ x : f.domain, (x : E) ∈ s → 0 ≤ f x) (dense : ∀ y : E, ∃ x : f.domain, (x : E) + y ∈ s) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x ∈ s, 0 ≤ g x :=
  riesz_extension s f nonneg dense
