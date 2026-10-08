-- Prove2me | solution 1 for ConvexOptAlg.MirrorDescent.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:56:59.248037+00:00
-- url     : https://prove2.me/submissions/325fb567-3db5-4c1e-a4ee-03f190875a86

import Mathlib
import Definitions.Def_ConvexOptAlg_MirrorDescent_Defs

set_option autoImplicit false

open ConvexOptAlg.MirrorDescent in
theorem md_firstorder_bea8a4ca {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X D : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ)
    (hX : Convex ℝ X) (hD : Convex ℝ D) (hΦ : ∀ x ∈ D, HasFDerivAt Φ (Φ' x) x)
    (y z : E) (hz : IsBregmanProjection X D Φ Φ' y z) (u : E) (hu : u ∈ X ∩ D) :
    (Φ' z - Φ' y) (z - u) ≤ 0 := by
  obtain ⟨hzS, hmin⟩ := hz
  have hS : Convex ℝ (X ∩ D) := hX.inter hD
  have hloc : IsLocalMinOn (fun w => bregman Φ Φ' w y) (X ∩ D) z :=
    Filter.eventually_of_mem self_mem_nhdsWithin (fun w hw => hmin w hw)
  have hder : HasFDerivAt (fun w => bregman Φ Φ' w y) (Φ' z - Φ' y) z := by
    have h1 := hΦ z hzS.2
    have h2 : HasFDerivAt (fun w => Φ' y (w - y)) (Φ' y) z := by
      have h3 : HasFDerivAt (fun w => Φ' y w - Φ' y y) (Φ' y) z :=
        (Φ' y).hasFDerivAt.sub_const _
      refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
      simp [map_sub]
    have := (h1.sub_const (Φ y)).sub h2
    show HasFDerivAt (fun w => Φ w - Φ y - Φ' y (w - y)) _ z
    exact this
  have hcone : u - z ∈ posTangentConeAt (X ∩ D) z :=
    sub_mem_posTangentConeAt_of_segment_subset (hS.segment_subset hzS hu)
  have key := hloc.hasFDerivWithinAt_nonneg hder.hasFDerivWithinAt hcone
  simp only [ContinuousLinearMap.sub_apply, map_sub] at key ⊢
  linarith

open ConvexOptAlg.MirrorDescent in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X D : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ)
    (hset : IsMirrorSetting X D Φ Φ')
    (x y z : E) (hx : x ∈ X ∩ D) (hy : y ∈ D)
    (hz : IsBregmanProjection X D Φ Φ' y z) :
    (Φ' z - Φ' y) (z - x) ≤ 0 ∧
      bregman Φ Φ' x z + bregman Φ Φ' z y ≤ bregman Φ Φ' x y := by
  obtain ⟨_, hXc, ⟨_, hDc, _, hΦ, _, _⟩, _, _⟩ := hset
  have h1 := md_firstorder_bea8a4ca X D Φ Φ' hXc hDc hΦ y z hz x hx
  refine ⟨h1, ?_⟩
  simp only [ContinuousLinearMap.sub_apply, map_sub] at h1
  simp only [bregman, map_sub]
  linarith
