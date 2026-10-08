-- Prove2me | solution 1 for ConvexOptAlg.MirrorProx.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:25:23.828373+00:00
-- url     : https://prove2.me/submissions/43464aa4-171a-4596-9c11-49fa424dcf80

import Mathlib
import Definitions.Def_ConvexOptAlg_MirrorProx_Defs

set_option autoImplicit false

open ConvexOptAlg.MirrorProx in
theorem mp_firstorder_c925566d {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X D : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ)
    (hX : Convex ℝ X) (hD : Convex ℝ D) (hΦ : ∀ x ∈ D, HasFDerivAt Φ (Φ' x) x)
    (y z : E) (hz : IsBregmanProj X D Φ Φ' y z) (u : E) (hu : u ∈ X ∩ D) :
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

open ConvexOptAlg.MirrorProx in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X D : Set E) (hXc : IsCompact X) (hXconv : Convex ℝ X) (hXD : X ⊆ closure D)
    (hXDne : (X ∩ D).Nonempty)
    (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (hΦ : IsMirrorMap D Φ Φ')
    (x y z : E) (hx : x ∈ X ∩ D) (hy : y ∈ D) (hz : IsBregmanProj X D Φ Φ' y z) :
    (Φ' z - Φ' y) (z - x) ≤ 0 ∧
      bregman Φ Φ' x z + bregman Φ Φ' z y ≤ bregman Φ Φ' x y := by
  obtain ⟨_, hDc, _, hΦd, _, _⟩ := hΦ
  have h1 := mp_firstorder_c925566d X D Φ Φ' hXconv hDc hΦd y z hz x hx
  refine ⟨h1, ?_⟩
  simp only [ContinuousLinearMap.sub_apply, map_sub] at h1
  simp only [bregman, map_sub]
  linarith
