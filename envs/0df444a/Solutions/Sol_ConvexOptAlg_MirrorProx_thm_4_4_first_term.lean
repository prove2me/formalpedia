-- Prove2me | solution 1 for ConvexOptAlg.MirrorProx.thm_4_4_first_term
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:34:34.234775+00:00
-- url     : https://prove2.me/submissions/1addb9c1-b9f5-485e-b490-3c997e0ed5f5

import Mathlib
import Definitions.Def_ConvexOptAlg_MirrorProx_Defs

set_option autoImplicit false

namespace F8863cf9Aux

open ConvexOptAlg.MirrorProx

/-- First-order optimality of a Bregman projection. -/
theorem proj_opt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X D : Set E) (hXconv : Convex ℝ X) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ)
    (hΦ : IsMirrorMap D Φ Φ') (c z : E) (hp : IsBregmanProj X D Φ Φ' c z)
    (u : E) (hu : u ∈ X ∩ D) :
    0 ≤ (Φ' z - Φ' c) (u - z) := by
  obtain ⟨_, hDconv, _, hder, _, _⟩ := hΦ
  obtain ⟨hz, hmin⟩ := hp
  have hconv : Convex ℝ (X ∩ D) := hXconv.inter hDconv
  have hmo : IsMinOn (fun w => bregman Φ Φ' w c) (X ∩ D) z := fun w hw => hmin w hw
  have hloc : IsLocalMinOn (fun w => bregman Φ Φ' w c) (X ∩ D) z := hmo.localize
  have hd : HasFDerivAt (fun w => bregman Φ Φ' w c) (Φ' z - Φ' c) z := by
    have h2 : HasFDerivAt (fun w => Φ' c w - Φ' c c) (Φ' c) z :=
      (Φ' c).hasFDerivAt.sub_const _
    have h1 := ((hder z hz.2).sub_const (Φ c)).sub h2
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
    simp only [bregman, map_sub, Pi.sub_apply]
  have hy : u - z ∈ posTangentConeAt (X ∩ D) z :=
    sub_mem_posTangentConeAt_of_segment_subset (hconv.segment_subset hz hu)
  exact hloc.hasFDerivWithinAt_nonneg hd.hasFDerivWithinAt hy

end F8863cf9Aux

open ConvexOptAlg.MirrorProx in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (X D : Set E) (hXc : IsCompact X) (hXconv : Convex ℝ X) (hXD : X ⊆ closure D)
    (hXDne : (X ∩ D).Nonempty)
    (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (hΦ : IsMirrorMap D Φ Φ')
    (f' : E → E →L[ℝ] ℝ) (η : ℝ) (x y y' x' : ℕ → E)
    (hrun : IsMirrorProxRun X D Φ Φ' f' η x y y' x')
    (t : ℕ) (ht : 1 ≤ t) (u : E) (hu : u ∈ X ∩ D) :
    η * f' (y (t + 1)) (x (t + 1) - u)
      ≤ bregman Φ Φ' u (x t) - bregman Φ Φ' u (x (t + 1))
          - bregman Φ Φ' (x (t + 1)) (x t) := by
  obtain ⟨_, hstep⟩ := hrun
  obtain ⟨_, _, _, _, hx', hproj⟩ := hstep t ht
  have h := F8863cf9Aux.proj_opt X D hXconv Φ Φ' hΦ _ _ hproj u hu
  rw [ContinuousLinearMap.sub_apply, hx'] at h
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    map_sub] at h
  unfold bregman
  simp only [map_sub]
  linarith [h]
