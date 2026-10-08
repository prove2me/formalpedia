-- Prove2me | solution 1 for ConvexOptAlg.MirrorDescent.thm_4_2_step
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:28:31.231394+00:00
-- url     : https://prove2.me/submissions/4806d8e3-e1e8-4a6e-8dac-3397cedbbdbf

import Mathlib
import Definitions.Def_ConvexOptAlg_MirrorDescent_Defs

set_option autoImplicit false

open ConvexOptAlg.MirrorDescent in
theorem md_pyth_1089097f {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X D : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ)
    (hX : Convex ℝ X) (hD : Convex ℝ D) (hΦ : ∀ x ∈ D, HasFDerivAt Φ (Φ' x) x)
    (y z : E) (hz : IsBregmanProjection X D Φ Φ' y z) (u : E) (hu : u ∈ X ∩ D) :
    bregman Φ Φ' u z + bregman Φ Φ' z y ≤ bregman Φ Φ' u y := by
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
  simp only [ContinuousLinearMap.sub_apply, map_sub] at key
  simp only [bregman, map_sub]
  linarith

open ConvexOptAlg.MirrorDescent in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X D : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ)
    (hset : IsMirrorSetting X D Φ Φ')
    (f : E → ℝ) (hf : ConvexOn ℝ X f)
    (η : ℝ) (hη : 0 < η) (x y : ℕ → E) (g : ℕ → E →L[ℝ] ℝ) (T : ℕ)
    (hrun : IsMirrorDescentRun X D Φ Φ' f η x y g T)
    (s : ℕ) (hs1 : 1 ≤ s) (hsT : s ≤ T) (u : E) (hu : u ∈ X ∩ D) :
    f (x s) - f u ≤
      (1 / η) * (bregman Φ Φ' u (x s) + bregman Φ Φ' (x s) (y (s + 1))
        - bregman Φ Φ' u (x (s + 1)) - bregman Φ Φ' (x (s + 1)) (y (s + 1))) := by
  obtain ⟨_, hXc, ⟨_, hDc, _, hΦ, _, _⟩, _, _⟩ := hset
  obtain ⟨_, _, hstep⟩ := hrun
  obtain ⟨hsub, _, hgrad, hproj⟩ := hstep s hs1 hsT
  have hpy := md_pyth_1089097f X D Φ Φ' hXc hDc hΦ (y (s + 1)) (x (s + 1)) hproj u hu
  have hsg := hsub u hu.1
  have hid : η * g s (x s - u) = bregman Φ Φ' u (x s) + bregman Φ Φ' (x s) (y (s + 1))
      - bregman Φ Φ' u (y (s + 1)) := by
    have e1 : η * g s (x s - u) = (η • g s) (x s - u) := by simp
    have e2 : η • g s = Φ' (x s) - Φ' (y (s + 1)) := by rw [hgrad]; abel
    rw [e1, e2]
    simp only [bregman, ContinuousLinearMap.sub_apply, map_sub]
    ring
  have hm := mul_le_mul_of_nonneg_left hsg hη.le
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hη]
  nlinarith
