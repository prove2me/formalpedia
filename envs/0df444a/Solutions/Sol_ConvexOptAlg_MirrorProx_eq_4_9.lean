-- Prove2me | solution 1 for ConvexOptAlg.MirrorProx.eq_4_9
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:52:03.109031+00:00
-- url     : https://prove2.me/submissions/10b8075d-afd4-4dd7-b800-11c7a0475103

import Mathlib
import Definitions.Def_ConvexOptAlg_MirrorProx_Defs

set_option autoImplicit false

open ConvexOptAlg.MirrorProx in
theorem mp_pyth_926fa291 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X D : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ)
    (hX : Convex ℝ X) (hD : Convex ℝ D) (hΦ : ∀ x ∈ D, HasFDerivAt Φ (Φ' x) x)
    (y z : E) (hz : IsBregmanProj X D Φ Φ' y z) (u : E) (hu : u ∈ X ∩ D) :
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

open ConvexOptAlg.MirrorProx in
theorem mp_mem_926fa291 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X D : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (f' : E → E →L[ℝ] ℝ) (η : ℝ)
    (x y y' x' : ℕ → E) (hrun : IsMirrorProxRun X D Φ Φ' f' η x y y' x')
    (t : ℕ) (ht : 1 ≤ t) : x t ∈ X ∩ D := by
  obtain ⟨h1, hstep⟩ := hrun
  rcases Nat.eq_or_lt_of_le ht with h | h
  · subst h; exact h1
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    exact (hstep s (by omega)).2.2.2.2.2.1

open ConvexOptAlg.MirrorProx in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X D : Set E) (hXc : IsCompact X) (hXconv : Convex ℝ X) (hXD : X ⊆ closure D)
    (hXDne : (X ∩ D).Nonempty)
    (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (hΦ : IsMirrorMap D Φ Φ')
    (ρ : ℝ) (hsc : IsStronglyConvexWRT (X ∩ D) Φ Φ' ρ)
    (f' : E → E →L[ℝ] ℝ) (η : ℝ) (x y y' x' : ℕ → E)
    (hrun : IsMirrorProxRun X D Φ Φ' f' η x y y' x')
    (t : ℕ) (ht : 1 ≤ t) :
    η * f' (x t) (y (t + 1) - x (t + 1))
        ≤ bregman Φ Φ' (x (t + 1)) (x t) - bregman Φ Φ' (x (t + 1)) (y (t + 1))
            - bregman Φ Φ' (y (t + 1)) (x t) ∧
      η * f' (x t) (y (t + 1) - x (t + 1))
        ≤ bregman Φ Φ' (x (t + 1)) (x t) - ρ / 2 * ‖x (t + 1) - y (t + 1)‖ ^ 2
            - ρ / 2 * ‖y (t + 1) - x t‖ ^ 2 := by
  obtain ⟨_, hDc, _, hder, _, _⟩ := hΦ
  have hxt : x t ∈ X ∩ D := mp_mem_926fa291 X D Φ Φ' f' η x y y' x' hrun t ht
  have hxn : x (t + 1) ∈ X ∩ D :=
    mp_mem_926fa291 X D Φ Φ' f' η x y y' x' hrun (t + 1) (by omega)
  obtain ⟨_, hgrad, hproj, _, _, _⟩ := hrun.2 t ht
  have hyn : y (t + 1) ∈ X ∩ D := hproj.1
  have hpy := mp_pyth_926fa291 X D Φ Φ' hXconv hDc hder (y' (t + 1)) (y (t + 1)) hproj
    (x (t + 1)) hxn
  have hid : η * f' (x t) (y (t + 1) - x (t + 1))
      = (Φ' (x t) - Φ' (y' (t + 1))) (y (t + 1) - x (t + 1)) := by
    have e1 : η * f' (x t) (y (t + 1) - x (t + 1))
        = (η • f' (x t)) (y (t + 1) - x (t + 1)) := by simp
    have e2 : η • f' (x t) = Φ' (x t) - Φ' (y' (t + 1)) := by rw [hgrad]; abel
    rw [e1, e2]
  have part1 : η * f' (x t) (y (t + 1) - x (t + 1))
        ≤ bregman Φ Φ' (x (t + 1)) (x t) - bregman Φ Φ' (x (t + 1)) (y (t + 1))
            - bregman Φ Φ' (y (t + 1)) (x t) := by
    rw [hid]
    simp only [bregman, ContinuousLinearMap.sub_apply, map_sub] at hpy ⊢
    linarith
  refine ⟨part1, ?_⟩
  have s1 := hsc (y (t + 1)) hyn (x (t + 1)) hxn
  have s2 := hsc (x t) hxt (y (t + 1)) hyn
  have b1 : ρ / 2 * ‖x (t + 1) - y (t + 1)‖ ^ 2 ≤ bregman Φ Φ' (x (t + 1)) (y (t + 1)) := by
    have e : ‖x (t + 1) - y (t + 1)‖ = ‖y (t + 1) - x (t + 1)‖ := norm_sub_rev _ _
    rw [e]
    simp only [bregman, map_sub] at s1 ⊢
    linarith
  have b2 : ρ / 2 * ‖y (t + 1) - x t‖ ^ 2 ≤ bregman Φ Φ' (y (t + 1)) (x t) := by
    have e : ‖y (t + 1) - x t‖ = ‖x t - y (t + 1)‖ := norm_sub_rev _ _
    rw [e]
    simp only [bregman, map_sub] at s2 ⊢
    linarith
  linarith
