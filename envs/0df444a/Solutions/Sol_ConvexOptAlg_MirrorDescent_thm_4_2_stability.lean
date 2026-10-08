-- Prove2me | solution 1 for ConvexOptAlg.MirrorDescent.thm_4_2_stability
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:34:57.608245+00:00
-- url     : https://prove2.me/submissions/3d982813-afeb-42a2-a0e2-a4d7af30041f

import Mathlib
import Definitions.Def_ConvexOptAlg_MirrorDescent_Defs

set_option autoImplicit false

open ConvexOptAlg.MirrorDescent in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (X D : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ)
    (hset : IsMirrorSetting X D Φ Φ')
    (ρ : ℝ) (hρ : 0 < ρ) (hΦ : IsStronglyConvexMirror X D Φ Φ' ρ)
    (f : E → ℝ) (hf : ConvexOn ℝ X f) (L : ℝ)
    (η : ℝ) (hη : 0 < η) (x y : ℕ → E) (g : ℕ → E →L[ℝ] ℝ) (T : ℕ)
    (hgL : ∀ s : ℕ, 1 ≤ s → s ≤ T → ‖g s‖ ≤ L)
    (hrun : IsMirrorDescentRun X D Φ Φ' f η x y g T)
    (s : ℕ) (hs1 : 1 ≤ s) (hsT : s ≤ T) :
    bregman Φ Φ' (x s) (y (s + 1)) - bregman Φ Φ' (x (s + 1)) (y (s + 1)) ≤
      (η * L) ^ 2 / (2 * ρ) := by
  obtain ⟨h1, _, hstep⟩ := hrun
  have hxs : x s ∈ X ∩ D := by
    rcases Nat.lt_or_ge 1 s with h | h
    · obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
      exact (hstep k (by omega) (by omega)).2.2.2.1
    · have hs : s = 1 := by omega
      subst hs
      exact h1
  obtain ⟨_, _, hy, hproj⟩ := hstep s hs1 hsT
  have hxs1 : x (s + 1) ∈ X ∩ D := hproj.1
  have hsc := hΦ (x s) hxs (x (s + 1)) hxs1
  have hlin : Φ' (y (s + 1)) (x s - y (s + 1)) - Φ' (y (s + 1)) (x (s + 1) - y (s + 1)) =
      Φ' (x s) (x s - x (s + 1)) - η * g s (x s - x (s + 1)) := by
    rw [← map_sub, hy, sub_sub_sub_cancel_right]
    simp
  have hg : g s (x s - x (s + 1)) ≤ L * ‖x s - x (s + 1)‖ := by
    calc g s (x s - x (s + 1)) ≤ ‖g s (x s - x (s + 1))‖ := Real.le_norm_self _
      _ ≤ ‖g s‖ * ‖x s - x (s + 1)‖ := (g s).le_opNorm _
      _ ≤ L * ‖x s - x (s + 1)‖ :=
          mul_le_mul_of_nonneg_right (hgL s hs1 hsT) (norm_nonneg _)
  have hg' : η * g s (x s - x (s + 1)) ≤ η * (L * ‖x s - x (s + 1)‖) :=
    mul_le_mul_of_nonneg_left hg hη.le
  have key : η * L * ‖x s - x (s + 1)‖ - ρ / 2 * ‖x s - x (s + 1)‖ ^ 2 ≤
      (η * L) ^ 2 / (2 * ρ) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (η * L - ρ * ‖x s - x (s + 1)‖)]
  unfold bregman
  nlinarith
