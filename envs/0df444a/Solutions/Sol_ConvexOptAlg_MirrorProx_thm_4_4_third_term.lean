-- Prove2me | solution 1 for ConvexOptAlg.MirrorProx.thm_4_4_third_term
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:22:49.778772+00:00
-- url     : https://prove2.me/submissions/a81100c8-b784-4302-834e-3b0df2e06da0

import Mathlib
import Definitions.Def_ConvexOptAlg_MirrorProx_Defs

set_option autoImplicit false

open ConvexOptAlg.MirrorProx in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (X D : Set E) (hXc : IsCompact X) (hXconv : Convex ℝ X) (hXD : X ⊆ closure D)
    (hXDne : (X ∩ D).Nonempty)
    (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (hΦ : IsMirrorMap D Φ Φ')
    (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (β : ℝ) (hsm : IsSmoothWRT X f f' β)
    (η : ℝ) (x y y' x' : ℕ → E)
    (hrun : IsMirrorProxRun X D Φ Φ' f' η x y y' x')
    (t : ℕ) (ht : 1 ≤ t) :
    (f' (y (t + 1)) - f' (x t)) (y (t + 1) - x (t + 1))
        ≤ ‖f' (y (t + 1)) - f' (x t)‖ * ‖y (t + 1) - x (t + 1)‖ ∧
      ‖f' (y (t + 1)) - f' (x t)‖ * ‖y (t + 1) - x (t + 1)‖
        ≤ β * ‖y (t + 1) - x t‖ * ‖y (t + 1) - x (t + 1)‖ ∧
      β * ‖y (t + 1) - x t‖ * ‖y (t + 1) - x (t + 1)‖
        ≤ β / 2 * ‖y (t + 1) - x t‖ ^ 2 + β / 2 * ‖y (t + 1) - x (t + 1)‖ ^ 2 := by
  obtain ⟨hx1, hstep⟩ := hrun
  have hxt : x t ∈ X := by
    rcases Nat.lt_or_ge t 2 with h | h
    · have : t = 1 := by omega
      subst this; exact hx1.1
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      exact (hstep s (by omega)).2.2.2.2.2.1.1
  have hyt : y (t + 1) ∈ X := (hstep t ht).2.2.1.1.1
  have hxt1 : x (t + 1) ∈ X := (hstep t ht).2.2.2.2.2.1.1
  have hL1 := hsm.2 _ hyt _ hxt
  have hL2 := hsm.2 _ hyt _ hxt1
  have hn1 : ‖f' (y (t + 1)) - f' (x t)‖ ≥ 0 := norm_nonneg _
  have hn2 : ‖f' (y (t + 1)) - f' (y (t + 1))‖ ≥ 0 := norm_nonneg _
  have ha := norm_nonneg (y (t + 1) - x t)
  have hb := norm_nonneg (y (t + 1) - x (t + 1))
  refine ⟨?_, ?_, ?_⟩
  · have h1 := (f' (y (t + 1)) - f' (x t)).le_opNorm (y (t + 1) - x (t + 1))
    rw [Real.norm_eq_abs] at h1
    exact (le_abs_self _).trans h1
  · exact mul_le_mul_of_nonneg_right hL1 hb
  · rcases le_or_gt 0 β with hβ | hβ
    · nlinarith [mul_nonneg hβ (sq_nonneg (‖y (t + 1) - x t‖ - ‖y (t + 1) - x (t + 1)‖))]
    · have hL2' := hsm.2 _ hyt _ hxt1
      have hb0 : ‖y (t + 1) - x (t + 1)‖ = 0 := by
        have := norm_nonneg (f' (y (t + 1)) - f' (x (t + 1)))
        nlinarith
      have ha0 : ‖y (t + 1) - x t‖ = 0 := by nlinarith
      rw [ha0, hb0]; simp
