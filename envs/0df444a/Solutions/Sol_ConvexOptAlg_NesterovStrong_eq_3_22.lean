-- Prove2me | solution 1 for ConvexOptAlg.NesterovStrong.eq_3_22
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:33:45.098799+00:00
-- url     : https://prove2.me/submissions/ff0ce4f0-33ae-418d-a93c-c1b16e65f6a5

import Mathlib
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn
import Definitions.Def_ConvexOptAlg_NesterovStrong_Defs

open scoped InnerProductSpace

set_option autoImplicit false

theorem p2m_7e6c14bf_alg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (α θ : ℝ) (hα : α ≠ 0) (v x g z w : E)
    (hw : w = (1 - θ) • v + θ • x - (θ / α) • g) :
    (1 - θ) * (α / 2 * ‖z - v‖ ^ 2) + θ * (⟪g, z - x⟫_ℝ + α / 2 * ‖z - x‖ ^ 2) =
      (1 - θ) * (α / 2 * ‖w - v‖ ^ 2) + θ * (⟪g, w - x⟫_ℝ + α / 2 * ‖w - x‖ ^ 2) +
        α / 2 * ‖z - w‖ ^ 2 := by
  have hvec : ((1 - θ) * α) • (w - v) + (θ * α) • (w - x) + θ • g = 0 := by
    rw [hw]
    have hc : α * (θ / α) = θ := by field_simp
    have e : ((1 - θ) * α) • ((1 - θ) • v + θ • x - (θ / α) • g - v) +
        (θ * α) • ((1 - θ) • v + θ • x - (θ / α) • g - x) + θ • g =
        (θ - α * (θ / α)) • g := by module
    rw [e, hc, sub_self, zero_smul]
  have hkey : ⟪z - w, ((1 - θ) * α) • (w - v) + (θ * α) • (w - x) + θ • g⟫_ℝ = 0 := by
    rw [hvec, inner_zero_right]
  rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_smul_right] at hkey
  have h1 : z - v = (z - w) + (w - v) := by abel
  have h2 : z - x = (z - w) + (w - x) := by abel
  rw [h1, h2, norm_add_sq_real, norm_add_sq_real, inner_add_right]
  rw [real_inner_comm (z - w) g]
  linear_combination hkey

open ConvexOptAlg.NesterovStrong in
theorem p2m_7e6c14bf_form {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (α β : ℝ)
    (hα : 0 < α) (x : ℕ → EuclideanSpace ℝ (Fin n)) :
    ∀ s : ℕ, ∀ z, Phi f g α β x (s + 1) z =
      Phi f g α β x (s + 1) (v g α β x (s + 1)) + α / 2 * ‖z - v g α β x (s + 1)‖ ^ 2 := by
  intro s
  induction s with
  | zero =>
    intro z
    simp [Phi, v]
  | succ k ih =>
    intro z
    set θ := 1 / Real.sqrt (kappa α β) with hθ
    have hw : v g α β x (k + 2) = (1 - θ) • v g α β x (k + 1) + θ • x (k + 1) -
        (θ / α) • g (x (k + 1)) := by
      rw [v]
      congr 2
      rw [hθ, div_div, mul_comm]
    have halg := p2m_7e6c14bf_alg α θ hα.ne' (v g α β x (k + 1)) (x (k + 1)) (g (x (k + 1))) z
      (v g α β x (k + 2)) hw
    show Phi f g α β x (k + 2) z = Phi f g α β x (k + 2) (v g α β x (k + 2)) +
      α / 2 * ‖z - v g α β x (k + 2)‖ ^ 2
    rw [Phi, Phi, ih z, ih (v g α β x (k + 2))]
    rw [← hθ]
    linear_combination halg

open ConvexOptAlg.NesterovStrong in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (α β : ℝ)
    (hα : 0 < α) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (s : ℕ) (hs : 1 ≤ s) :
    PhiStar f g α β x (s + 1) + α / 2 * ‖x s - v g α β x (s + 1)‖ ^ 2 =
      (1 - 1 / Real.sqrt (kappa α β)) * PhiStar f g α β x s +
        α / 2 * (1 - 1 / Real.sqrt (kappa α β)) * ‖x s - v g α β x s‖ ^ 2 +
          1 / Real.sqrt (kappa α β) * f (x s) := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  have h1 := p2m_7e6c14bf_form f g α β hα x (k + 1) (x (k + 1))
  have h0 := p2m_7e6c14bf_form f g α β hα x k (x (k + 1))
  unfold PhiStar
  rw [← h1]
  show Phi f g α β x (k + 2) (x (k + 1)) = _
  rw [Phi, h0]
  simp
  ring
