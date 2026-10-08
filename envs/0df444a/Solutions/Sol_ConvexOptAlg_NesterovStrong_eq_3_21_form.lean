-- Prove2me | solution 1 for ConvexOptAlg.NesterovStrong.eq_3_21_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T17:31:23.950838+00:00
-- url     : https://prove2.me/submissions/081e49c0-48c9-4e48-bbf9-3307c9548c8b

import Mathlib
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn
import Definitions.Def_ConvexOptAlg_NesterovStrong_Defs

open scoped InnerProductSpace

namespace ConvexOptAlg.NesterovStrong.P4c8c6511

lemma step_alg {n : ℕ} (z v x g : EuclideanSpace ℝ (Fin n)) (α c d K F : ℝ)
    (hd : α * d = c) :
    (1 - c) * (K + α / 2 * ‖z - v‖ ^ 2) +
        c * (F + ⟪g, z - x⟫_ℝ + α / 2 * ‖z - x‖ ^ 2) =
      ((1 - c) * (K + α / 2 * ‖((1 - c) • v + c • x - d • g) - v‖ ^ 2) +
        c * (F + ⟪g, ((1 - c) • v + c • x - d • g) - x⟫_ℝ +
          α / 2 * ‖((1 - c) • v + c • x - d • g) - x‖ ^ 2)) +
      α / 2 * ‖z - ((1 - c) • v + c • x - d • g)‖ ^ 2 := by
  set w := (1 - c) • v + c • x - d • g with hw
  have e1 : z - v = (z - w) + (w - v) := by abel
  have e2 : z - x = (z - w) + (w - x) := by abel
  have key : (1 - c) • (w - v) + c • (w - x) = -(d • g) := by
    rw [hw]
    module
  have hk : ⟪z - w, (1 - c) • (w - v) + c • (w - x)⟫_ℝ = ⟪z - w, -(d • g)⟫_ℝ := by rw [key]
  rw [inner_add_right, inner_smul_right, inner_smul_right, inner_neg_right,
    inner_smul_right] at hk
  rw [e1, e2, norm_add_sq_real, norm_add_sq_real, inner_add_right]
  have hc : ⟪g, z - w⟫_ℝ = ⟪z - w, g⟫_ℝ := real_inner_comm _ _
  rw [hc]
  linear_combination α * hk - ⟪z - w, g⟫_ℝ * hd

end ConvexOptAlg.NesterovStrong.P4c8c6511

open ConvexOptAlg.NesterovStrong.P4c8c6511 in
open ConvexOptAlg.NesterovStrong in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (α β : ℝ)
    (hα : 0 < α) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (s : ℕ) (hs : 1 ≤ s) (z : EuclideanSpace ℝ (Fin n)) :
    Phi f g α β x s z = PhiStar f g α β x s + α / 2 * ‖z - v g α β x s‖ ^ 2 := by
  unfold PhiStar
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  induction m generalizing z with
  | zero =>
    simp only [Phi, v]
    simp
  | succ m ih =>
    have hd : α * (1 / (α * Real.sqrt (kappa α β))) = 1 / Real.sqrt (kappa α β) := by
      rcases eq_or_ne (Real.sqrt (kappa α β)) 0 with h | h
      · simp [h]
      · field_simp
    have h1 := ih z (by omega)
    have h2 := ih (v g α β x (m + 2)) (by omega)
    show Phi f g α β x (m + 2) z =
      Phi f g α β x (m + 2) (v g α β x (m + 2)) + α / 2 * ‖z - v g α β x (m + 2)‖ ^ 2
    simp only [Phi]
    rw [h1, h2]
    simp only [v]
    exact step_alg _ _ _ _ α _ _ _ _ hd
