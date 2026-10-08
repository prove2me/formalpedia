-- Prove2me | solution 1 for BanditGD.Regret.points_mem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T04:11:17.984629+00:00
-- url     : https://prove2.me/submissions/624b3866-fe01-406d-9ae8-74d54bcfd43a

import Mathlib
import Definitions.Def_RegretBandits_Nonlinear_OSGD
import Definitions.Def_BanditGD_Regret_Setting
open scoped Pointwise

open BanditGD.Regret Pointwise in
theorem solution {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (hSconv : Convex ℝ S)
    (r : ℝ) (hr : 0 < r) (hrS : Metric.closedBall 0 r ⊆ S)
    (α δ ν : ℝ) (hδ : 0 < δ) (hδα : δ ≤ α * r) (hα1 : α ≤ 1)
    (c : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (u y : ℕ → EuclideanSpace ℝ (Fin d)) (hu : ∀ t, ‖u t‖ = 1)
    (hrun : IsBGDRun S α δ ν c u y) :
    ∀ t, 1 ≤ t → y t ∈ (1 - α) • S ∧ y t + δ • u t ∈ S := by
  obtain ⟨h1, hstep⟩ := hrun
  have hαpos : 0 < α := by
    by_contra h
    push_neg at h
    nlinarith
  have h0S : (0 : EuclideanSpace ℝ (Fin d)) ∈ S :=
    hrS (Metric.mem_closedBall_self hr.le)
  have hmem : ∀ t, 1 ≤ t → y t ∈ (1 - α) • S := by
    intro t ht
    rcases Nat.exists_eq_add_of_le ht with ⟨k, rfl⟩
    rcases k with _ | k
    · rw [h1]
      exact ⟨0, h0S, smul_zero _⟩
    · have := (hstep (1 + k) (by omega)).1
      simpa [add_assoc, add_comm, add_left_comm] using this
  intro t ht
  refine ⟨hmem t ht, ?_⟩
  obtain ⟨s, hs, hys⟩ := hmem t ht
  have hv : (δ / α) • u t ∈ S := by
    apply hrS
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hu t, mul_one,
      Real.norm_eq_abs, abs_of_pos (div_pos hδ hαpos)]
    rw [div_le_iff₀ hαpos]
    linarith
  have hconv := hSconv hs hv (show (0:ℝ) ≤ 1 - α by linarith) hαpos.le (by ring)
  have heq : (1 - α) • s + α • ((δ / α) • u t) = y t + δ • u t := by
    rw [← hys, smul_smul, mul_div_cancel₀ _ hαpos.ne']
  simpa only [smul_eq_mul, heq] using hconv
