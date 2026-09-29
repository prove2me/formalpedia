-- Prove2me | solution 1 for DynamicsRelativity.vector_project_plane_orbit
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T00:37:39.383318+00:00
-- url     : https://prove2.me/submissions/12dd4b3f-3888-406b-bbaa-6778253bec5e

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Mathlib

open DynamicsRelativity

theorem solution {n : Vec} {x : ℝ → Vec} {A : Vec} {r₀ : ℝ} (hn : n ≠ 0)
    (h_plane : ∀ t, inner ℝ n (x t) = 0) (h_orbit : ∀ t, ‖x t‖ + inner ℝ A (x t) = r₀) :
    ∃ A' : Vec, inner ℝ n A' = 0 ∧ ∀ t, ‖x t‖ + inner ℝ A' (x t) = r₀ := by
  have hnn : inner ℝ n n ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]; exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hn)
  refine ⟨A - (inner ℝ n A / inner ℝ n n) • n, ?_, fun t => ?_⟩
  · rw [inner_sub_right, inner_smul_right]
    field_simp
    ring
  · rw [inner_sub_left, inner_smul_left, h_plane t]
    simpa using h_orbit t
