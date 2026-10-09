-- Prove2me | solution 1 for BookProof.BrstUnboundedLeakage.flow_apply_flow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:46:48.959692+00:00
-- url     : https://prove2.me/submissions/6921a246-277b-43db-9f8e-74c1e8bb2abd

-- Generated from ChapterBrstUnboundedLeakage.lean — solution of BookProof.BrstUnboundedLeakage.flow_apply_flow
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
open BookProof.BrstUnboundedLeakage



open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 1000000 in
theorem solution (B : H →L[ℂ] H) (s u : ℝ) (x : H) :
    flow B u (flow B s x) = flow B (u + s) x := by

  have hc : Commute (u • ((-Complex.I) • B)) (s • ((-Complex.I) • B)) :=
    ((Commute.refl ((-Complex.I) • B)).smul_left u).smul_right s
  have hball : ∀ z : H →L[ℂ] H,
      z ∈ Metric.eball (0 : H →L[ℂ] H) (expSeries ℂ (H →L[ℂ] H)).radius := by
    intro z
    rw [expSeries_radius_eq_top ℂ (H →L[ℂ] H)]
    exact Metric.mem_eball.mpr (edist_lt_top z (0 : H →L[ℂ] H))
  have h : exp (u • ((-Complex.I) • B)) * exp (s • ((-Complex.I) • B))
      = exp ((u + s) • ((-Complex.I) • B)) := by
    rw [← exp_add_of_commute_of_mem_ball (𝕂 := ℂ) hc (hball _) (hball _), ← add_smul]
  calc flow B u (flow B s x)
      = (exp (u • ((-Complex.I) • B)) * exp (s • ((-Complex.I) • B))) x := rfl
    _ = flow B (u + s) x := by rw [h]; rfl
