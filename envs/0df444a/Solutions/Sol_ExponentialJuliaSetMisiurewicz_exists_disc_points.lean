-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.exists_disc_points
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:11:29.59694+00:00
-- url     : https://prove2.me/submissions/c8265974-d008-4a2d-97a8-6c1d000d1d42

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_ExpChaotic_HalfPlane
import Definitions.Def_ExpChaotic_RealAxis
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma6_eventually_meets_disc

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution
    {V : Set ℂ}
    (hnoreal : ∀ (n : ℕ), ∀ z ∈ V, (expIterate n z).im ≠ 0)
    {c : ℂ} {σ : ℝ} (hσ : 0 < σ) (hsub : ball c σ ⊆ V) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∃ y ∈ ball c σ, ‖expIterate n y‖ ≤ Real.exp 4 := by
  have hconn : IsConnected (ball c σ) :=
    ⟨⟨c, Metric.mem_ball_self hσ⟩, (convex_ball c σ).isPreconnected⟩
  have hnr : ∀ (n : ℕ), ∀ z ∈ ball c σ, (expIterate n z).im ≠ 0 :=
    fun n z hz => hnoreal n z (hsub hz)
  obtain ⟨N, hN⟩ := lemma6_eventually_meets_disc isOpen_ball hconn
    ⟨c, Metric.mem_ball_self hσ⟩ hnr
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨x, ⟨y, hy, rfl⟩, hx⟩ := hN n hn
  refine ⟨y, hy, ?_⟩
  rwa [Metric.mem_closedBall, dist_zero_right] at hx
end ExponentialJuliaSetMisiurewicz
