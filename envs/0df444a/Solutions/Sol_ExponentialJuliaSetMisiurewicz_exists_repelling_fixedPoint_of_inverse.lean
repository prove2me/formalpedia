-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.exists_repelling_fixedPoint_of_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:08.845794+00:00
-- url     : https://prove2.me/submissions/1bd87ee3-4cec-40a8-a8ee-f8d81c97f601

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Definitions.Def_ExpChaotic_Covering
import Definitions.Def_ExpChaotic_Periodic
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero



set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution
    {f h : ℂ → ℂ} {a : ℂ} {r : ℝ} (hr : 0 < r)
    (hlip : LipschitzOnWith (1 / 2) h (closedBall a r))
    (hmaps : MapsTo h (closedBall a r) (ball a (r / 2)))
    (hinv : ∀ z ∈ closedBall a r, f (h z) = z)
    (hf : Differentiable ℂ f) (hf0 : ∀ z, deriv f z ≠ 0) :
    ∃ p ∈ ball a r, f p = p ∧ 1 < ‖deriv f p‖ := by
  -- Apply Banach on the complete closed disk; the smaller image disk makes the fixed point
  -- interior.
  have hself : MapsTo h (closedBall a r) (closedBall a r) :=
    fun z hz => ball_subset_closedBall ((ball_subset_ball (by linarith)) (hmaps hz))
  have hcontract : ContractingWith (1 / 2) (hself.restrict h _ _) :=
    ⟨by norm_num, hlip.mapsToRestrict hself⟩
  obtain ⟨p, hp, hfix, _⟩ := ContractingWith.exists_fixedPoint'
    isClosed_closedBall.isComplete hself hcontract (mem_closedBall_self hr.le)
      (edist_ne_top a (h a))
  have hhp : h p = p := hfix
  have hpball : p ∈ ball a r := by
    have hh := hmaps hp
    rw [hhp] at hh
    exact (ball_subset_ball (by linarith)) hh
  -- At the interior fixed point the inverse identity can be differentiated.
  have hpnhds : closedBall a r ∈ 𝓝 p :=
    mem_of_superset (isOpen_ball.mem_nhds hpball) ball_subset_closedBall
  have hcont : ContinuousAt h p := (hlip.continuousOn p hp).continuousAt hpnhds
  have hright : ∀ᶠ z in 𝓝 p, f (h z) = z :=
    Filter.mem_of_superset hpnhds (fun z hz => hinv z hz)
  have hd : HasDerivAt h (deriv f p)⁻¹ p :=
    HasDerivAt.of_local_left_inverse hcont
      (by rw [hhp]; exact (hf p).hasDerivAt) (hf0 p) hright
  -- The inverse derivative has norm at most 1/2, so the forward multiplier has norm at least two.
  have hbound := hd.le_of_lipschitzOn hpnhds hlip
  rw [norm_inv] at hbound
  have hpos : 0 < ‖deriv f p‖ := norm_pos_iff.mpr (hf0 p)
  rw [← one_div] at hbound
  have hmul := (div_le_iff₀ hpos).mp hbound
  refine ⟨p, hpball, ?_, ?_⟩
  · simpa only [hhp] using hinv p hp
  · norm_num at hmul
    linarith
end ExponentialJuliaSetMisiurewicz
