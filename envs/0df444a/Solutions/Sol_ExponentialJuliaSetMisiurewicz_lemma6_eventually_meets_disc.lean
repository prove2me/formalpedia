-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.lemma6_eventually_meets_disc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:41.766972+00:00
-- url     : https://prove2.me/submissions/e832298e-6b6f-41c0-9f87-563e357c5e5f

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_ExpChaotic_HalfPlane
import Definitions.Def_ExpChaotic_RealAxis
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma5_real_axis_of_frequently_in_rightHalfPlane
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ



set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution
    {V : Set ℂ} (hVopen : IsOpen V) (hVconn : IsConnected V) (hVne : V.Nonempty)
    (hnoreal : ∀ (n : ℕ), ∀ z ∈ V, (expIterate n z).im ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N,
      (expIterate n '' V ∩ closedBall (0 : ℂ) (Real.exp 4)).Nonempty := by
  have hfin : {n : ℕ | MapsTo (expIterate n) V rightHalfPlane}.Finite := by
    by_contra hinf
    rw [Set.not_finite] at hinf
    obtain ⟨n, z, hz, hval⟩ :=
      lemma5_real_axis_of_frequently_in_rightHalfPlane hVopen hVconn hVne hinf
    exact hnoreal n z hz hval
  obtain ⟨M, hM⟩ := hfin.bddAbove
  refine ⟨M + 2, fun n hn => ?_⟩
  have hn1 : ¬ MapsTo (expIterate (n - 1)) V rightHalfPlane := by
    intro hmaps
    have hle : n - 1 ≤ M := hM hmaps
    omega
  rw [MapsTo] at hn1
  push Not at hn1
  obtain ⟨z, hz, hnot⟩ := hn1
  refine ⟨expIterate n z, ⟨z, hz, rfl⟩, ?_⟩
  have hre : (expIterate (n - 1) z).re ≤ 4 := by
    by_contra hgt
    push Not at hgt
    exact hnot hgt
  have hidx : n = (n - 1) + 1 := by omega
  rw [Metric.mem_closedBall, dist_zero_right]
  conv_lhs => rw [hidx]
  rw [expIterate_succ, Complex.norm_exp]
  exact Real.exp_le_exp.mpr hre
end ExponentialJuliaSetMisiurewicz
