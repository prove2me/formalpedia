-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.exists_repelling_near_real_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:20.5113+00:00
-- url     : https://prove2.me/submissions/c83376c0-d9e4-4599-85d7-094dbf90510f

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
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_exists_lipschitz_local_inverse
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_logIterate_real_ball
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_exists_repelling_fixedPoint_of_inverse
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_closing_inverse_on_small_ball
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_deriv_expIterate_ne_zero
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_differentiable_expIterate
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_real_orbit
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
theorem _root_.solution {a : ℂ} (ha : a ≠ 0)
    {m : ℕ} (hm : expIterate m a = 10) {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ ball a ε, ∃ N : ℕ,
      0 < N ∧ expIterate N p = p ∧ 1 < ‖deriv (expIterate N) p‖ := by
  obtain ⟨r, hr, hrε, C, ρ, hclosing⟩ := closing_inverse_on_small_ball ha hε
  have hsd : HasStrictDerivAt (expIterate m) (deriv (expIterate m) a) a :=
    ((differentiable_expIterate m).analyticAt a).hasStrictDerivAt
  obtain ⟨g, A, s, hs, hga, hglip, hginv⟩ :=
    exists_lipschitz_local_inverse hsd (deriv_expIterate_ne_zero m a)
  rw [hm] at hga hglip hginv
  -- The logarithmic contraction eventually dominates both fixed local Lipschitz constants.
  have hlim : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsmall : ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) ^ n * 8 < s := by
    have h := hlim.mul_const 8
    simp only [zero_mul] at h
    exact h.eventually (gt_mem_nhds hs)
  have hsmallA : ∀ᶠ n : ℕ in atTop, (A : ℝ) * ((1 / 2 : ℝ) ^ n * 8) < r / 2 := by
    have h := (hlim.mul_const 8).const_mul (A : ℝ)
    simp only [mul_zero, zero_mul] at h
    exact h.eventually (gt_mem_nhds (by positivity))
  have hsmallAC : ∀ᶠ n : ℕ in atTop, (A : ℝ) * (1 / 2 : ℝ) ^ n * (C : ℝ) < 1 / 2 := by
    have h := (hlim.const_mul (A : ℝ)).mul_const (C : ℝ)
    simp only [mul_zero, zero_mul] at h
    exact h.eventually (gt_mem_nhds (by norm_num))
  have hfar : ∀ᶠ n : ℕ in atTop, ρ ≤ (expIterate n (10 : ℂ)).re := by
    obtain ⟨d, hd⟩ := exists_nat_gt (ρ - 10)
    refine eventually_atTop.2 ⟨d, fun n hn => ?_⟩
    have hcast : (d : ℝ) ≤ n := by exact_mod_cast hn
    have h := (expIterate_real_orbit (p := (10 : ℂ)) (by norm_num) n).2
    norm_num at h
    linarith
  -- Choose one time satisfying all size, contraction and location requirements.
  obtain ⟨n, hnsmall, hnA, hnAC, hnfar⟩ := (hsmall.and (hsmallA.and (hsmallAC.and hfar))).exists
  obtain ⟨ψ, hψlip, hψmaps, hψinv⟩ := hclosing (expIterate n (10 : ℂ)).re hnfar
  have hnreal : (((expIterate n (10 : ℂ)).re : ℝ) : ℂ) = expIterate n (10 : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using (expIterate_real_orbit (p := (10 : ℂ)) (by norm_num) n).1.symm
  rw [hnreal] at hψmaps
  obtain ⟨hlogcenter, hlogmaps, hloglip, hloginv⟩ :=
    logIterate_real_ball (x := (10 : ℂ)) (by norm_num) (by norm_num) n
  have hlogbound : ∀ z ∈ ball (expIterate n (10 : ℂ)) 8,
      ‖logIterate n z - 10‖ ≤ (1 / 2 : ℝ) ^ n * 8 := by
    intro z hz
    have h := hloglip.norm_sub_le hz (mem_ball_self (by norm_num : (0 : ℝ) < 8))
    rw [hlogcenter] at h
    have hz' : ‖z - expIterate n (10 : ℂ)‖ ≤ 8 := by
      exact le_of_lt (by simpa [mem_ball, dist_eq_norm] using hz)
    have h' : ‖logIterate n z - 10‖ ≤
        (1 / 2 : ℝ) ^ n * ‖z - expIterate n (10 : ℂ)‖ := by
      simpa using h
    exact h'.trans (mul_le_mul_of_nonneg_left hz' (by positivity))
  have hinto : MapsTo (logIterate n ∘ ψ) (closedBall a r) (ball (10 : ℂ) s) := by
    intro z hz
    rw [mem_ball, dist_eq_norm]
    exact (hlogbound _ (hψmaps hz)).trans_lt hnsmall
  -- Return via two logarithms, n principal logarithms, and the local inverse of expIterate m.
  let H : ℂ → ℂ := g ∘ logIterate n ∘ ψ
  have hHlip : LipschitzOnWith (1 / 2) H (closedBall a r) := by
    have h := hglip.comp (hloglip.comp hψlip hψmaps) hinto
    apply h.weaken
    exact_mod_cast (show (A : ℝ) * ((1 / 2 : ℝ) ^ n * (C : ℝ)) ≤ 1 / 2 by nlinarith [hnAC])
  have hHmaps : MapsTo H (closedBall a r) (ball a (r / 2)) := by
    intro z hz
    have h := hglip.norm_sub_le (hinto hz) (mem_ball_self hs)
    rw [hga] at h
    rw [mem_ball, dist_eq_norm]
    change ‖g (logIterate n (ψ z)) - a‖ < r / 2
    exact (h.trans (mul_le_mul_of_nonneg_left (hlogbound _ (hψmaps hz)) A.coe_nonneg)).trans_lt hnA
  -- Reverse those three inverse steps to identify the forward return time as 2 + n + m.
  have hHinv : ∀ z ∈ closedBall a r, expIterate (2 + n + m) (H z) = z := by
    intro z hz
    calc
      expIterate (2 + n + m) (H z) =
          expIterate 2 (expIterate n (expIterate m (g (logIterate n (ψ z))))) := by
        dsimp [H]
        exact (Function.iterate_add_apply exponentialMap (2 + n) m _).trans
          (Function.iterate_add_apply exponentialMap 2 n _)
      _ = z := by rw [hginv (logIterate n (ψ z)) (hinto hz), hloginv _ (hψmaps hz), hψinv z hz]
  obtain ⟨p, hp, hperiod, hrepel⟩ :=
    exists_repelling_fixedPoint_of_inverse hr hHlip hHmaps hHinv
      (differentiable_expIterate _) (deriv_expIterate_ne_zero _)
  exact ⟨p, (ball_subset_ball hrε) hp, 2 + n + m, by omega, hperiod, hrepel⟩
end ExponentialJuliaSetMisiurewicz
