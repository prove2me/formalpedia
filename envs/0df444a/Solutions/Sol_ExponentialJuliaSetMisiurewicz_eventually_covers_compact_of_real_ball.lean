-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.eventually_covers_compact_of_real_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:58.439159+00:00
-- url     : https://prove2.me/submissions/12e3f913-9c38-4bf9-8b48-8eb6ae5d267b

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_RealAxis
import Definitions.Def_ExpChaotic_Covering
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_exp_ball_real_expands
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_eventually_unit_ball_subset_iterate_real
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_compact_subset_exp_exp_ball_real
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
theorem _root_.solution {K : Set ℂ}
    (hK : IsCompact K) (hK0 : (0 : ℂ) ∉ K)
    {x : ℂ} (hx : x.im = 0) (hx2 : 2 ≤ x.re) {r : ℝ} (hr : 0 < r) :
    ∃ N : ℕ, ∀ n ≥ N, K ⊆ expIterate n '' ball x r := by
  obtain ⟨N, hN⟩ := eventually_unit_ball_subset_iterate_real hx hx2 hr
  obtain ⟨ρ, hρ⟩ := compact_subset_exp_exp_ball_real hK hK0
  obtain ⟨d, hd⟩ := exists_nat_gt (max 8 ρ - x.re)
  -- After reaching a unit disk, one iterate gives radius eight and two more cover K.
  have htail : ∀ k ≥ max N d, K ⊆ expIterate (k + 3) '' ball x r := by
    intro k hk w hw
    have hkN : N ≤ k := (le_max_left _ _).trans hk
    have hkd : (d : ℝ) ≤ k := by exact_mod_cast (le_max_right N d).trans hk
    have hxk : max 8 ρ ≤ (expIterate k x).re := by
      linarith [(expIterate_real_orbit hx k).2]
    have hxnext : ρ ≤ (expIterate (k + 1) x).re := by
      have h := (expIterate_real_orbit hx (k + 1)).2
      push_cast at h
      linarith [le_max_right (8 : ℝ) ρ]
    have hlarge : ball (expIterate (k + 1) x) 8 ⊆
        Complex.exp '' ball (expIterate k x) 1 := by
      simpa only [one_mul, expIterate_succ] using
        exp_ball_real_expands (expIterate_real_orbit hx k).1
          (by norm_num : (0 : ℝ) < 1) le_rfl (by norm_num : (0 : ℝ) ≤ 8)
          ((le_max_left _ _).trans hxk)
    have hxreal : (((expIterate (k + 1) x).re : ℝ) : ℂ) = expIterate (k + 1) x := by
      apply Complex.ext
      · rfl
      · simpa using (expIterate_real_orbit hx (k + 1)).1.symm
    have hcover := hρ (expIterate (k + 1) x).re hxnext hw
    rw [hxreal] at hcover
    obtain ⟨a, ha, haw⟩ := hcover
    obtain ⟨b, hb, hba⟩ := hlarge ha
    obtain ⟨c, hc, hcb⟩ := hN k hkN hb
    refine ⟨c, hc, ?_⟩
    calc
      expIterate (k + 3) c = expIterate 2 (Complex.exp (expIterate k c)) := by
        rw [show k + 3 = 2 + (k + 1) by omega]
        exact (Function.iterate_add_apply exponentialMap 2 (k + 1) c).trans
          (congrArg (expIterate 2) (expIterate_succ k c))
      _ = w := by rw [hcb, hba, haw]
  refine ⟨max N d + 3, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa only [show max N d + 3 + k = (max N d + k) + 3 by omega] using
    htail (max N d + k) (Nat.le_add_right _ _)
end ExponentialJuliaSetMisiurewicz
