-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.logIterate_real_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:39.736629+00:00
-- url     : https://prove2.me/submissions/591c95f8-66df-415d-8491-acc10cf06f2d

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
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_log_lipschitz_real_ball
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_log_maps_real_ball
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
theorem _root_.solution {x : ℂ} (hx : x.im = 0) (hx10 : 10 ≤ x.re) (n : ℕ) :
    logIterate n (expIterate n x) = x ∧
    MapsTo (logIterate n) (ball (expIterate n x) 8) (ball x 8) ∧
    LipschitzOnWith ((1 / 2 : ℝ≥0) ^ n) (logIterate n) (ball (expIterate n x) 8) ∧
    ∀ z ∈ ball (expIterate n x) 8, expIterate n (logIterate n z) = z := by
  -- Each principal logarithm stays in the preceding real-centred disk and halves distances.
  induction n with
  | zero =>
      refine ⟨rfl, fun z hz => hz, ?_, fun z _ => rfl⟩
      simpa using (LipschitzWith.id.lipschitzOnWith : LipschitzOnWith 1 id (ball x 8))
  | succ n ih =>
      have hyn := (expIterate_real_orbit hx n).1
      have hy10 : 10 ≤ (expIterate n x).re := by
        linarith [(expIterate_real_orbit hx n).2, Nat.cast_nonneg (α := ℝ) n]
      have hmaps := log_maps_real_ball hyn hy10
      have hlip := log_lipschitz_real_ball hyn hy10
      have hlog : Complex.log (expIterate (n + 1) x) = expIterate n x := by
        rw [expIterate_succ]
        exact Complex.log_exp (by rw [hyn]; linarith [Real.pi_pos])
          (by rw [hyn]; exact Real.pi_pos.le)
      have hli : logIterate (n + 1) = logIterate n ∘ Complex.log :=
        Function.iterate_succ Complex.log n
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hli, comp_apply, hlog, ih.1]
      · simpa only [expIterate_succ, hli] using ih.2.1.comp hmaps
      · simpa only [expIterate_succ, hli, pow_succ] using ih.2.2.1.comp hlip hmaps
      · intro z hz
        have hzin := hmaps (by simpa only [expIterate_succ] using hz)
        have hz0 : z ≠ 0 := by
          intro heq
          subst z
          have hz' : ‖expIterate (n + 1) x‖ < 8 := by simpa [mem_ball, dist_eq_norm] using hz
          have hreal := (expIterate_real_orbit hx (n + 1)).2
          have hnorm := Complex.re_le_norm (expIterate (n + 1) x)
          linarith [Nat.cast_nonneg (α := ℝ) (n + 1)]
        rw [hli, comp_apply, expIterate_succ, ih.2.2.2 _ hzin, Complex.exp_log hz0]
end ExponentialJuliaSetMisiurewicz
