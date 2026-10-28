-- Prove2me | solution 1 for GaussianMatrix.incomplete_gamma_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T19:43:23.400995+00:00
-- url     : https://prove2.me/submissions/00843605-ae4b-4af3-9da8-bd073af40d16

import Mathlib
import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

open Filter Topology Set Real in
theorem solution {a x : ℝ} (ha : -1 < a) (hx : 0 ≤ x) :
    (∫ t in Set.Ioi x, t ^ (a + 1) * Real.exp (-t / 2))
      = 2 * x ^ (a + 1) * Real.exp (-x / 2)
        + 2 * (a + 1) * (∫ t in Set.Ioi x, t ^ a * Real.exp (-t / 2)) := by
  have hsub : Ioi x ⊆ Ioi (0:ℝ) := fun t ht => lt_of_le_of_lt hx ht
  have hint : ∀ s : ℝ, -1 < s → IntegrableOn (fun t : ℝ => t ^ s * Real.exp (-t / 2)) (Ioi x) := by
    intro s hs
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (b := 1/2) hs one_pos (by norm_num)
    refine (h.mono_set hsub).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one]; congr 2; ring
  have hu : ∀ t ∈ Ioi x, HasDerivAt (fun t : ℝ => t ^ (a + 1)) ((a + 1) * t ^ a) t := by
    intro t ht
    have := Real.hasDerivAt_rpow_const (x := t) (p := a + 1) (Or.inl (ne_of_gt (hsub ht)))
    simpa using this
  have hv : ∀ t ∈ Ioi x, HasDerivAt (fun t : ℝ => -2 * Real.exp (-t / 2)) (Real.exp (-t / 2)) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => -t / 2) (-1 / 2) t := by
      simpa using ((hasDerivAt_id t).neg).div_const 2
    have := (h1.exp).const_mul (-2)
    exact this.congr_deriv (by ring)
  have hcont : ContinuousAt (fun t : ℝ => t ^ (a + 1) * (-2 * Real.exp (-t / 2))) x := by
    apply ContinuousAt.mul
    · exact Real.continuousAt_rpow_const _ _ (Or.inr (by linarith))
    · fun_prop
  have h0 : Tendsto ((fun t : ℝ => t ^ (a + 1)) * (fun t => -2 * Real.exp (-t / 2))) (𝓝[>] x)
      (𝓝 (x ^ (a + 1) * (-2 * Real.exp (-x / 2)))) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hinf : Tendsto ((fun t : ℝ => t ^ (a + 1)) * (fun t => -2 * Real.exp (-t / 2))) atTop (𝓝 0) := by
    have := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a + 1) (1/2) (by norm_num)).const_mul (-2)
    rw [mul_zero] at this
    refine this.congr' (Eventually.of_forall fun t => ?_)
    simp only [Pi.mul_apply]; rw [show -t / 2 = -(1/2) * t by ring]; ring
  have huv' : IntegrableOn ((fun t : ℝ => t ^ (a + 1)) * fun t => Real.exp (-t / 2)) (Ioi x) :=
    hint (a + 1) (by linarith)
  have hu'v : IntegrableOn ((fun t : ℝ => (a + 1) * t ^ a) * fun t => -2 * Real.exp (-t / 2)) (Ioi x) := by
    refine IntegrableOn.congr_fun ((hint a ha).const_mul (-2 * (a + 1))) (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply]; ring
  have key := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h0 hinf
  rw [key]
  have : (∫ t in Ioi x, (a + 1) * t ^ a * (-2 * Real.exp (-t / 2)))
      = -(2 * (a + 1)) * ∫ t in Ioi x, t ^ a * Real.exp (-t / 2) := by
    rw [← integral_const_mul]; congr 1; funext t; ring
  rw [this]; ring
