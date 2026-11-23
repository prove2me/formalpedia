-- Prove2me | solution 1 for BroughanRH.psiSmallPower
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T18:36:38.187981+00:00
-- url     : https://prove2.me/submissions/2cc60ee5-68ca-4c47-aefa-555dc25360a8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_LandauCriterion_psi_error_of_riemannHypothesis

open Asymptotics Filter

theorem solution :
    ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO Filter.atTop (fun x : ℝ => Chebyshev.psi x - x) (fun x : ℝ => x^(1/2+ε)) := by
  intro ε hε
  obtain ⟨C, hC⟩ := LandauCriterion.psi_error_of_riemannHypothesis riemann_hypothesis
  -- log x ^ 2 = O(x^ε)
  have hlog : (fun x : ℝ => Real.log x ^ 2) =O[atTop] (fun x : ℝ => x ^ ε) := by
    have h := (isLittleO_log_rpow_atTop (show 0 < ε / 2 by linarith)).isBigO
    have h2 := h.mul h
    refine h2.congr' (Eventually.of_forall fun x => by ring) ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [← Real.rpow_add hx]; ring_nf
  have hsq : (fun x : ℝ => Real.sqrt x) =O[atTop] (fun x : ℝ => x ^ (1/2 : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [Real.sqrt_eq_rpow, one_mul]
  have hmain : (fun x : ℝ => Real.sqrt x * Real.log x ^ 2) =O[atTop] (fun x : ℝ => x ^ (1/2+ε)) := by
    refine (hsq.mul hlog).congr' (Eventually.of_forall fun x => rfl) ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [← Real.rpow_add hx]
  have h1 : (fun x : ℝ => Chebyshev.psi x - x) =O[atTop] (fun x : ℝ => Real.sqrt x * Real.log x ^ 2) := by
    refine IsBigO.of_bound |C| ?_
    filter_upwards [eventually_ge_atTop 2] with x hx
    have := hC x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    calc |Chebyshev.psi x - x| ≤ C * Real.sqrt x * Real.log x ^ 2 := this
      _ ≤ |C| * |Real.sqrt x * Real.log x ^ 2| := by
        rw [mul_assoc]
        exact (le_abs_self _).trans (by rw [abs_mul])
  exact h1.trans hmain
