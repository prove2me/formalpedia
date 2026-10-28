-- Prove2me | solution 1 for FunctionalInequalities.Analysis.deriv_comp_sub_div_and_deriv_deriv_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:32:19.380456+00:00
-- url     : https://prove2.me/submissions/2114777f-fb5f-4d2d-bf2d-4cb014b66eb0

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_Profile

open scoped ContDiff
/-- **Affine rescaling of derivatives** (Letwin Lemma A.4, p. 17, `η(W/R)` with `W = φ − c`): for arbitrary `f`, `c`,
`R`, `t`, `(f((· − c)/R))′(t) = R⁻¹ f′((t − c)/R)` and `(f((· − c)/R))″(t) = (R⁻¹)² f″((t − c)/R)`, with Lean's
total-derivative conventions (no differentiability or `R ≠ 0` hypothesis). -/
theorem solution (f : ℝ → ℝ) (c R t : ℝ) :
    deriv (fun s => f ((s - c) / R)) t = R⁻¹ * deriv f ((t - c) / R) ∧
      deriv (deriv (fun s => f ((s - c) / R))) t = (R⁻¹) ^ 2 * deriv (deriv f) ((t - c) / R) := by
    have hcomp : ∀ (g : ℝ → ℝ) (x : ℝ),
        deriv (fun s => g ((s - c) / R)) x =
          R⁻¹ * deriv g ((x - c) / R) := by
      intro g x
      calc
        deriv (fun s => g ((s - c) / R)) x =
            deriv (fun s => g (R⁻¹ * (s - c))) x := by
              apply congrArg (fun q : ℝ → ℝ => deriv q x)
              funext s
              simp [div_eq_mul_inv, mul_comm]
        _ = deriv (fun u => g (R⁻¹ * u)) (x - c) := by
              exact deriv_comp_sub_const (fun u : ℝ => g (R⁻¹ * u)) c x
        _ = R⁻¹ * deriv g (R⁻¹ * (x - c)) := by
              rw [deriv_comp_mul_left]; ring
        _ = R⁻¹ * deriv g ((x - c) / R) := by
              simp [div_eq_mul_inv, mul_comm]
    constructor
    · exact hcomp f t
    · have hfun :
          deriv (fun s => f ((s - c) / R)) =
            (fun s => R⁻¹ * deriv f ((s - c) / R)) := by
        funext s
        exact hcomp f s
      rw [hfun]
      calc
        deriv (fun s => R⁻¹ * deriv f ((s - c) / R)) t =
            R⁻¹ * deriv (fun s => deriv f ((s - c) / R)) t := by
              rw [deriv_const_mul_field']
        _ = R⁻¹ * (R⁻¹ * deriv (deriv f) ((t - c) / R)) := by
              rw [hcomp (deriv f) t]
        _ = (R⁻¹) ^ 2 * deriv (deriv f) ((t - c) / R) := by
              ring
