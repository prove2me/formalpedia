-- Prove2me | solution 1 for DiazModulus.schwarz_order_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T06:21:28.368315+00:00
-- url     : https://prove2.me/submissions/3c610f0b-16d4-4eef-94f1-6d3ac03d9a65

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # Schwarz lemma with a zero of order T at the origin (DALAG Lemma 2.4)

Let `F` be entire with a zero of order at least `T` at `0`, and `‖F‖ ≤ B` on the circle
`‖z‖ = R` with `R ≥ 1`. By `natCast_le_analyticOrderAt` there is `g`, analytic at `0`, with
`F z = z ^ T • g z` near `0`. The function `G z = F z / z ^ T` (and `G 0 = g 0`) agrees with `g`
near `0`, hence is entire. On the circle `‖G z‖ = ‖F z‖ / R ^ T ≤ B / R ^ T`, so the maximum
modulus principle on the disc `‖z‖ < R` (`Complex.norm_le_of_forall_mem_frontier_norm_le`)
gives `‖G 1‖ ≤ B / R ^ T`, since `1` lies in the closed disc. Finally `G 1 = F 1`.
-/

namespace C14_A5
open DiazModulus

/-- The quotient `F z / z ^ T`, patched at `0`. -/
noncomputable def quot (F g : ℂ → ℂ) (T : ℕ) (z : ℂ) : ℂ := if z = 0 then g 0 else F z / z ^ T

theorem quot_differentiable (F g : ℂ → ℂ) (hF : Differentiable ℂ F) (T : ℕ)
    (hg : AnalyticAt ℂ g 0) (hFg : ∀ᶠ z in nhds (0 : ℂ), F z = (z - 0) ^ T • g z) :
    Differentiable ℂ (quot F g T) := by
  intro z
  by_cases hz : z = 0
  · subst hz
    have heq : quot F g T =ᶠ[nhds 0] g := by
      filter_upwards [hFg] with w hw
      by_cases hw0 : w = 0
      · simp [quot, hw0]
      · simp only [quot, hw0, if_false, sub_zero, smul_eq_mul] at hw ⊢
        rw [hw]; field_simp
    exact (hg.differentiableAt).congr_of_eventuallyEq heq
  · have heq : quot F g T =ᶠ[nhds z] fun w => F w / w ^ T := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      simp [quot, hw]
    refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
    exact (hF z).div ((differentiableAt_id).pow T) (pow_ne_zero _ hz)

end C14_A5

open DiazModulus C14_A5 in
theorem solution (F : ℂ → ℂ) (hF : Differentiable ℂ F) (T : ℕ)
    (hT : (T : ℕ∞) ≤ analyticOrderAt F 0) (R B : ℝ) (hR : 1 ≤ R)
    (hB : ∀ z : ℂ, ‖z‖ = R → ‖F z‖ ≤ B) : ‖F 1‖ ≤ R ^ (-(T : ℤ)) * B := by
  have hFa : AnalyticAt ℂ F 0 := hF.analyticAt 0
  obtain ⟨g, hg, hFg⟩ := (natCast_le_analyticOrderAt hFa).mp hT
  have hG := quot_differentiable F g hF T hg hFg
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hRT : 0 < R ^ T := pow_pos hR0 T
  have hmax : ‖quot F g T 1‖ ≤ B / R ^ T := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := Metric.ball (0 : ℂ) R)
      Metric.isBounded_ball hG.diffContOnCl ?_ ?_
    · intro z hz
      rw [frontier_ball (0 : ℂ) hR0.ne', mem_sphere_zero_iff_norm] at hz
      have hz0 : z ≠ 0 := by
        intro h; rw [h, norm_zero] at hz; exact hR0.ne' hz.symm
      simp only [quot, hz0, if_false, norm_div, norm_pow, hz]
      exact div_le_div_of_nonneg_right (hB z hz) hRT.le
    · rw [closure_ball (0 : ℂ) hR0.ne', Metric.mem_closedBall, dist_zero_right, norm_one]
      exact hR
  have h1 : quot F g T 1 = F 1 := by simp [quot]
  rw [h1] at hmax
  rw [zpow_neg, zpow_natCast, inv_mul_eq_div]
  exact hmax
