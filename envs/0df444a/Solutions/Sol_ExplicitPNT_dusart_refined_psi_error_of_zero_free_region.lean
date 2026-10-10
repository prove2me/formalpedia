-- Prove2me | solution 1 for ExplicitPNT.dusart_refined_psi_error_of_zero_free_region
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T15:53:34.796499+00:00
-- url     : https://prove2.me/submissions/203799a1-46a0-496f-bafa-a26a9ec50558
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/- Proof sketch: the numerical comparison is proved separately; the analytic
   smoothing estimate is an explicit Open dependency. -/
import Mathlib
import Theorems.Thm_ExplicitPNT_dusart_smoothing_factor_comparison
import Theorems.Thm_ExplicitPNT_dusart_psi_error_with_smoothing_parameter

namespace DusartComparison

lemma log_two_pi_bounds : (3 / 2 : ℝ) ≤ Real.log (2 * Real.pi) ∧
    Real.log (2 * Real.pi) ≤ 7 := by
  have hp : 0 < 2 * Real.pi := by positivity
  have he : Real.exp (1 / 2 : ℝ) < 2 := by
    have hs : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have ht := Real.exp_one_lt_three
    have hz := Real.exp_pos (1 / 2 : ℝ)
    nlinarith
  have he3 : Real.exp (3 / 2 : ℝ) < 6 := by
    have hs : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
    rw [hs, Real.exp_add]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos (1 : ℝ),
      Real.exp_pos (1 / 2 : ℝ)]
  constructor
  · have ht : Real.exp (3 / 2 : ℝ) < Real.exp (Real.log (2 * Real.pi)) := by
      rw [Real.exp_log hp]
      linarith [Real.pi_gt_three]
    exact (Real.exp_lt_exp.mp ht).le
  · have hl := Real.log_le_sub_one_of_pos hp
    linarith [Real.pi_le_four]

end DusartComparison

theorem solution
    (R : ℝ) (hR : 0 < R)
    (hzero : ∀ s : ℂ, 2 * Real.pi < |s.im| →
      1 - 1 / (R * Real.log |s.im|) < s.re → riemannZeta s ≠ 0)
    (x : ℝ) (hx : 0 < x)
    (hX : max (836 / 100 : ℝ) (8 / R) < Real.sqrt (Real.log x / R)) :
    |Chebyshev.psi x - x| <
      x * Real.sqrt (8 / Real.pi) * Real.sqrt (Real.sqrt (Real.log x / R)) *
        Real.exp (-Real.sqrt (Real.log x / R)) *
        Real.sqrt (Real.sqrt
          (1 - (Real.log (2 * Real.pi) - 1 / 2) / Real.sqrt (Real.log x / R))) := by
  let X := Real.sqrt (Real.log x / R)
  have h8 : (8 : ℝ) ≤ X := by
    have hh : (836 / 100 : ℝ) < X :=
      lt_of_le_of_lt (le_max_left _ _) hX
    linarith
  have hXp : 0 < X := by linarith
  obtain ⟨ν, hν, hν1, hpsi⟩ :=
    ExplicitPNT.dusart_psi_error_with_smoothing_parameter R hR hzero x hx hX
  obtain ⟨hL, hL7⟩ := DusartComparison.log_two_pi_bounds
  have hcmp := ExplicitPNT.dusart_smoothing_factor_comparison
    X ν (Real.log (2 * Real.pi)) h8 hν.le hν1 hL hL7
  have hA : 0 < x * Real.sqrt (8 / Real.pi) * Real.sqrt X * Real.exp (-X) := by
    apply mul_pos
    · exact mul_pos (mul_pos hx (Real.sqrt_pos.2 (by positivity))) (Real.sqrt_pos.2 hXp)
    · exact Real.exp_pos _
  exact hpsi.trans (mul_lt_mul_of_pos_left hcmp hA)


