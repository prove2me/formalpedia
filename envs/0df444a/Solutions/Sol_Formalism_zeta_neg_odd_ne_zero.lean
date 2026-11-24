-- Prove2me | solution 1 for Formalism.zeta_neg_odd_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:46:33.99163+00:00
-- url     : https://prove2.me/submissions/d26eb183-d103-4be6-8f19-92443ea7d70f

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_RHofHalfPlane

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism
namespace Formalism
theorem _root_.solution (m : ℕ) : riemannZeta (-((2 * m + 1 : ℕ) : ℂ)) ≠ 0 := by
  set t : ℂ := ((2 * m + 2 : ℕ) : ℂ) with ht
  have htre : t.re = 2 * (m : ℝ) + 2 := by simp [ht]
  have ht1 : (1 : ℝ) < t.re := by rw [htre]; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hn : ∀ n : ℕ, t ≠ -n := by
    intro n hn
    have := congrArg Complex.re hn
    rw [htre] at this
    simp at this
    have h0 : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have ht1' : t ≠ 1 := by
    intro h1
    have := congrArg Complex.re h1
    rw [htre] at this
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hfe := riemannZeta_one_sub hn ht1'
  have hsub : (1 : ℂ) - t = -((2 * m + 1 : ℕ) : ℂ) := by
    rw [ht]; push_cast; ring
  rw [hsub] at hfe
  rw [hfe]
  have hcos : Complex.cos (Real.pi * t / 2) = ((Real.cos (((m + 1 : ℕ) : ℝ) * Real.pi) : ℝ) : ℂ) := by
    rw [ht]; push_cast; ring_nf
  have hpi : (2 * ((Real.pi : ℝ) : ℂ)) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_) ?_)
    (riemannZeta_ne_zero_of_one_lt_re ht1)
  · exact (cpow_ne_zero_iff).mpr (Or.inl hpi)
  · exact Complex.Gamma_ne_zero hn
  · rw [hcos, Real.cos_nat_mul_pi]
    push_cast
    exact pow_ne_zero _ (by norm_num)
end Formalism
