-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.BoxTail.tail_num
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:35.709102+00:00
-- url     : https://prove2.me/submissions/88edeaf9-6b80-4269-875f-12ae7d326caa

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailNum
import Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_num_rpow
import Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_num_alg
import Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_num_third
import Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_num_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail
namespace Formalism.HermitianLattices.Ext.BoxTail
theorem _root_.solution (ε K : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hK : 0 ≤ K) : ∃ x₀ : ℝ, 3 ≤ x₀ ∧
    ∀ x Q : ℝ, x₀ ≤ x → 0 < Q → x ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ x ^ (ε / 4) →
      x * ((K * Real.log Q * (Real.log Q * (1 / x ^ 2) * (x ^ 400) ^ (1 - 1 / 400 + ε / 1600) + (x ^ 400) ^ 2 / Q)
          + x ^ 400 * (1 / x ^ 2) * (x ^ 400 * (1 / x ^ 2) + 1) * Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2)) / x ^ 400)
          / (x ^ 400 * (1 / x ^ 2))) ≤ x ^ ε := by
  have hq : 0 < ε / 4 := by positivity
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      K * (x ^ 404 * Real.exp (-(x ^ (ε / 6)))) ≤ 1 / 3 ∧ K + 803 ≤ x ^ (ε / 4) :=
    (tail_num_exp ε K hε).and
      ((tendsto_rpow_atTop hq).eventually (Filter.eventually_ge_atTop (K + 803)))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max N 3, le_max_right _ _, ?_⟩
  intro x Q hx hQ hlo hhi
  have hxN : N ≤ x := le_trans (le_max_left _ _) hx
  have hx3 : 3 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  obtain ⟨hexp, hy⟩ := hN x hxN
  rw [tail_num_rpow x ε hx0, tail_num_alg x Q K (Real.log Q) (x ^ (ε / 4))
    (Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2))) hx0 hQ]
  set y := x ^ (ε / 4) with hydef
  set l := Real.log Q with hldef
  have hs0 : 0 < x ^ (ε / 6) := Real.rpow_pos_of_pos hx0 _
  have hl0 : 0 ≤ l := by linarith
  have hy0 : 0 ≤ y := by linarith
  have ht1 : K * l ^ 2 * y ≤ K * y ^ 3 := by
    have : l ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hl0 hhi 2
    have h' : l ^ 2 * y ≤ y ^ 2 * y := mul_le_mul_of_nonneg_right this hy0
    calc K * l ^ 2 * y = K * (l ^ 2 * y) := by ring
      _ ≤ K * (y ^ 2 * y) := mul_le_mul_of_nonneg_left h' hK
      _ = K * y ^ 3 := by ring
  have hyx : y ≤ x := by
    have := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith : ε / 4 ≤ 1)
    rwa [Real.rpow_one] at this
  have hlx : l ≤ x := le_trans hhi hyx
  have hQinv : 1 / Q ≤ Real.exp (-(x ^ (ε / 6))) := by
    have hQe : Real.exp (x ^ (ε / 6)) ≤ Q := by
      calc Real.exp (x ^ (ε / 6)) ≤ Real.exp l := Real.exp_le_exp.2 hlo
        _ = Q := Real.exp_log hQ
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos _) hQe
  have ht2 : K * (l * x ^ 403 / Q) ≤ 1 / 3 := by
    have hin : l * x ^ 403 / Q ≤ x ^ 404 * Real.exp (-(x ^ (ε / 6))) := by
      calc l * x ^ 403 / Q = (l * x ^ 403) * (1 / Q) := by ring
        _ ≤ (x * x ^ 403) * Real.exp (-(x ^ (ε / 6))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hlx (by positivity)) hQinv
            (by positivity) (by positivity)
        _ = x ^ 404 * Real.exp (-(x ^ (ε / 6))) := by ring
    exact le_trans (mul_le_mul_of_nonneg_left hin hK) hexp
  have ht3 := tail_num_third x hx3
  have hpow : x ^ ε = y * y * y * y := by
    rw [hydef, ← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    congr 1
    ring
  have hy1 : 803 ≤ y := by linarith
  have hy3 : y ≤ y ^ 3 := by nlinarith
  have hfin : K * y ^ 3 + 1 / 3 + 802 ≤ y * y * y * y := by
    have : (K + 803) * y ^ 3 ≤ y * y ^ 3 :=
      mul_le_mul_of_nonneg_right hy (by positivity)
    nlinarith
  rw [hpow]
  linarith
end Formalism.HermitianLattices.Ext.BoxTail
