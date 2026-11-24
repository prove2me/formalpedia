-- Prove2me | solution 1 for Formalism.GM.MeanGammaLemmas.negLog_beta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:48.185811+00:00
-- url     : https://prove2.me/submissions/c31af897-53cd-441f-a5b1-4b0da953b3da

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_norm_nat
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_neg_logb_zpow_self
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.MeanGammaLemmas
open Finset
namespace Formalism.GM.MeanGammaLemmas
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] (M e z o S : ℕ) :
    -Real.logb p ‖(p : ℚ_[p]) ^ M * ((e.factorial * (z + e).choose e : ℕ) : ℚ_[p]) /
        ((o.factorial * S.factorial : ℕ) : ℚ_[p])‖ =
      (M : ℝ) + padicValNat p e.factorial + padicValNat p ((z + e).choose e) -
        padicValNat p o.factorial - padicValNat p S.factorial := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hA : e.factorial * (z + e).choose e ≠ 0 :=
    Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.choose_pos (Nat.le_add_left e z)).ne'
  have hB : o.factorial * S.factorial ≠ 0 :=
    Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  rw [norm_div, norm_mul, norm_pow, Padic.norm_p, norm_nat p _ hA, norm_nat p _ hB,
    padicValNat.mul (Nat.factorial_ne_zero _) (Nat.choose_pos (Nat.le_add_left e z)).ne',
    padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
  rw [show ((p : ℝ)⁻¹) ^ M = (p : ℝ) ^ (-(M : ℤ)) by rw [zpow_neg, zpow_natCast, inv_pow],
    ← zpow_add₀ hp0.ne', ← zpow_sub₀ hp0.ne', neg_logb_zpow_self]
  simp only [Int.cast_sub, Int.cast_add, Int.cast_neg, Int.cast_natCast, Nat.cast_add]
  ring
end Formalism.GM.MeanGammaLemmas
