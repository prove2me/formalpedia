-- Prove2me | solution 1 for CCRuleCW.term_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:01:23.967077+00:00
-- url     : https://prove2.me/submissions/13e2f1ca-f1ec-4cd0-95e8-cb786515df6d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt
namespace CCRuleCW
theorem _root_.solution {N A Bc m n a b C₁ C₂ : ℝ} {D : ℕ} (hN : 1 ≤ N) (hB : 0 ≤ Bc) (hmn : m ≤ n)
    (_ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha : a ≤ C₁ * N ^ D) (hb : N ^ (A - Bc * m) * b ≤ C₂) :
    N ^ (A - D - Bc * n) * (a * b) ≤ max C₁ 0 * max C₂ 0 := by
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN
  have ha' : a ≤ max C₁ 0 * N ^ (D : ℝ) := by
    rw [Real.rpow_natCast]
    exact ha.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hN0.le _))
  have hx : N ^ (A - D - Bc * n) * N ^ (D : ℝ) = N ^ (A - Bc * m) * N ^ (-(Bc * (n - m))) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
    congr 1
    ring
  have h3 : N ^ (-(Bc * (n - m))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN (by nlinarith)
  have hE : 0 ≤ N ^ (A - D - Bc * n) := Real.rpow_nonneg hN0.le _
  have hP : 0 ≤ N ^ (A - Bc * m) * b := mul_nonneg (Real.rpow_nonneg hN0.le _) hb0
  calc N ^ (A - D - Bc * n) * (a * b)
      ≤ N ^ (A - D - Bc * n) * ((max C₁ 0 * N ^ (D : ℝ)) * b) := by
        apply mul_le_mul_of_nonneg_left _ hE
        exact mul_le_mul_of_nonneg_right ha' hb0
    _ = max C₁ 0 * ((N ^ (A - Bc * m) * b) * N ^ (-(Bc * (n - m)))) := by
        calc N ^ (A - D - Bc * n) * ((max C₁ 0 * N ^ (D : ℝ)) * b)
            = max C₁ 0 * ((N ^ (A - D - Bc * n) * N ^ (D : ℝ)) * b) := by ring
          _ = _ := by rw [hx]; ring
    _ ≤ max C₁ 0 * (max C₂ 0 * 1) := by
        apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
        exact mul_le_mul (hb.trans (le_max_left _ _)) h3 (Real.rpow_nonneg hN0.le _) (le_max_right _ _)
    _ = max C₁ 0 * max C₂ 0 := by ring
end CCRuleCW
