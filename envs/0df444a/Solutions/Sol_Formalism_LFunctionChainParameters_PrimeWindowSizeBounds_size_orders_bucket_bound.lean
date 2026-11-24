-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.size_orders_bucket_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:27:19.458782+00:00
-- url     : https://prove2.me/submissions/cbf01cdf-df0f-4829-bea5-ae825f9fb241

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_facts
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_scale2
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_log_two_le_one_alt
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_xpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Kpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_zpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Xpos__19fb6e
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_b0
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_rpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_xr
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Kzr0
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_div_le_div_sq_of_le
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_npos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_log_le_alt
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Kzr_sg
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_close_sg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr
namespace Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
theorem _root_.solution : SizeOrders := by
  intro P e K m T hW hL hm hT
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  unfold tOrders unitU
  have h9 := F.xpos; have h11 := F.Kpos; have hb := F.b0; have hz := F.zpos; have hr0 := F.rpos
  have hM1 : 1 ≤ max P.Y P.Xpp := F.Y1.trans (le_max_left _ _)
  have hlM : Real.log (max P.Y P.Xpp) ≤ 3 * z := by
    rcases max_choice P.Y P.Xpp with h | h <;> rw [h]
    · have hY0 : 0 < P.Y := by linarith [F.Y1]
      have a2 : Real.log P.Y ≤ Real.log (2 * X) := Real.log_le_log hY0 F.YX
      rw [Real.log_mul (by norm_num) F.Xpos.ne', F.logX] at a2
      linarith [log_two_le_one_alt, F.uz, F.z1]
    · rw [F.hXpp, Real.log_mul (mul_pos h9 F.npos).ne' F.Xpos.ne', Real.log_mul h9.ne' F.npos.ne', F.logX]
      have a1 : Real.log P.n ≤ z := F.log_le_alt F.npos F.nE
      have a2 : Real.log P.x ≤ z := F.lxz
      linarith [F.uz]
  generalize max P.Y P.Xpp = M at hM1 hlM ⊢
  have q1 := F.n2x; have q2 := F.n2n
  have q0 : (1 : ℝ) ≤ 2 ^ P.e₂ := one_le_pow₀ (by norm_num)
  generalize (2 : ℝ) ^ P.e₂ = n at q0 q1 q2 ⊢
  have qp : 0 < n := by linarith
  have hnY1 : 1 ≤ n * M := one_le_mul_of_one_le_of_one_le q0 hM1
  have hL0 : 0 ≤ Real.log (n * M) := Real.log_nonneg hnY1
  have hL3 : Real.log (n * M) ≤ 4 * z := by
    rw [Real.log_mul qp.ne' (by linarith)]
    have a1 : Real.log n ≤ z := F.log_le_alt qp (q2.trans F.nE)
    linarith
  have hJ0 : (0 : ℝ) ≤ P.Jo := Nat.cast_nonneg _
  have hJ := F.Joz
  have hC0 := F.Co0; have hCK := F.CoK
  have c1 : P.Cord * P.Jo * Real.log (n * M) ^ 2 / n ≤ K * z * (4 * z) ^ 2 * P.x⁻¹ ^ 2 := by
    refine F.div_le_div_sq_of_le ?_ (by positivity) q1
    gcongr
  have key : 4 * P.a * (P.Cord * P.Jo * Real.log (n * M) ^ 2 / n) ≤ sg P K * P.b := by
    rw [F.ha]
    calc 4 * (P.x * P.b) * (P.Cord * P.Jo * Real.log (n * M) ^ 2 / n)
        ≤ 4 * (P.x * P.b) * (K * z * (4 * z) ^ 2 * P.x⁻¹ ^ 2) := by gcongr
      _ = P.b * (64 / 100 * (P.x * P.x⁻¹)) * (100 * K * z ^ 3 * P.x⁻¹) := by ring
      _ ≤ sg P K * P.b := by
          rw [F.xr]
          exact F.close_sg (by norm_num) (by norm_num) (F.Kzr0 3) (F.Kzr_sg (by norm_num))
  have := scale2 hm hT key
  linarith
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
