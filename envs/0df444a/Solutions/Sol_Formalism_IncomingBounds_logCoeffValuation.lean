-- Prove2me | solution 1 for Formalism.IncomingBounds.logCoeffValuation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:57.975901+00:00
-- url     : https://prove2.me/submissions/cdcf715b-a9c9-4f8a-8894-2f34f6ed2589

import Definitions.Def_Formalism_IncomingBounds_LemmaMNumerics
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
import Theorems.Thm_Formalism_IncomingBounds_num_one_add_four_mul_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution : LogCoeffVal := by
  intro l hl hl5 s hs
  haveI := Fact.mk hl
  have hdvd : l ^ padicValNat l s ∣ s := pow_padicValNat_dvd
  have hle : l ^ padicValNat l s ≤ s := Nat.le_of_dvd (by omega) hdvd
  have h5 : 5 ^ padicValNat l s ≤ l ^ padicValNat l s := Nat.pow_le_pow_left hl5 _
  have h4 := num_one_add_four_mul_le (padicValNat l s)
  have hN : 1 + 4 * padicValNat l s ≤ s := by omega
  have hR : (1 : ℝ) + 4 * (padicValNat l s : ℝ) ≤ s := by exact_mod_cast hN
  have hl5R : (5 : ℝ) ≤ l := by exact_mod_cast hl5
  have h14 : 1 / ((l : ℝ) - 1) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  linarith
end Formalism.IncomingBounds
