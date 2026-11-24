-- Prove2me | solution 1 for Formalism.GrowthSums.cappedGainSubLE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:05.13904+00:00
-- url     : https://prove2.me/submissions/11a313bf-a22d-4187-8fbd-57e6aa442231

import Definitions.Def_Formalism_GrowthSums_StatementG
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_PathBasisOfCount
import Theorems.Thm_Formalism_GrowthSums_summable_min_div_pow_two_mul_add_one

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
open Finset
open Formalism Formalism.GrowthSums
namespace Formalism.GrowthSums
theorem _root_.solution : CappedGainSubLE := by
  intro n p TT TTodd al cap de v i₀ i E hp hsub hal hcap hi hiE h1 h2 h3
  unfold gainG
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hsplit : ∑ s ∈ TT, ∑ e ∈ E, i s e =
      ∑ s ∈ TT \ TTodd, ∑ e ∈ E, i s e + ∑ s ∈ TTodd, ∑ e ∈ E, i s e :=
    (Finset.sum_sdiff hsub).symm
  have hodd : ∑ s ∈ TTodd, ∑ e ∈ E, i s e ≤
      ∑ s ∈ TTodd, ∑' e : ℕ, min (al s / p ^ (2 * e + 1)) (cap (s + ((2 * e + 1 : ℕ) : ZMod n))) := by
    refine Finset.sum_le_sum fun s hs => ?_
    refine (Finset.sum_le_sum fun e _ => h3 s hs e).trans ?_
    exact Summable.sum_le_tsum E
      (fun e _ => le_min (div_nonneg (hal s) (pow_nonneg hp0.le _)) (hcap _))
      (summable_min_div_pow_two_mul_add_one p hp (al s) (hal s) cap hcap s)
  linarith
end Formalism.GrowthSums
