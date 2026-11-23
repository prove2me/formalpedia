-- Prove2me | solution 1 for Formalism.GrowthSums.summable_min_div_pow_two_mul_add_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:24.410921+00:00
-- url     : https://prove2.me/submissions/e56932a2-e4d5-4ba2-92ff-ce884efe31d6

import Definitions.Def_Formalism_GrowthSums_StatementG
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_PathBasisOfCount

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
theorem _root_.solution {n : ℕ} (p : ℝ) (hp : 1 < p) (a : ℝ) (ha : 0 ≤ a)
    (cap : ZMod n → ℝ) (hcap : ∀ s, 0 ≤ cap s) (s : ZMod n) :
    Summable (fun e : ℕ => min (a / p ^ (2 * e + 1)) (cap (s + ((2 * e + 1 : ℕ) : ZMod n)))) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hq0 : 0 ≤ (p ^ 2)⁻¹ := inv_nonneg.mpr (by positivity)
  have hq1 : (p ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hp two_ne_zero)
  have hgeom : Summable (fun e : ℕ => a / p * ((p ^ 2)⁻¹) ^ e) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left (a / p)
  refine Summable.of_nonneg_of_le (fun e => le_min (div_nonneg ha (pow_nonneg hp0.le _)) (hcap _))
    (fun e => (min_le_left _ _).trans (le_of_eq ?_)) hgeom
  rw [inv_pow, ← pow_mul, pow_succ]
  field_simp
end Formalism.GrowthSums
