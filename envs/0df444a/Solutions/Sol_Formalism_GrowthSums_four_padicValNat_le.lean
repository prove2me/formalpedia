-- Prove2me | solution 1 for Formalism.GrowthSums.four_padicValNat_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:05.500901+00:00
-- url     : https://prove2.me/submissions/06611213-dcea-48cc-8d00-c7b5d771b36f

import Definitions.Def_Formalism_GrowthSums_StatementC
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_Harmonic
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_LogCoef
import Theorems.Thm_Formalism_GrowthSums_four_mul_add_two_le_three_mul_five_pow

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
theorem _root_.solution (p s : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hs : 1 ≤ s) :
    4 * padicValNat p s + 2 ≤ 3 * s := by
  have hv := four_mul_add_two_le_three_mul_five_pow (padicValNat p s)
  have h1 : 5 ^ padicValNat p s ≤ p ^ padicValNat p s := Nat.pow_le_pow_left hp5 _
  have h2 : p ^ padicValNat p s ≤ s := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  omega
end Formalism.GrowthSums
