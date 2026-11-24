-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.cappedGainBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:23.187781+00:00
-- url     : https://prove2.me/submissions/ae28d7ec-afac-4d59-800d-47095d95f71c

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_PathBasisOfCount
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_QuadraticExponentIdentity
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ABArith
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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : BCore := by
  intro n p TT TTodd al cap de v paid i E hp hsub hal hcap hi0 hiE hv hpaid hodd
  have hp0 : 0 < p := by linarith
  have hsplit : ∑ s ∈ TT, ∑ e ∈ E, i s e =
      ∑ s ∈ TT \ TTodd, ∑ e ∈ E, i s e + ∑ s ∈ TTodd, ∑ e ∈ E, i s e :=
    (Finset.sum_sdiff hsub).symm
  have hodd' : ∑ s ∈ TTodd, ∑ e ∈ E, i s e ≤
      ∑ s ∈ TTodd, ∑' e : ℕ,
        min (al s / p ^ (2 * e + 1)) (cap (s + ((2 * e + 1 : ℕ) : ZMod n))) := by
    apply Finset.sum_le_sum
    intro s hs
    have hsum := Formalism.GrowthSums.summable_min_div_pow_two_mul_add_one p hp (al s) (hal s) cap hcap s
    calc ∑ e ∈ E, i s e
        ≤ ∑ e ∈ E, min (al s / p ^ (2 * e + 1)) (cap (s + ((2 * e + 1 : ℕ) : ZMod n))) :=
          Finset.sum_le_sum (fun e _ => hodd s hs e)
      _ ≤ _ := hsum.sum_le_tsum E
          (fun e _ => le_min (div_nonneg (hal s) (pow_nonneg hp0.le _)) (hcap _))
  unfold gainG
  linarith
end Formalism.InvariantFactorPaths.G7
