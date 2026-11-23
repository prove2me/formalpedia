-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.volume_ratio_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:54.895609+00:00
-- url     : https://prove2.me/submissions/ba04d6b5-cf57-4d69-a773-f3598f29b2c7

import Definitions.Def_Formalism_FlagUnipotentLattices_UnitSumBound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ConstantProductFormula
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_volU_pos_minkowski_factorial_bounds
import Theorems.Thm_P2M_Formalism_HermitianLatticeCounting_P_volU_succ__cd99a22eae0a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.HermitianLatticeCounting.LocalIntegralStructure
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.LocalIntegralStructure.VolRatio := by
  intro k p
  induction p with
  | zero => simp [(volU_pos_minkowski_factorial_bounds k).ne']
  | succ p ih =>
    rw [← add_assoc, volU_succ', Finset.prod_Ico_succ_top (by omega)]
    have e : (p + 1) * k + (p + 1) * (p + 1 + 1) / 2 = (p * k + p * (p + 1) / 2) + (k + p + 1) := by
      have h1 : (p + 1) * (p + 1 + 1) = p * (p + 1) + 2 * (p + 1) := by ring
      rw [h1, Nat.add_mul_div_left _ _ (by norm_num)]; ring
    rw [e, pow_add _ (p * k + p * (p + 1) / 2), ← ih]
    have := volU_pos_minkowski_factorial_bounds k
    have h3 : ((k + p).factorial : ℝ) ≠ 0 := by positivity
    field_simp
end Formalism.HermitianLatticeCounting.P
