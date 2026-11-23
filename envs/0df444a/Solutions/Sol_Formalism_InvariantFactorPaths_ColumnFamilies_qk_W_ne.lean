-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qk_W_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:00.139319+00:00
-- url     : https://prove2.me/submissions/084638c8-1aeb-4bc1-8b6f-da81b58cdee7

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntSym
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QkDetExpand
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_Branch
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_WeylGT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntLam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT)
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) : vandermondeDenominator n ≠ 0 := by
  unfold vandermondeDenominator
  refine prod_ne_zero_iff.2 fun j _ => prod_ne_zero_iff.2 fun i hi => ?_
  have : (i : ℝ) < (j : ℝ) := by exact_mod_cast mem_range.1 hi
  exact sub_ne_zero.2 (ne_of_gt this)
end Formalism.InvariantFactorPaths.ColumnFamilies
