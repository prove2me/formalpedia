-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_exp_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:41.996985+00:00
-- url     : https://prove2.me/submissions/6e2039d2-13b4-40c0-8f87-d03fedddd6e1

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DefsMod
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Lemmata_GeneralBFactSecondTer_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (b p : Fin n) :
    qa_exp I (b, p) = ∑ c : ↥(TCols mu), ∑ q : Fin (colH mu c),
      if qa_row I c q = b ∧ q.val = p.val then 1 else 0 := by
  simp only [qa_exp, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, Prod.mk.injEq, Fin.ext_iff,
    Fin.val_castLE]
end Formalism.InvariantFactorPaths.ColumnFamilies
