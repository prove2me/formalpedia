-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xn_lap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:27:02.824338+00:00
-- url     : https://prove2.me/submissions/fdcd908b-d841-45d5-b494-c5cec70cd324

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
variable {r n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (ι : κ → Fin r) {p : ℕ} (hp : p + 1 ≤ n) (a : Fin p → κ) (b : κ) :
    initMinor ℂ (ι ∘ (Fin.snoc a b : Fin (p + 1) → κ)) hp =
      ∑ j, X (ι b, Fin.castLE hp j) * xnCof ι hp a j := by
  unfold initMinor xnCof
  rw [Matrix.det_succ_row _ (Fin.last p)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.submatrix, Matrix.of_apply, Function.comp_apply, Fin.snoc_last, Fin.val_last,
    Fin.succAbove_last, Fin.snoc_castSucc]
  ring
end Formalism.BranchingDeterminantCap
