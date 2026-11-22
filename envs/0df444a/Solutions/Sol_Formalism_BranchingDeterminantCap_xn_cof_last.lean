-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xn_cof_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:59.692261+00:00
-- url     : https://prove2.me/submissions/d5e0e1e7-987c-4640-8801-19bb3d442df1

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
theorem _root_.solution (ι : κ → Fin r) {p : ℕ} (hp : p + 1 ≤ n) (a : Fin p → κ) :
    xnCof ι hp a (Fin.last p) = initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp) := by
  unfold xnCof initMinor
  rw [Fin.val_last, (Even.neg_one_pow ⟨p, rfl⟩ : ((-1 : MvPolynomial (Fin r × Fin n) ℂ)) ^ (p + p) = 1),
    one_mul]
  congr 1
  refine Matrix.ext fun i k => ?_
  simp only [Matrix.of_apply, Function.comp_apply, Fin.succAbove_last]
  rfl
end Formalism.BranchingDeterminantCap
