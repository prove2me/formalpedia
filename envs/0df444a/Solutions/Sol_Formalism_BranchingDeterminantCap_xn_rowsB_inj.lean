-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xn_rowsB_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:02.626688+00:00
-- url     : https://prove2.me/submissions/85b491de-9ba5-4b7b-b938-bed284c9f2e5

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
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {n : ℕ} (i : Fin n) : Function.Injective (rowsB i) := by
  intro x y h
  have hx := x.isLt
  have hy := y.isLt
  have hi := i.isLt
  simp only [rowsB] at h
  apply Fin.ext
  split_ifs at h
  all_goals first
    | (simpa using h)
    | (have h' := congrArg Fin.val h
       simp only [Fin.val_last, Fin.val_mk] at h'
       omega)
    | omega
end Formalism.BranchingDeterminantCap
