-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xn_cof_supported
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:47.076796+00:00
-- url     : https://prove2.me/submissions/680ff79e-893b-46c2-a9d8-a3ce4db57274

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_det_supported

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
theorem _root_.solution (ι : κ → Fin r) {p : ℕ} (hp : p + 1 ≤ n) (a : Fin p → κ) (j : Fin (p + 1)) :
    xnCof ι hp a j ∈ supported ℂ {v : Fin r × Fin n | ∃ i, v.1 = ι (a i)} := by
  unfold xnCof
  refine mul_mem (pow_mem (neg_mem (one_mem _)) _) (xn_det_supported _ _ fun i k => ?_)
  rw [Matrix.of_apply]
  first
  | exact (MvPolynomial.X_mem_supported (R := ℂ)).2 ⟨i, rfl⟩
  | exact MvPolynomial.X_mem_supported.mpr ⟨i, rfl⟩
end Formalism.BranchingDeterminantCap
