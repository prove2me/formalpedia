-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xnInv_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:29.738933+00:00
-- url     : https://prove2.me/submissions/75bcc6b8-2788-4f84-ab1f-b42ee8d2df9e

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
variable {r n : ℕ}
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {k : ℕ} {μ : ℕ → ℕ} {x h : MvPolynomial (Fin r × Fin n) ℂ} (H : xnInv k μ x h) :
    xnInv (k + 1) μ x h := by
  exact { supp := fun q hq => H.supp q (by omega), xm := H.xm, hm := H.hm,
          hs := MvPolynomial.supported_mono
            (fun v hv => by simp only [Set.mem_setOf_eq] at hv ⊢; omega) H.hs,
          le := H.le }
end Formalism.BranchingDeterminantCap
