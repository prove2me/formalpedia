-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xnLam_anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:29.808939+00:00
-- url     : https://prove2.me/submissions/e0afb6e0-f487-4495-969b-402b7a5f7c09

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_interlace

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
theorem _root_.solution {n : ℕ} (lam sg : Fin n → ℕ) (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ))) :
    Antitone (xnLam lam) := by
  refine antitone_nat_of_succ_le fun q => ?_
  unfold xnLam
  by_cases h1 : q + 1 < n
  · have h0 : q < n := by omega
    rw [dif_pos h1, dif_pos h0]
    obtain ⟨ha, hb⟩ := xn_interlace lam sg hI ⟨q, h0⟩
    unfold nuNext at ha
    rw [dif_pos h1] at ha
    exact le_trans ha hb
  · rw [dif_neg h1]
    exact Nat.zero_le _
end Formalism.BranchingDeterminantCap
