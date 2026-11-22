-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xn_interlace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:27:03.092587+00:00
-- url     : https://prove2.me/submissions/0d6bb44b-fea5-4049-b0b3-d3bbc8d9233a

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
theorem _root_.solution {n : ℕ} (lam sg : Fin n → ℕ) (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ)))
    (i : Fin n) : nuNext lam i ≤ sg i ∧ sg i ≤ lam i := by
  obtain ⟨h1, h2⟩ := hI i
  have hi := i.isLt
  simp only [lamZ, Fin.coe_castSucc, Fin.val_succ] at h1 h2
  rw [dif_pos hi] at h1
  unfold nuNext
  constructor
  · split_ifs with hh
    · rw [dif_pos hh] at h2
      exact_mod_cast h2
    · exact Nat.zero_le _
  · exact_mod_cast h1
end Formalism.BranchingDeterminantCap
