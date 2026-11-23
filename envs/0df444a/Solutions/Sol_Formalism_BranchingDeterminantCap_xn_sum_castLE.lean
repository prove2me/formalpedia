-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xn_sum_castLE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:33.795233+00:00
-- url     : https://prove2.me/submissions/71d208ac-1ceb-4660-a66c-134b314dbe41

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
theorem _root_.solution {A : Type*} [AddCommMonoid A] {k : ℕ} (hk : k ≤ r) (g : Fin r → A)
    (hg : ∀ b : Fin r, k ≤ b.val → g b = 0) :
    ∑ b : Fin k, g (Fin.castLE hk b) = ∑ b : Fin r, g b := by
  classical
  rw [← Finset.sum_image (s := Finset.univ) (g := Fin.castLE hk) (f := g)
    (by intro x _ y _ hxy; exact Fin.castLE_injective hk hxy)]
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro b _ hb
  apply hg
  by_contra hlt
  push_neg at hlt
  exact hb (Finset.mem_image.2 ⟨⟨b.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
end Formalism.BranchingDeterminantCap
