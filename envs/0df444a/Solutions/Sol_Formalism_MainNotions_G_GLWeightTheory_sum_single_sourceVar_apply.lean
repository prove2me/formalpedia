-- Prove2me | solution 1 for Formalism.MainNotions.G.GLWeightTheory.sum_single_sourceVar_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:01:39.118789+00:00
-- url     : https://prove2.me/submissions/c5b63583-b91e-4085-8874-4cdf51865686

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_TwistSubEqMatrixSubst
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionX
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_sourceVar_fst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory
open Formalism.MainNotions.G
variable {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (a b : Fin n)
open Classical
namespace Formalism.MainNotions.G.GLWeightTheory
theorem _root_.solution (c : ι → ℕ) (v : ι × Fin n) :
    (∑ l : ι, Finsupp.single (sourceVar LL a b l) (c l)) v = if v = sourceVar LL a b v.1 then c v.1 else 0 := by
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single v.1]
  · rw [Finsupp.single_apply]
    by_cases h : v = sourceVar LL a b v.1
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (Ne.symm h), if_neg h]
  · intro l _ hl
    rw [Finsupp.single_apply, if_neg]
    intro h
    apply hl
    rw [← h, sourceVar_fst]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.MainNotions.G.GLWeightTheory
