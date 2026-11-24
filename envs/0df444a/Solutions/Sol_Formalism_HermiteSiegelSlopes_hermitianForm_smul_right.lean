-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.hermitianForm_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:08.272144+00:00
-- url     : https://prove2.me/submissions/61f4420d-35b5-4c92-9e2e-316a603b92d6

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset
noncomputable section
open Formalism Formalism.HermiteSiegelSlopes
open Formalism.HN
open scoped nonZeroDivisors
open IsDedekindDomain
variable {F E ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Fintype ι] [DecidableEq ι]
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
namespace Formalism.HermiteSiegelSlopes
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (a : K) (x y : V) : Formalism.HermitianLatticesTheory.majAt b X v x (a • y) =
      v.embedding a * Formalism.HermitianLatticesTheory.majAt b X v x y := by
  have hs : ∀ (a : K) (x : V), Formalism.HermitianLatticesTheory.fcoord b X v (a • x) = v.embedding a • Formalism.HermitianLatticesTheory.fcoord b X v x := by
    intro a x
    unfold Formalism.HermitianLatticesTheory.fcoord
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt]
  unfold Formalism.HermitianLatticesTheory.majAt
  rw [hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
end Formalism.HermiteSiegelSlopes
