-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.hermitianForm_add_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:07.024459+00:00
-- url     : https://prove2.me/submissions/37c27064-55d9-48df-8560-e0e661bf8949

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
    (x y z : V) : Formalism.HermitianLatticesTheory.majAt b X v (x + y) z =
      Formalism.HermitianLatticesTheory.majAt b X v x z + Formalism.HermitianLatticesTheory.majAt b X v y z := by
  have hf : ∀ x y : V, Formalism.HermitianLatticesTheory.fcoord b X v (x + y) = Formalism.HermitianLatticesTheory.fcoord b X v x + Formalism.HermitianLatticesTheory.fcoord b X v y := by
    intro x y
    unfold Formalism.HermitianLatticesTheory.fcoord
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt]
  unfold Formalism.HermitianLatticesTheory.majAt
  rw [hf]
  simp [add_mul, Finset.sum_add_distrib]
end Formalism.HermiteSiegelSlopes
