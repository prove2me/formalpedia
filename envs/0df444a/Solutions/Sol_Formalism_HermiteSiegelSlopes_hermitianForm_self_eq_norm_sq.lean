-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.hermitianForm_self_eq_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:07.738321+00:00
-- url     : https://prove2.me/submissions/2f39d48c-e19a-4534-8b1d-42a3d19fbf7a

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
    (x : V) : Formalism.HermitianLatticesTheory.majAt b X v x x = ((Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 : ℝ) : ℂ) := by
  unfold Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Complex.conj_mul' _
end Formalism.HermiteSiegelSlopes
