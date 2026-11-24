-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_coeff_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:19.231338+00:00
-- url     : https://prove2.me/submissions/559b2ca8-2cce-4bde-8d75-d0983e434e7c

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnPtEmpty
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_prod_pt
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_off_inj
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_weight_col
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) (ν : Fin n → ℕ) (F : MvPolynomial (Fin n × Fin n) ℚ)
    (hF : IsWeightedHomogeneous (colW n n) F ν) (e : Fin n × Fin n →₀ ℕ) (he : LowerTri e)
    (hec : ∀ t : Fin n, ∑ a : Fin n, e (a, t) = ν t) :
    coeff (qn_off e) (aeval (qn_pt n (qn_low n)) F) = coeff e F := by
  classical
  rw [aeval_def, eval₂_eq', coeff_sum]
  simp only [algebraMap_eq, coeff_C_mul, qn_prod_pt]
  rw [Finset.sum_eq_single e]
  · rw [if_pos he, coeff_monomial, if_pos rfl, mul_one]
  · intro m hm hne
    split_ifs with hl
    · rw [coeff_monomial, if_neg, mul_zero]
      intro hoff
      apply hne
      refine qn_off_inj ν m e hl he ?_ hec hoff
      intro t
      rw [← lhwline_weight_col, hF (mem_support_iff.mp hm)]
    · simp
  · intro h
    rw [notMem_support_iff.mp h, zero_mul]
end Formalism.InvariantFactorPaths.ColumnFamilies
