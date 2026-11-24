-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_prod_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:42.431946+00:00
-- url     : https://prove2.me/submissions/ac98408b-6d6f-432d-94f4-31cbb74e7461

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnPtEmpty
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
theorem _root_.solution (n : ℕ) (m : Fin n × Fin n →₀ ℕ) :
    (∏ i, qn_pt n (qn_low n) i ^ m i) = open Classical in if LowerTri m then monomial (qn_off m) 1 else 0 := by
  classical
  split_ifs with h
  · rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
    refine Finset.prod_congr rfl fun i _ => ?_
    obtain ⟨a, c⟩ := i
    rcases lt_trichotomy a c with hac | hac | hac
    · have h0 : m (a, c) = 0 := h a c hac
      have h1 : ¬ c < a := not_lt.mpr hac.le
      simp [h0, qn_off, Finsupp.filter_apply, h1]
    · subst hac
      simp [qn_pt, qn_low, qn_off, Finsupp.filter_apply]
    · have h1 : a ≠ c := ne_of_gt hac
      simp [qn_pt, qn_low, qn_off, Finsupp.filter_apply, hac, h1]
  · unfold LowerTri at h
    push Not at h
    obtain ⟨a, c, hac, hne⟩ := h
    refine Finset.prod_eq_zero (Finset.mem_univ (a, c)) ?_
    have hac' : a < c := hac
    have h1 : ¬ c < a := not_lt.mpr hac'.le
    have h2 : a ≠ c := ne_of_lt hac'
    simp [qn_pt, qn_low, h1, h2, hne]
end Formalism.InvariantFactorPaths.ColumnFamilies
