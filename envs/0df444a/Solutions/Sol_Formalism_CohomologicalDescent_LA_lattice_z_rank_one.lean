-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.lattice_z_rank_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:24:51.969889+00:00
-- url     : https://prove2.me/submissions/69da628b-bcd0-4378-98d1-1d24751f2077

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_hw_mem
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_incl_of_le
import Theorems.Thm_Formalism_CohomologicalDescent_LA_lattice_z_zero_columns
import Theorems.Thm_Formalism_CohomologicalDescent_LA_highest_weight_one_column
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution : LatticeInclusionRankOne := by
  unfold LatticeInclusionRankOne
  intro n hn ν hν l hl
  obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
  · exact lattice_z_zero_columns 1 hn ν l hl
  · apply la_incl_of_le hn ν _ _ hl
    intro x hx
    have hx' : x ∈ weightedHomogeneousSubmodule ℤ (colW 1 1) ν := (Submodule.mem_inf.mp hx).1
    rw [mem_weightedHomogeneousSubmodule] at hx'
    have hhw : hw ℤ hn ν = X ((0 : Fin 1), (0 : Fin 1)) ^ ν 0 := highest_weight_one_column ℤ hn ν
    rw [x.as_sum]
    refine Submodule.sum_mem _ (fun d hd => ?_)
    have hwd := hx' (mem_support_iff.mp hd)
    have hd0 : d = Finsupp.single ((0 : Fin 1), (0 : Fin 1)) (ν 0) := by
      have h0 := congrFun hwd 0
      rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h0
      simp [Fintype.sum_prod_type, colW] at h0
      ext ⟨i, j⟩
      fin_cases i
      fin_cases j
      simpa using h0
    have e : monomial (Finsupp.single ((0 : Fin 1), (0 : Fin 1)) (ν 0))
        (coeff (Finsupp.single ((0 : Fin 1), (0 : Fin 1)) (ν 0)) x) =
        coeff (Finsupp.single ((0 : Fin 1), (0 : Fin 1)) (ν 0)) x • hw ℤ hn ν := by
      rw [hhw, X_pow_eq_monomial, smul_monomial, smul_eq_mul, mul_one]
    rw [hd0, e]
    exact Submodule.smul_mem _ _ (la_hw_mem ℤ hn ν)
end Formalism.CohomologicalDescent.LA
