-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_nabla_r2n1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:02:24.486813+00:00
-- url     : https://prove2.me/submissions/ab6b7f92-1318-413e-aec9-d94b7571bd4c

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_xy_eq
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_mono_of_weight
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
theorem _root_.solution (R : Type) [CommRing R] (ν : Fin 1 → ℕ) :
    dualWeyl R 2 1 ν = la_monLat R (0 : Fin 1) (ν 0) := by
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ weightedHomogeneousSubmodule R (colW 2 1) ν := (Submodule.mem_inf.mp hx).1
    rw [mem_weightedHomogeneousSubmodule] at hx'
    rw [x.as_sum]
    refine Submodule.sum_mem _ (fun d hd => ?_)
    obtain ⟨hd', hsum⟩ := la_mono_of_weight (hx' (mem_support_iff.mp hd))
    have e : monomial d (coeff d x) = coeff d x • la_xy R (0 : Fin 1) (d (0, 0)) (d (1, 0)) := by
      rw [la_xy_eq, ← hd', smul_monomial, smul_eq_mul, mul_one]
    rw [e, la_monLat]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, hsum, rfl⟩)
  · rw [la_monLat, Submodule.span_le]
    rintro f ⟨p, q, hpq, rfl⟩
    show la_xy R (0 : Fin 1) p q ∈ weightedHomogeneousSubmodule R (colW 2 1) ν ⊓ _
    rw [Submodule.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [mem_weightedHomogeneousSubmodule, la_xy_eq]
      apply isWeightedHomogeneous_monomial
      funext j
      fin_cases j
      simp [la_mono, colW, Finsupp.weight_single, hpq]
    · simp only [Submodule.mem_iInf]
      intro a b hab
      exact ((ne_of_lt hab) (Subsingleton.elim a b)).elim
end Formalism.CohomologicalDescent.LA
