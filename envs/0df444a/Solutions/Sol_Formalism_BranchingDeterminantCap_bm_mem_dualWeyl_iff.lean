-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bm_mem_dualWeyl_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:40:55.895906+00:00
-- url     : https://prove2.me/submissions/f4f29db5-b519-4bbf-856d-c3a5c5fa951c

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmC_pderiv_colAddGen
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmC_eq_rename_of_pderiv
import Theorems.Thm_Formalism_GradedWeylDivisibility_mem_dualWeyl_iff
import Theorems.Thm_Formalism_GradedWeylDivisibility_ndE_eq_zero
import Theorems.Thm_Formalism_GradedWeylDivisibility_ndEul_coeff
import Theorems.Thm_Formalism_GradedWeylDivisibility_ndEul_homog
import Theorems.Thm_Formalism_GradedWeylDivisibility_ndEv_colAddGen
import Theorems.Thm_Formalism_GradedWeylDivisibility_nd_weight_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] [CharZero R] {r n : ℕ} {ν : Fin n → ℕ}
    {G : MvPolynomial (Fin r × Fin n) R} :
    G ∈ dualWeyl R r n ν ↔
      (∀ s, ndEul R r n s G = (ν s : R) • G) ∧ ∀ l j : Fin n, l < j → ndE R r n l j G = 0 := by
  rw [mem_dualWeyl_iff]
  constructor
  · rintro ⟨hhom, hinv⟩
    exact ⟨fun s => ndEul_homog hhom s, fun l j hlj => ndE_eq_zero (hinv l j hlj)⟩
  · rintro ⟨heul, hE⟩
    refine ⟨?_, fun l j hlj => ?_⟩
    · intro m hm
      funext s
      have h1 := congrArg (coeff m) (heul s)
      rw [ndEul_coeff, coeff_smul, smul_eq_mul] at h1
      have h2 := mul_right_cancel₀ hm h1
      rw [← nd_weight_apply]
      exact_mod_cast h2
    · have h1 : pderiv none (colAddGen R l j G) = 0 := by
        rw [bmC_pderiv_colAddGen (ne_of_lt hlj), hE l j hlj, map_zero]
      have h2 := bmC_eq_rename_of_pderiv _ h1
      rw [ndEv_colAddGen] at h2
      exact h2
end Formalism.BranchingDeterminantCap
