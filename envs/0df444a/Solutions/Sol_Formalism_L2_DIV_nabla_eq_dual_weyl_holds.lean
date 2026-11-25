-- Prove2me | solution 1 for Formalism.L2.DIV.nabla_eq_dual_weyl_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:01:17.756785+00:00
-- url     : https://prove2.me/submissions/bdad9cb7-2482-4406-840d-20e363687508

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LowerTriangularIntegral
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_WeTransposeWordTransposeWord
import Theorems.Thm_Formalism_L2_DIV_we_intQ_apply
import Theorems.Thm_Formalism_L2_DIV_we_fock_zero_right
import Theorems.Thm_Formalism_L2_DIV_we_hw_norm_ne
import Theorems.Thm_Formalism_L2_DIV_we_eval_idFrame_map
import Theorems.Thm_Formalism_L2_DIV_we_intQ_word
import Theorems.Thm_Formalism_L2_DIV_we_fock_word
import Theorems.Thm_Formalism_L2_DIV_we_transposeWord_transposeWord
import Theorems.Thm_Formalism_CohomologicalDescent_LR_coefficient_word
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lower_triangular_integral
import Theorems.Thm_Formalism_GradedWeylDivisibility_colSums
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylIntRat
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_applyWord_map
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
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.GradedWeylDivisibility
namespace Formalism.L2.DIV
theorem _root_.solution : NablaEqDualWeyl := by
  intro r n hn ν hν
  ext P
  constructor
  · rintro ⟨P0, hP0, rfl⟩
    have hPQ : intQ r n P0 ∈ dualWeyl ℚ r n ν := dualWeylMap ℤ ℚ (Int.castRingHom ℚ) r n ν P0 hP0
    refine ⟨hPQ, ?_⟩
    rintro _ ⟨Q0, hQ0, rfl⟩
    replace hQ0 : Q0 ∈ weyl ℤ r n hn ν := hQ0
    unfold weyl at hQ0
    induction hQ0 using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      refine ⟨eval (idFrame ℤ r n) (applyWord ℤ (transposeWord w) P0), ?_⟩
      simp only
      rw [we_intQ_word, we_fock_word hn ν hν w _ hPQ, we_intQ_apply, lclosedeq_applyWord_map, we_eval_idFrame_map]
    | zero => exact ⟨0, by rw [map_zero, we_fock_zero_right]; simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, we_fock_add_right, ha, hb]; push_cast; ring⟩
    | smul c x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨c * a, ?_⟩
      rw [map_smul, ← Int.cast_smul_eq_zsmul ℚ, we_fock_smul_right, ha]
      push_cast; ring
  · rintro ⟨hP, hdual⟩
    have hc := we_hw_norm_ne hn ν
    obtain ⟨Q', hQ'⟩ := Formalism.CohomologicalDescent.LR.lower_triangular_integral r n ν P hP (fun e he => by
      by_cases hcol : ∀ s : Fin n, ∑ a : Fin r, e (a, s) = ν s
      · have hhom : IsWeightedHomogeneous (colW r n) P ν := hP.1
        rw [Formalism.CohomologicalDescent.LR.coefficient_word ℚ r n ν P e hhom he hcol]
        obtain ⟨z, hz⟩ := hdual (intQ r n (applyWord ℤ (transposeWord (wordOf e)) (hw ℤ hn ν)))
          (Submodule.mem_map_of_mem (Submodule.subset_span ⟨_, rfl⟩))
        rw [we_intQ_word, we_fock_word hn ν hν _ P hP, we_transposeWord_transposeWord] at hz
        exact ⟨z, mul_right_cancel₀ hc hz⟩
      · refine ⟨0, ?_⟩
        rw [Int.cast_zero]
        by_contra h
        exact hcol (colSums ℚ r n ν P hP e (mem_support_iff.mpr h)))
    refine ⟨Q', (dualWeylIntRat r n ν Q').2 ?_, hQ'.symm⟩
    rw [← we_intQ_apply, ← hQ']
    exact hP
end Formalism.L2.DIV
