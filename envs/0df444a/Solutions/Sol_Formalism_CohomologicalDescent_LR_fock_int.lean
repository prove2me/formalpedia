-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.fock_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:20:10.903101+00:00
-- url     : https://prove2.me/submissions/ab89a026-daaa-4c55-b77a-809fb0be63e3

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrcFockZeroRight
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrc_intQ_apply
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrc_eval_map
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrc_fock_add_right
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrc_fock_smul_right
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrc_fock_zero_right
import Theorems.Thm_Formalism_CohomologicalDescent_LR_fock_word
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_applyWord_map
import Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_hw_map
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution (r : ℕ) (ν : Fin r → ℕ) (hν : Antitone ν) (x : MvPolynomial (Fin r × Fin r) ℤ)
    (hx : x ∈ dualWeyl ℤ r r ν) (y : MvPolynomial (Fin r × Fin r) ℤ) (hy : y ∈ weyl ℤ r r le_rfl ν) :
    ∃ z : ℤ, fockQ (intQ r r x) (intQ r r y) = z * fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) := by
  unfold weyl at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl⟩ := hy
    refine ⟨eval (idFrame ℤ r r) (applyWord ℤ (transposeWord w) x), ?_⟩
    simp only [lrc_intQ_apply]
    rw [← lclosedeq_applyWord_map, lclosedeq_hw_map,
      fock_word r ν hν _ (dualWeylMap ℤ ℚ (Int.castRingHom ℚ) r r ν x hx) w, lclosedeq_applyWord_map, lrc_eval_map]
  | zero =>
    refine ⟨0, ?_⟩
    rw [map_zero, lrc_fock_zero_right]
    simp
  | add y y' _ _ ih ih' =>
    obtain ⟨z, hz⟩ := ih
    obtain ⟨z', hz'⟩ := ih'
    refine ⟨z + z', ?_⟩
    rw [map_add, lrc_fock_add_right, hz, hz']
    push_cast
    ring
  | smul c y _ ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨c * z, ?_⟩
    rw [map_smul, ← Int.cast_smul_eq_zsmul ℚ, lrc_fock_smul_right, hz]
    push_cast
    ring
end Formalism.CohomologicalDescent.LR
