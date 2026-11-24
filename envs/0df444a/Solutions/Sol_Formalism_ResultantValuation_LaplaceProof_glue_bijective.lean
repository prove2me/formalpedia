-- Prove2me | solution 1 for Formalism.ResultantValuation.LaplaceProof.glue_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:02:38.778682+00:00
-- url     : https://prove2.me/submissions/260c75be-bb9d-48c4-9850-af6cb2ef389d

import Definitions.Def_Formalism_ResultantValuation_ResultantConjugate
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Laplace
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_natAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_natAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_injective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_natAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.glue_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.glue_natAdd

set_option autoImplicit false
open Finset Equiv
noncomputable section
open Formalism Formalism.ResultantValuation
open Formalism.ResultantValuation.LaplaceProof
variable {a b : ℕ}
namespace Formalism.ResultantValuation.LaplaceProof
theorem _root_.solution : Function.Bijective (glue (a := a) (b := b)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨glue_injective, ?_⟩
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_perm, Fintype.card_fin,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_finset_len]
  have key := Nat.add_choose_mul_factorial_mul_factorial b a
  rw [add_comm b a] at key
  rw [← key]
  ring
end Formalism.ResultantValuation.LaplaceProof
