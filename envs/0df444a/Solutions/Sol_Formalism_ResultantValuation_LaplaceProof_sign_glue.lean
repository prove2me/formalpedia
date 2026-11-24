-- Prove2me | solution 1 for Formalism.ResultantValuation.LaplaceProof.sign_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:02:40.428847+00:00
-- url     : https://prove2.me/submissions/ec56ec52-1f81-48d4-9e54-9ecca808f79e

import Definitions.Def_Formalism_ResultantValuation_ResultantConjugate
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Laplace
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_natAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_sign_shuffle
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_natAdd
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
theorem _root_.solution (x : Σ _ : {J : Finset (Fin (a + b)) // J.card = a},
    Perm (Fin a) × Perm (Fin b)) :
    Perm.sign (glue x) = (-1) ^ (a * (a - 1) / 2 + ∑ j ∈ x.1.1, (j : ℕ)) *
      Perm.sign x.2.1 * Perm.sign x.2.2 := by
  simp only [glue, Perm.sign_mul, sign_shuffle, Perm.sign_permCongr, Perm.sign_sumCongr, mul_assoc]
end Formalism.ResultantValuation.LaplaceProof
