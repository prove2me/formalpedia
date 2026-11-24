-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_sym_hw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:53:54.258369+00:00
-- url     : https://prove2.me/submissions/d2cad38e-c471-46bd-8d10-f10074bbee17

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_symmetric_block_weight_zero
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_sym_nu_ne
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution (q w : ℕ) :
    hw ℤ (le_refl (1 + q)) (blockWt 1 q w (fun _ => 0)) = X (ldZ q, ldZ q) ^ w := by
  unfold hw
  rw [Finset.prod_eq_single (ldZ q)]
  · have h1 : nuNext (blockWt 1 q w fun _ => 0) (ldZ q) = 0 := by
      unfold nuNext
      split_ifs with h
      · apply ld_sym_nu_ne
        intro heq
        exact absurd (congrArg Fin.val heq) (by simp)
      · rfl
    rw [h1, symmetric_block_weight_zero, Nat.sub_zero]
    congr 1
    have hz : ((ldZ q : Fin (1 + q)) : ℕ) = 0 := rfl
    simp only [hz, zero_add]
    unfold lpMinor
    rw [Matrix.det_unique]
    rfl
  · intro b _ hb
    rw [ld_sym_nu_ne q w b hb, Nat.zero_sub, pow_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.CohomologicalDescent.LD
