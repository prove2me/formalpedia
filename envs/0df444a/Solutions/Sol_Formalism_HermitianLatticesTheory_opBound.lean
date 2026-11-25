-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.opBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:03:26.903645+00:00
-- url     : https://prove2.me/submissions/6fd85473-27fb-432d-bfc6-d208e47ac50e

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_OpBound
import Theorems.Thm_Formalism_HermitianLatticesTheory_opBound_cnorm_nonneg
import Theorems.Thm_Formalism_HermitianLatticesTheory_opBound_normSq
import Theorems.Thm_Formalism_HermitianLatticesTheory_opBound_fcoord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution : OpBound := by
  intro K V ι _ _ _ _ _ _ _ b X g δ hδ hO y
  have hb : ∀ v, cnorm (fcoord b X v (g y - y)) ≤ δ * cnorm (fcoord b X v y) := by
    intro v
    rw [opBound_fcoord]
    exact hO v (vecAt b v y)
  have hsq : ‖realize b X (g y - y)‖ ^ 2 ≤ (δ * ‖realize b X y‖) ^ 2 := by
    rw [mul_pow, opBound_normSq, opBound_normSq, Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    calc cnorm (fcoord b X v (g y - y)) ^ 2 ≤ (δ * cnorm (fcoord b X v y)) ^ 2 :=
          pow_le_pow_left₀ (opBound_cnorm_nonneg _) (hb v) 2
      _ = δ ^ 2 * cnorm (fcoord b X v y) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
end Formalism.HermitianLatticesTheory
