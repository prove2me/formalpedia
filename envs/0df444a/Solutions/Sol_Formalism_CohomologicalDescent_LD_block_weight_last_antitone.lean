-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.block_weight_last_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:02:36.393328+00:00
-- url     : https://prove2.me/submissions/c0b4b43b-849e-459d-b448-16a79dc73a5a

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
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
theorem _root_.solution (p q w : ℕ) (lam2 : Fin q → ℕ) (ha : Antitone lam2) (hb : ∀ b, w ≤ lam2 b) :
    Antitone (blockWtLast p q w lam2) := by
  intro a b
  unfold blockWtLast
  refine Fin.addCases (fun a' => ?_) (fun a' => ?_) a <;>
    refine Fin.addCases (fun b' => ?_) (fun b' => ?_) b <;> intro hab
  · rw [Fin.append_left, Fin.append_left]
    refine ha ?_
    have h1 : (Fin.castAdd p a').val ≤ (Fin.castAdd p b').val := hab
    simp only [Fin.val_castAdd] at h1
    exact Fin.le_def.mpr h1
  · rw [Fin.append_left, Fin.append_right]
    exact hb a'
  · exfalso
    have h1 : (Fin.natAdd q a').val ≤ (Fin.castAdd p b').val := hab
    have h2 := b'.isLt
    simp only [Fin.val_natAdd, Fin.val_castAdd] at h1
    omega
  · rw [Fin.append_right, Fin.append_right]
end Formalism.CohomologicalDescent.LD
