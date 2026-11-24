-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_blockWt_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:53:03.744581+00:00
-- url     : https://prove2.me/submissions/f82f2458-09d2-427c-90cc-d3496d588326

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
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
theorem _root_.solution (p q w : ℕ) (lam2 : Fin q → ℕ) (ha : Antitone lam2) (hb : ∀ b, lam2 b ≤ w) :
    Antitone (blockWt p q w lam2) := by
  intro i j hij
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j => simp only [blockWt, Fin.append_left, le_refl]
    | right j =>
      simp only [blockWt, Fin.append_left, Fin.append_right]
      exact hb j
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      exfalso
      have := j.isLt
      rw [Fin.le_def] at hij
      simp at hij
      omega
    | right j =>
      simp only [blockWt, Fin.append_right]
      apply ha
      rw [Fin.le_def] at hij ⊢
      simpa using hij
end Formalism.CohomologicalDescent.LD
