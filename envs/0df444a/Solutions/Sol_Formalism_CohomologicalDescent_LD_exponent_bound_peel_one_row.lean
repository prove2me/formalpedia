-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.exponent_bound_peel_one_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:52:32.055432+00:00
-- url     : https://prove2.me/submissions/e944b311-caf9-463a-9ca4-30b5052f7bbd

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Theorems.Thm_Formalism_CohomologicalDescent_LD_depth2Levi
import Theorems.Thm_Formalism_CohomologicalDescent_LD_peelBoundLast
import Theorems.Thm_Formalism_CohomologicalDescent_LD_restriction_eq_block_weight
import Theorems.Thm_Formalism_CohomologicalDescent_LD_restriction_antitone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution (hD : BranchingBoundLastGradedOneRow) (l n : ℕ) (lam : ℕ → ℕ) (ξ : ℕ → ℤ) (hl : l.Prime)
    (ha : ∀ a b, a ≤ b → b < n + 1 → lam b ≤ lam a) (hξ : Antitone ξ) (I : ℤ) (e : ℕ)
    (hE : ExpUpTo l n lam ξ I e) : ExpUpTo l (n + 1) lam ξ I (e + (lam 0 + n - lam n - 1) / (l - 1)) := by
  intro μ hμ
  have hres := restriction_eq_block_weight n 1 lam (fun a h1 h2 => by
    have : a = n := by omega
    rw [this])
  rw [hres] at hμ ⊢
  refine peelBoundLast hD l n (lam n) (lam 0) (res n lam) (res (n + 1) ξ) hl
    (restriction_antitone n lam fun a b hab hb => ha a b hab (by omega))
    (fun b => ⟨ha b.val n (le_of_lt b.isLt) (by omega), ha 0 b.val (Nat.zero_le _) (by have := b.isLt; omega)⟩)
    (fun a b hab => hξ hab) I e (fun μ2 h2 => hE μ2 ?_) μ hμ
  rw [depth2Levi] at h2
  exact h2
end Formalism.CohomologicalDescent.LD
