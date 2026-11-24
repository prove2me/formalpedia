-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.telescoping_weighted_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:10:12.934855+00:00
-- url     : https://prove2.me/submissions/573b22bb-5cce-4164-bf1f-1dee4f4ac936

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
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
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution (f : ℕ → ℕ) (hf : ∀ s, f (s + 1) ≤ f s) (n : ℕ) :
    ∑ s ∈ Finset.range n, (s + 1) * (f s - f (s + 1)) + n * f n = ∑ s ∈ Finset.range n, f s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih]
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le (hf n)
    rw [hc, Nat.add_sub_cancel_left]
    ring
end Formalism.CohomologicalDescent.LD
