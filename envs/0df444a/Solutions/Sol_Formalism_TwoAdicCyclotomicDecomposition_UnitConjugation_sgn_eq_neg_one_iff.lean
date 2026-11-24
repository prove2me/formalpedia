-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation.sgn_eq_neg_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:37:19.834868+00:00
-- url     : https://prove2.me/submissions/7d12393b-cf28-4b35-a930-93bd5da3cfd8

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_ConjEqInvOfPowEqOne
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_UnitConjugation_ne_zero_of_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation
variable {n q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation
theorem _root_.solution (hq : 0 < q) (ha : a ^ 2 = -(q : L)) (σ : Gal(L/ℚ)) :
    sgn σ a = -1 ↔ σ a = -a := by
  have ha0 := ne_zero_of_sq hq ha
  have hsq : σ a ^ 2 = a ^ 2 := by
    rw [← map_pow, ha, map_neg, map_natCast]
  unfold sgn
  split_ifs with hc
  · constructor
    · intro h; exact absurd h (by decide)
    · intro h
      exfalso
      have h3 : (2 : L) * a = 0 := by linear_combination h - hc
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact two_ne_zero h4
      · exact ha0 h4
  · simp only [true_iff]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h1 | h1
    · exact absurd h1 hc
    · exact h1
end Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation
