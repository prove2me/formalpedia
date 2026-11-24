-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.part_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:48:24.018802+00:00
-- url     : https://prove2.me/submissions/bbf02096-4283-4dd8-ab63-905bbb2d392c

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
variable {ι ζ : Type*} {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution {σ L : Type*} [CommRing L] (H : MvPolynomial σ L) (p : (σ →₀ ℕ) → Prop) [DecidablePred p] :
    (∑ e ∈ H.support.filter p, monomial e (coeff e H)) ≠ 0 ↔ ∃ e ∈ H.support, p e := by
  classical
  constructor
  · intro h
    by_contra hc
    apply h
    have : H.support.filter p = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro e he hp
      exact hc ⟨e, he, hp⟩
    rw [this, Finset.sum_empty]
  · rintro ⟨e, he, hp⟩ h
    have := congrArg (coeff e) h
    rw [coeff_sum] at this
    simp only [coeff_monomial, Finset.sum_ite_eq', Finset.mem_filter, coeff_zero] at this
    rw [if_pos ⟨he, hp⟩] at this
    exact (mem_support_iff.mp he) this
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
