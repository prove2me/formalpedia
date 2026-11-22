-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.AllMono.one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:36:15.084039+00:00
-- url     : https://prove2.me/submissions/b096c9bd-f460-4e2b-9fc3-9ccc1d67a6ad

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type} [DecidableEq σ] {M : Type} [AddCommMonoid M]
variable (Q : M → (σ →₀ ℕ) → Prop)
namespace Formalism.GM.gammaIntegralityLemmas
namespace AllMono
theorem _root_.solution (hQ0 : Q 0 0) : AllMono Q 0 (1 : MvPolynomial σ ℚ_[p]) := by
  intro β hβ
  have : β = 0 := by
    have h1 : (1 : MvPolynomial σ ℚ_[p]) = monomial 0 1 := rfl
    rw [h1] at hβ
    simpa using support_monomial_subset hβ
  subst this; exact hQ0
end AllMono
end Formalism.GM.gammaIntegralityLemmas
