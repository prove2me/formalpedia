-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.AllMono.X_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:23.691132+00:00
-- url     : https://prove2.me/submissions/2da6fc08-0855-4934-ad1e-daae1b079da4

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
theorem _root_.solution (u u' : σ) (d : M) (hq : Q d (Finsupp.single u 1 + Finsupp.single u' 1)) :
    AllMono Q d (X u * X u' : MvPolynomial σ ℚ_[p]) := by
  intro β hβ
  rw [X, X, monomial_mul, one_mul] at hβ
  have := support_monomial_subset hβ
  rw [Finset.mem_singleton] at this
  subst this; exact hq
end AllMono
end Formalism.GM.gammaIntegralityLemmas
