-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.X_pow_mul_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:24:35.67983+00:00
-- url     : https://prove2.me/submissions/b2ffade0-0fdb-4fc4-81fc-28e476bafb5b

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
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type} [Fintype σ] [DecidableEq σ]
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (y : σ) (m : ℕ) (γ : σ →₀ ℕ) (h : ℚ_[p]) :
    (X y ^ m * monomial γ h : MvPolynomial σ ℚ_[p]) = monomial (γ + Finsupp.single y m) h := by
  rw [X_pow_eq_monomial, monomial_mul, one_mul, add_comm]
end Formalism.GM.gammaIntegralityLemmas
