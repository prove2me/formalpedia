-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.pderiv_X_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:25.115829+00:00
-- url     : https://prove2.me/submissions/354b0c9d-eec5-4061-bd71-3ececf0c4d74

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
variable {σ : Type} [DecidableEq σ]
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (i y : σ) (hiy : i ≠ y) (m : ℕ) (G : MvPolynomial σ ℚ_[p]) :
    pderiv i (X y ^ m * G) = X y ^ m * pderiv i G := by
  rw [Derivation.leibniz, X_pow_eq_monomial, pderiv_monomial]
  have : (Finsupp.single y m : σ →₀ ℕ) i = 0 := by simp [Finsupp.single_apply, Ne.symm hiy]
  rw [this]
  simp
end Formalism.GM.gammaIntegralityLemmas
