-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.Dop_pow_monomial_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:23.848619+00:00
-- url     : https://prove2.me/submissions/716c9223-69d2-4178-9d81-7bea73046f37

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_coeff_Dop_pow

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
theorem _root_.solution (u v : σ) (huv : u ≠ v) (a : ℕ) (δ : σ →₀ ℕ) (h : ℚ_[p]) :
    (Dop u v ^ a) (monomial (δ + a • (Finsupp.single u 1 + Finsupp.single v 1)) h) =
      monomial δ (h * (((δ u + a).descFactorial a : ℕ) : ℚ_[p]) * (((δ v + a).descFactorial a : ℕ) : ℚ_[p])) := by
  ext β
  rw [coeff_Dop_pow u v huv, coeff_monomial, coeff_monomial]
  by_cases hb : δ = β
  · subst hb; simp
  · have : δ + a • (Finsupp.single u 1 + Finsupp.single v 1) ≠ β + a • (Finsupp.single u 1 + Finsupp.single v 1) :=
      fun h' => hb (add_right_cancel h')
    simp [this, hb]
end Formalism.GM.gammaIntegralityLemmas
