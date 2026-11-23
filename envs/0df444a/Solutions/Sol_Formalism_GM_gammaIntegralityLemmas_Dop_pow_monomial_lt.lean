-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.Dop_pow_monomial_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:00.857975+00:00
-- url     : https://prove2.me/submissions/82e6fc2d-e797-4f5e-a8b9-960307a8657b

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
theorem _root_.solution (u v : σ) (huv : u ≠ v) (a : ℕ) (γ : σ →₀ ℕ) (h : ℚ_[p]) (hlt : γ u < a) :
    (Dop u v ^ a) (monomial γ h) = 0 := by
  ext β
  rw [coeff_Dop_pow u v huv, coeff_monomial, coeff_zero]
  have : γ ≠ β + a • (Finsupp.single u 1 + Finsupp.single v 1) := by
    intro h'
    have := congrArg (fun f : σ →₀ ℕ => f u) h'
    simp [Finsupp.single_apply, huv] at this
    omega
  rw [if_neg this]; ring
end Formalism.GM.gammaIntegralityLemmas
