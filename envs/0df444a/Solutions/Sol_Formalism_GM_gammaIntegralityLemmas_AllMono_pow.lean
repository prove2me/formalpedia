-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.AllMono.pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:23:36.683458+00:00
-- url     : https://prove2.me/submissions/a28a7ddb-ef5c-4210-97cc-7c078cd2c07c

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_zero
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_zero
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_one

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
theorem _root_.solution (hQ : ∀ d d' β β', Q d β → Q d' β' → Q (d + d') (β + β')) (hQ0 : Q 0 0) {d : M}
    {P : MvPolynomial σ ℚ_[p]} (h : AllMono Q d P) (n : ℕ) : AllMono Q (n • d) (P ^ n) := by
  induction n with
  | zero => simpa using AllMono.one Q hQ0
  | succ n ih => rw [pow_succ, succ_nsmul]; exact ih.mul Q hQ h
end AllMono
end Formalism.GM.gammaIntegralityLemmas
