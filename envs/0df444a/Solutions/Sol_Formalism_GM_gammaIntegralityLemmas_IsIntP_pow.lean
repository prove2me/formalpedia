-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.IsIntP.pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:51.544683+00:00
-- url     : https://prove2.me/submissions/23ab1671-6aff-432c-9b45-4bdf8f091b80

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_zero
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_zero
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_one
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_one

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
namespace IsIntP
theorem _root_.solution {P : MvPolynomial σ ℚ_[p]} (h : IsIntP P) (n : ℕ) : IsIntP (P ^ n) := by
  induction n with
  | zero => simpa using IsIntP.one (p := p) (σ := σ)
  | succ n ih => rw [pow_succ]; exact ih.mul h
end IsIntP
end Formalism.GM.gammaIntegralityLemmas
