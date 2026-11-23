-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.AllMono.sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:00.761034+00:00
-- url     : https://prove2.me/submissions/273f7ca2-cef6-4de6-b4f0-b78a1074a307

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_add
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_add
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_neg

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
theorem _root_.solution {d : M} {P P' : MvPolynomial σ ℚ_[p]} (h : AllMono Q d P) (h' : AllMono Q d P') :
    AllMono Q d (P - P') := by
  rw [sub_eq_add_neg]; exact h.add Q h'.neg
end AllMono
end Formalism.GM.gammaIntegralityLemmas
