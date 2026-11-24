-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.GoodQ_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:24.022251+00:00
-- url     : https://prove2.me/submissions/a04df06d-ac6b-42c4-b98a-662c5c99412c

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas__v_add_9b2e3af02dc8

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
variable {N r : ℕ}
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (ρ : Fin r) : ∀ d d' β β', GoodQ (N := N) ρ d β → GoodQ ρ d' β' → GoodQ ρ (d + d') (β + β') := by
  intro d d' β β' h h'
  refine ⟨by rw [δv_add, h.1, h'.1], ?_⟩
  simp only [Finsupp.add_apply]
  have := h.2; have := h'.2; omega
end Formalism.GM.gammaIntegralityLemmas
