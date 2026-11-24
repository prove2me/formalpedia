-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.hy_wv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:06.228128+00:00
-- url     : https://prove2.me/submissions/a5d12cdc-81a1-456a-8e82-bb286d8c195b

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
variable {N r : ℕ}
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (ρ : Fin r) : ∀ c ∈ univ.erase ρ, wv (N := N) c ≠ ev ρ ∧ ev (N := N) c ≠ ev ρ := by
  intro c hc
  refine ⟨?_, ?_⟩
  · simp [wv, ev, Fin.castSucc_ne_last]
  · simp only [ev, ne_eq, Prod.mk.injEq, true_and]; exact ne_of_mem_erase hc
end Formalism.GM.gammaIntegralityLemmas
