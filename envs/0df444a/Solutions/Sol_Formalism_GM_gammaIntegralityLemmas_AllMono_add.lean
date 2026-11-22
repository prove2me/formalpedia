-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.AllMono.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:31:26.923364+00:00
-- url     : https://prove2.me/submissions/13135f5f-2063-4b9c-8ccc-4942636b161f

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
theorem _root_.solution {d : M} {P P' : MvPolynomial σ ℚ_[p]} (h : AllMono Q d P) (h' : AllMono Q d P') :
    AllMono Q d (P + P') := by
  intro β hβ
  rcases Finset.mem_union.mp (support_add hβ) with h1 | h1
  · exact h _ h1
  · exact h' _ h1
end AllMono
end Formalism.GM.gammaIntegralityLemmas
