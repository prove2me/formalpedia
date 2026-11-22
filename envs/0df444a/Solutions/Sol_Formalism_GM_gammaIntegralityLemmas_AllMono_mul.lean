-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.AllMono.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:30:38.709844+00:00
-- url     : https://prove2.me/submissions/aa0c7b5f-e76b-4aae-b64b-af514d388b94

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
theorem _root_.solution (hQ : ∀ d d' β β', Q d β → Q d' β' → Q (d + d') (β + β')) {d d' : M}
    {P P' : MvPolynomial σ ℚ_[p]} (h : AllMono Q d P) (h' : AllMono Q d' P') : AllMono Q (d + d') (P * P') := by
  intro β hβ
  obtain ⟨β1, h1, β2, h2, rfl⟩ := Finset.mem_add.mp (support_mul P P' hβ)
  exact hQ _ _ _ _ (h _ h1) (h' _ h2)
end AllMono
end Formalism.GM.gammaIntegralityLemmas
