-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.AllMono.neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:23:27.619308+00:00
-- url     : https://prove2.me/submissions/962ee189-3957-4aa8-9a0e-e15890567263

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
theorem _root_.solution {d : M} {P : MvPolynomial σ ℚ_[p]} (h : AllMono Q d P) : AllMono Q d (-P) := by
  intro β hβ; rw [support_neg] at hβ; exact h _ hβ
end AllMono
end Formalism.GM.gammaIntegralityLemmas
