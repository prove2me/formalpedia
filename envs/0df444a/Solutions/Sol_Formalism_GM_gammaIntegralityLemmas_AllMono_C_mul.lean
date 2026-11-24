-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.AllMono.C_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:01.478838+00:00
-- url     : https://prove2.me/submissions/8308f2e8-7ed3-4d20-9e70-56558c44ac31

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
theorem _root_.solution (a : ℚ_[p]) {d : M} {P : MvPolynomial σ ℚ_[p]} (h : AllMono Q d P) :
    AllMono Q d (C a * P) := by
  intro β hβ
  rw [C_mul'] at hβ
  exact h _ (support_smul hβ)
end AllMono
end Formalism.GM.gammaIntegralityLemmas
