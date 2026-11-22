-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.AllMono.congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:53.836632+00:00
-- url     : https://prove2.me/submissions/65e49d96-bfd6-436e-88c0-7f2bf19edc91

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
theorem _root_.solution {d d' : M} (hd : d = d') {P : MvPolynomial σ ℚ_[p]} (h : AllMono Q d P) :
    AllMono Q d' P := hd ▸ h
end AllMono
end Formalism.GM.gammaIntegralityLemmas
