-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.fock_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:36:18.317887+00:00
-- url     : https://prove2.me/submissions/4fded2ce-acf8-43df-ad4d-74ace4c4a0d7

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
variable {σ : Type} [Fintype σ] [DecidableEq σ]
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (G : MvPolynomial σ ℚ_[p]) : Formalism.GM.M.fock p 0 G = 0 := by
  simp [Formalism.GM.M.fock]
end Formalism.GM.gammaIntegralityLemmas
