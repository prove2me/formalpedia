-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.fock_E_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:38.96308+00:00
-- url     : https://prove2.me/submissions/822ccfdc-53b3-409d-b5d3-fa00c2f65474

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_zero
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_E

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
variable {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} (w e : Fin r → σ)
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (j : ℕ) (g h : MvPolynomial σ ℚ_[p]) :
    Formalism.GM.M.fock p ((Formalism.GM.tieE w e ^ j) g) h = Formalism.GM.M.fock p g ((Formalism.GM.tieF w e ^ j) h) := by
  induction j generalizing h with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, fock_E, ih, pow_succ, Module.End.mul_apply]
end Formalism.GM.gammaIntegralityLemmas
