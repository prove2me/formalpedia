-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.fock_E
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:39.409729+00:00
-- url     : https://prove2.me/submissions/14f92227-fc87-4eac-a067-399978d50914

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_sum_left
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_sum_right
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_X_mul

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
theorem _root_.solution (g h : MvPolynomial σ ℚ_[p]) :
    Formalism.GM.M.fock p (Formalism.GM.tieE w e g) h = Formalism.GM.M.fock p g (Formalism.GM.tieF w e h) := by
  have h1 : Formalism.GM.tieE w e g = ∑ c, X (e c) * (X (w c) * g) := by
    simp only [Formalism.GM.tieE, LinearMap.mulLeft_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun c _ => by ring)
  have h2 : Formalism.GM.tieF w e h = ∑ c, pderiv (w c) (pderiv (e c) h) := by
    simp [Formalism.GM.tieF, LinearMap.sum_apply]
  rw [h1, h2, fock_sum_left, fock_sum_right]
  exact Finset.sum_congr rfl (fun c _ => by rw [fock_X_mul, fock_X_mul])
end Formalism.GM.gammaIntegralityLemmas
