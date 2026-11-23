-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.fock_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:00:59.295354+00:00
-- url     : https://prove2.me/submissions/2b472ce9-b9bb-4ece-9d94-878a93086228

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas_fock_def__dcd241737a4a
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_eq_sum

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
theorem _root_.solution (c : ℚ_[p]) (F G : MvPolynomial σ ℚ_[p]) :
    Formalism.GM.M.fock p (c • F) G = c * Formalism.GM.M.fock p F G := by
  rw [fock_eq_sum (c • F) G F.support support_smul, fock_def', Finset.mul_sum]
  exact Finset.sum_congr rfl (fun m _ => by rw [coeff_smul, smul_eq_mul]; ring)
end Formalism.GM.gammaIntegralityLemmas
