-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.fock_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:06.458149+00:00
-- url     : https://prove2.me/submissions/1bd97623-3801-4de6-a461-b1392449c33c

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_symm
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_smul_left

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
    Formalism.GM.M.fock p F (c • G) = c * Formalism.GM.M.fock p F G := by
  rw [fock_symm, fock_smul_left, fock_symm]
end Formalism.GM.gammaIntegralityLemmas
