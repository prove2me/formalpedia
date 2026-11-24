-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.fock_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:44.821984+00:00
-- url     : https://prove2.me/submissions/d9218f74-fd3c-4046-adf5-cc985c3afd77

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_wf_add_single
import Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas_fock_def__dcd241737a4a

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
theorem _root_.solution (i : σ) (g h : MvPolynomial σ ℚ_[p]) :
    Formalism.GM.M.fock p (X i * g) h = Formalism.GM.M.fock p g (pderiv i h) := by
  have hs : (X i * g).support = g.support.map (addRightEmbedding (Finsupp.single i 1)) := by
    rw [mul_comm]; exact support_mul_X i g
  rw [fock_def', hs, Finset.sum_map, fock_def']
  refine Finset.sum_congr rfl (fun m _ => ?_)
  simp only [addRightEmbedding_apply]
  rw [mul_comm (X i) g, coeff_mul_X, coeff_pderiv, wf_add_single]
  push_cast; ring
end Formalism.GM.gammaIntegralityLemmas
