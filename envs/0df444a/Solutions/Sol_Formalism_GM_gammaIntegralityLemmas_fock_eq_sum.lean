-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.fock_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:20.007446+00:00
-- url     : https://prove2.me/submissions/81c0f05a-3ea9-481e-b271-79cc620a1f0e

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
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
theorem _root_.solution (F G : MvPolynomial σ ℚ_[p]) (s : Finset (σ →₀ ℕ)) (h : F.support ⊆ s) :
    Formalism.GM.M.fock p F G = ∑ m ∈ s, F.coeff m * G.coeff m * wf m := by
  rw [fock_def']
  apply Finset.sum_subset h
  intro m _ hm
  rw [notMem_support_iff.mp hm]; ring
end Formalism.GM.gammaIntegralityLemmas
