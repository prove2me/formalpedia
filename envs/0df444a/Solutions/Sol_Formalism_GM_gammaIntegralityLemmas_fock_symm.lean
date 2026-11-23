-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.fock_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:00.049686+00:00
-- url     : https://prove2.me/submissions/badbe2ea-1d82-4a35-afef-0da56ee428ba

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
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
theorem _root_.solution (F G : MvPolynomial σ ℚ_[p]) : Formalism.GM.M.fock p F G = Formalism.GM.M.fock p G F := by
  rw [fock_eq_sum F G _ (Finset.subset_union_left (s₂ := G.support)),
    fock_eq_sum G F _ (Finset.subset_union_right (s₁ := F.support))]
  exact Finset.sum_congr rfl (fun m _ => by ring)
end Formalism.GM.gammaIntegralityLemmas
