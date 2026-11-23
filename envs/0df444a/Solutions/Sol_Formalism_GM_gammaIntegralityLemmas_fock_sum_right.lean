-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.fock_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:09:57.410246+00:00
-- url     : https://prove2.me/submissions/7653acec-57f6-4cb3-ad39-ab8f7afec407

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_symm
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_sum_left

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
theorem _root_.solution {ι : Type} (t : Finset ι) (F : MvPolynomial σ ℚ_[p]) (G : ι → MvPolynomial σ ℚ_[p]) :
    Formalism.GM.M.fock p F (∑ i ∈ t, G i) = ∑ i ∈ t, Formalism.GM.M.fock p F (G i) := by
  rw [fock_symm, fock_sum_left]; exact Finset.sum_congr rfl (fun i _ => fock_symm _ _)
end Formalism.GM.gammaIntegralityLemmas
