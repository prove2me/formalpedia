-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.fock_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:52.496293+00:00
-- url     : https://prove2.me/submissions/3c503df8-acaa-4723-8a66-454c65ee4c79

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Theorems.Thm_Formalism_GM_GammaExpansion_fock_comm
import Theorems.Thm_Formalism_GM_GammaExpansion_fock_sum_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime] {σ : Type} [Fintype σ] [DecidableEq σ]
namespace Formalism.GM.GammaExpansion
theorem _root_.solution {ι : Type} (t : Finset ι) (F : MvPolynomial σ ℚ_[p]) (G : ι → MvPolynomial σ ℚ_[p]) :
    M.fock p F (∑ i ∈ t, G i) = ∑ i ∈ t, M.fock p F (G i) := by
  rw [fock_comm, fock_sum_left]
  exact Finset.sum_congr rfl fun i _ => fock_comm p _ _
end Formalism.GM.GammaExpansion
