-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.fock_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:18:12.712132+00:00
-- url     : https://prove2.me/submissions/5b655a04-1196-4f2d-9511-419d783f0be3

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Theorems.Thm_P2M_Formalism_GM_GammaExpansion_fock_eq_sum__ebe099adb659

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
theorem _root_.solution (c : ℚ_[p]) (F G : MvPolynomial σ ℚ_[p]) :
    M.fock p (c • F) G = c * M.fock p F G := by
  rw [fock_eq_sum' p _ G G.support (Finset.Subset.refl _), fock_eq_sum' p F G G.support (Finset.Subset.refl _),
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by rw [coeff_smul, smul_eq_mul]; ring
end Formalism.GM.GammaExpansion
