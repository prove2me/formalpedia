-- Prove2me | solution 1 for Formalism.GM.M.SSD.kap_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:16.335378+00:00
-- url     : https://prove2.me/submissions/c6041827-8c7f-4ccc-8d50-ddd33a085c50

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_Formalism_GM_M_SSD_coeff_kap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.SSD
open MvPolynomial Finset
variable {σ τ K : Type} [Field K] [DecidableEq σ]
namespace Formalism.GM.M.SSD
theorem _root_.solution (F : (τ →₀ ℕ) → (σ →₀ ℕ)) (hF : Function.Injective F) (Q Q' : MvPolynomial σ K) :
    kap F hF (Q + Q') = kap F hF Q + kap F hF Q' := by
  ext n; simp only [coeff_kap, coeff_add]
end Formalism.GM.M.SSD
