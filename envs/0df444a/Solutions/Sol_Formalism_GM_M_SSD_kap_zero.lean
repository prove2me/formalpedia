-- Prove2me | solution 1 for Formalism.GM.M.SSD.kap_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:43.529043+00:00
-- url     : https://prove2.me/submissions/cff0845a-56df-4b22-8502-828da8414ae9

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
theorem _root_.solution (F : (τ →₀ ℕ) → (σ →₀ ℕ)) (hF : Function.Injective F) :
    kap F hF (0 : MvPolynomial σ K) = 0 := by
  ext n; simp only [coeff_kap, coeff_zero]
end Formalism.GM.M.SSD
