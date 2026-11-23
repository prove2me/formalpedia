-- Prove2me | solution 1 for Formalism.GM.M.SSD.kap_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:25.577714+00:00
-- url     : https://prove2.me/submissions/caaa7ce9-0a67-4073-acaa-2d056476f336

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
theorem _root_.solution (F : (τ →₀ ℕ) → (σ →₀ ℕ)) (hF : Function.Injective F) (c : K) (Q : MvPolynomial σ K) :
    kap F hF (c • Q) = c • kap F hF Q := by
  ext n; simp only [coeff_kap, coeff_smul]
end Formalism.GM.M.SSD
