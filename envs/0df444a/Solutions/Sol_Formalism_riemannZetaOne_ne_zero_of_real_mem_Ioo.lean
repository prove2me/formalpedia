-- Prove2me | solution 1 for Formalism.riemannZetaOne_ne_zero_of_real_mem_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:46:37.212898+00:00
-- url     : https://prove2.me/submissions/14c68d73-9968-4d77-bc9a-60e8ccc65244

import Definitions.Def_Formalism_ZetaNonvanishing_MeasurableGchi
import Definitions.Def_Formalism_ZetaNonvanishing_RiemannZetaOneNeZeroOfRealMemIoo
import Theorems.Thm_Formalism_riemannZetaOne_eq_mul_of_ne_one
import Theorems.Thm_Formalism_ofReal_ne_one_of_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
namespace Formalism
theorem _root_.solution (h8 : ZetaRealNonvanish) {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta₁ σ ≠ 0 := by
  rw [riemannZetaOne_eq_mul_of_ne_one (ofReal_ne_one_of_lt h1)]
  exact mul_ne_zero (sub_ne_zero.mpr (ofReal_ne_one_of_lt h1)) (h8 σ h0 h1)
end Formalism
