-- Prove2me | solution 1 for Formalism.REAL.f1alg_ct_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:35:03.779308+00:00
-- url     : https://prove2.me/submissions/e30a84b0-e0f8-43cb-892e-0f215a292665

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) :
    (X * Y - Y * X)ᴴ = Yᴴ * Xᴴ - Xᴴ * Yᴴ := by
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul]
end Formalism.REAL
