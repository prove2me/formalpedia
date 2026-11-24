-- Prove2me | solution 1 for Formalism.REAL.f1alg_unit_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:34:49.740324+00:00
-- url     : https://prove2.me/submissions/a63cbe9e-0f14-4680-8f4b-e1def08868b7

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
theorem _root_.solution {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    g ∈ Matrix.unitaryGroup (Fin n) ℂ ↔ gᴴ * g = 1 := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
end Formalism.REAL
