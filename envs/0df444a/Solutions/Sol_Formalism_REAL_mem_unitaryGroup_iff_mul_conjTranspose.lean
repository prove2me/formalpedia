-- Prove2me | solution 1 for Formalism.REAL.mem_unitaryGroup_iff_mul_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:34:56.397133+00:00
-- url     : https://prove2.me/submissions/5403dcc4-acd0-4def-a27c-d411991eeba8

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
    g ∈ Matrix.unitaryGroup (Fin n) ℂ ↔ g * gᴴ = 1 := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
end Formalism.REAL
