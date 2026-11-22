-- Prove2me | solution 1 for Formalism.REAL.Jm_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T16:51:29.244718+00:00
-- url     : https://prove2.me/submissions/fc84ae07-9fac-4428-96b1-377eda525566

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify

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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp only [Pi.star_apply]
  cases ε a <;> simp
end Formalism.REAL
