-- Prove2me | solution 1 for Formalism.UG.P.cT_conj_eq_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:37:58.815644+00:00
-- url     : https://prove2.me/submissions/def6d9a5-1e53-4a83-972b-c61a428135a8

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Upqcpt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (M : Matrix n n ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = star M := by
  unfold Formalism.UG.cT
  ext i j
  simp [Matrix.star_apply, Matrix.transpose_apply, Matrix.map_apply]
end Formalism.UG.P
