-- Prove2me | solution 1 for Formalism.UG.P.split_cT_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:39:46.236811+00:00
-- url     : https://prove2.me/submissions/38bdbf8d-b1c9-400c-b051-ab3794431921

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SplitUnitaryGroupIso

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
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (g : Matrix n n (R × R)) :
    (cT (swapR R) g).map Prod.snd = (g.map Prod.fst)ᵀ := by
  ext i j
  rfl
end Formalism.UG.P
