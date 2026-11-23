-- Prove2me | solution 1 for Formalism.UG.P.split_map_snd_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:15.894802+00:00
-- url     : https://prove2.me/submissions/f156b3f4-a22e-4f87-ab02-1c09c05aa861

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
theorem _root_.solution (M N : Matrix n n (R × R)) :
    (M * N).map Prod.snd = M.map Prod.snd * N.map Prod.snd := by
  ext i j
  simp [Matrix.mul_apply, Prod.snd_sum]
end Formalism.UG.P
