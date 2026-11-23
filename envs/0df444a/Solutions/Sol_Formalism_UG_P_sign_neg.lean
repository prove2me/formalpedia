-- Prove2me | solution 1 for Formalism.UG.P.sign_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:34.815029+00:00
-- url     : https://prove2.me/submissions/5a1226bc-7efd-4a84-880c-4badec4483f3

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.P
open Matrix
namespace Formalism.UG.P
theorem _root_.solution {x : ℝ} (h : x < 0) : x / |x| = -1 := by
  rw [abs_of_neg h, div_neg, div_self h.ne]
end Formalism.UG.P
