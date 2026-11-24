-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.alg_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:50.164289+00:00
-- url     : https://prove2.me/submissions/f667a54d-684c-4d06-a8a5-101049621434

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open MvPolynomial Finset
namespace Formalism.GM.GammaExpansion
theorem _root_.solution {K : Type} [Field K] (a b c G Den I I' : K) (hG : G ≠ 0) (hD : Den ≠ 0)
    (hI : I' = I / Den) : a * (b * (c * (G * I))) / (G * Den) = a * b * c * I' := by
  subst hI
  first
  | (field_simp; ring)
  | field_simp
end Formalism.GM.GammaExpansion
