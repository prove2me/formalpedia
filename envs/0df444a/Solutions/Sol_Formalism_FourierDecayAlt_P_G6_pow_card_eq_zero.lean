-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G6.pow_card_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:21.655105+00:00
-- url     : https://prove2.me/submissions/340e1b16-0434-4bfd-be02-76242f21cc66

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G6_pow_apply_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G6
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G6
theorem _root_.solution {d : ℕ} {X : Matrix (Fin d) (Fin d) ℂ} (hX : IsStrictUpper X) :
    X ^ d = 0 := by
  ext i j
  exact pow_apply_eq_zero hX d i j (by have := j.2; omega)
end Formalism.FourierDecayAlt.P.G6
