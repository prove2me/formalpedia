-- Prove2me | solution 1 for Formalism.UG.P.levelv_mulVec_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:22:47.945636+00:00
-- url     : https://prove2.me/submissions/994eb488-04a5-446b-864d-67eb12ceb3fa

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (k l : GL n R) (x : n → R) :
    ((k * l : GL n R) : Matrix n n R) *ᵥ x = (k : Matrix n n R) *ᵥ ((l : Matrix n n R) *ᵥ x) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]
end Formalism.UG.P
