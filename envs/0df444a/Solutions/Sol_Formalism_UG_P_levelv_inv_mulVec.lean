-- Prove2me | solution 1 for Formalism.UG.P.levelv_inv_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:38:54.031992+00:00
-- url     : https://prove2.me/submissions/aba49e1c-bde5-4799-875e-bae7e378e62e

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
theorem _root_.solution (k : GL n R) (x : n → R) :
    ((k⁻¹ : GL n R) : Matrix n n R) *ᵥ ((k : Matrix n n R) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
end Formalism.UG.P
