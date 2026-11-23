-- Prove2me | solution 1 for Formalism.UG.P.levelv_mulVec_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:02.751872+00:00
-- url     : https://prove2.me/submissions/20493e23-582a-4dca-9533-5b4bf046fba4

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
    (k : Matrix n n R) *ᵥ (((k⁻¹ : GL n R) : Matrix n n R) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
end Formalism.UG.P
