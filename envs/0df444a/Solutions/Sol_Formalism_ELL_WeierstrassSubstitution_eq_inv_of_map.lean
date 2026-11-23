-- Prove2me | solution 1 for Formalism.ELL.WeierstrassSubstitution.eq_inv_of_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:08.15167+00:00
-- url     : https://prove2.me/submissions/6f19efe1-0e96-4712-8d05-d39fe8bd5994

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.WeierstrassSubstitution
namespace Formalism.ELL.WeierstrassSubstitution
theorem _root_.solution {L F : Type*} [CommRing L] [Field F] (f : L →+* F) {a b : L}
    (h : a * b = 1) : f b = (f a)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← map_mul, h, map_one])
end Formalism.ELL.WeierstrassSubstitution
