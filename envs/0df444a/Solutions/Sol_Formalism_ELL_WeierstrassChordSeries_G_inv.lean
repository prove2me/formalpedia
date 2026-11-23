-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.G_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:14.732862+00:00
-- url     : https://prove2.me/submissions/001d6978-2b6b-44b3-8682-ec499488fa4f

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord

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
open Formalism Formalism.ELL
open Formalism.ELL.WeierstrassChordSeries
variable {R : Type*} [CommRing R]
namespace Formalism.ELL.WeierstrassChordSeries
theorem _root_.solution [IsDomain R] {a1 a2 a3 a4 a6 z v f u d : R} (hf : f * d = z) (hu : u * d = v)
    (hd : d = -1 + a1 * z + a3 * v) (hd0 : d ≠ 0) (hG : G a1 a2 a3 a4 a6 z v = 0) :
    G a1 a2 a3 a4 a6 f u = 0 := by
  subst hf hu
  have key : d ^ 3 * G a1 a2 a3 a4 a6 f u = 0 := by
    unfold G at hG ⊢
    linear_combination hG - u * d * (d - 1) * hd
  exact (mul_eq_zero.mp key).resolve_left (pow_ne_zero 3 hd0)
end Formalism.ELL.WeierstrassChordSeries
