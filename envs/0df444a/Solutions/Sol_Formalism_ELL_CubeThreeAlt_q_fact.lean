-- Prove2me | solution 1 for Formalism.ELL.CubeThreeAlt.q_fact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:27.409847+00:00
-- url     : https://prove2.me/submissions/b4522ad2-bcea-42e5-a379-18c69392f2c2

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeThree

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
open Formalism.ELL.CubeThreeAlt
open WeierstrassChordSeries
variable {R : Type*} [CommRing R]
namespace Formalism.ELL.CubeThreeAlt
theorem _root_.solution [IsDomain R] {a1 a2 a3 a4 a6 u s d l c : R} (hu : u ≠ 0) (hd0 : d ≠ 0)
    (hsd : s * d = u) (hd : d = -1 + a1 * u + a3 * (l * u))
    (hG : G a1 a2 a3 a4 a6 u (l * u) = 0) :
    G a1 a2 a3 a4 a6 c (l * c) = c * c3 a2 a4 a6 l * (c - u) * (c - s) := by
  have hA : Formalism.ELL.WeierstrassChordSeries.c3 a2 a4 a6 l = 1 + a2 * l + a4 * l ^ 2 + a6 * l ^ 3 := rfl
  have hE : u * (Formalism.ELL.WeierstrassChordSeries.c3 a2 a4 a6 l * u ^ 2 + (a1 * l + a3 * l ^ 2) * u - l) = 0 := by
    unfold Formalism.ELL.WeierstrassChordSeries.G at hG
    rw [hA]
    linear_combination hG
  have hE' := (mul_eq_zero.mp hE).resolve_left hu
  have h1 : d * (Formalism.ELL.WeierstrassChordSeries.c3 a2 a4 a6 l * u * s + l) = 0 := by
    linear_combination (Formalism.ELL.WeierstrassChordSeries.c3 a2 a4 a6 l * u) * hsd + hE' + l * hd
  have h1' := (mul_eq_zero.mp h1).resolve_left hd0
  have h2 : u * (a1 * l + a3 * l ^ 2 + Formalism.ELL.WeierstrassChordSeries.c3 a2 a4 a6 l * u + Formalism.ELL.WeierstrassChordSeries.c3 a2 a4 a6 l * s) = 0 := by
    linear_combination hE' + h1'
  have h2' := (mul_eq_zero.mp h2).resolve_left hu
  unfold Formalism.ELL.WeierstrassChordSeries.G
  linear_combination (-c ^ 3) * hA + c ^ 2 * h2' - c * h1'
end Formalism.ELL.CubeThreeAlt
