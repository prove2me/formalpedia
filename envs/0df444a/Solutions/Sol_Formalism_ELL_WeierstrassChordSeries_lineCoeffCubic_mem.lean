-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.lineCoeffCubic_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:12:32.789323+00:00
-- url     : https://prove2.me/submissions/22a62bf5-97c4-494b-89da-5b58c726b29c

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
variable (T : Subring R)
namespace Formalism.ELL.WeierstrassChordSeries
theorem _root_.solution {a2 a4 a6 l : R} (h2 : a2 ∈ T) (h4 : a4 ∈ T) (h6 : a6 ∈ T) (hl : l ∈ T) :
    c3 a2 a4 a6 l ∈ T := by
  unfold c3
  exact T.add_mem (T.add_mem (T.add_mem T.one_mem (T.mul_mem h2 hl)) (T.mul_mem h4 (T.pow_mem hl 2)))
    (T.mul_mem h6 (T.pow_mem hl 3))
end Formalism.ELL.WeierstrassChordSeries
