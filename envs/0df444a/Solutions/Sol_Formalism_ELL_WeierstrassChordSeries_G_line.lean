-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.G_line
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:15.614892+00:00
-- url     : https://prove2.me/submissions/908db755-0dfa-4296-ad0d-8b5f454bf3dc

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
theorem _root_.solution (a1 a2 a3 a4 a6 l n z : R) :
    G a1 a2 a3 a4 a6 z (l * z + n) = c3 a2 a4 a6 l * z ^ 3 + c2 a1 a2 a3 a4 a6 l n * z ^ 2
      + c1 a1 a3 a4 a6 l n * z + c0 a3 a6 n := by
  unfold G c3 c2 c1 c0
  ring
end Formalism.ELL.WeierstrassChordSeries
