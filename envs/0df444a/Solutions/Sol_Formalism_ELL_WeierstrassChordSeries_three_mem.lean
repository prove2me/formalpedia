-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.three_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:51.139149+00:00
-- url     : https://prove2.me/submissions/2181f6c4-155c-48eb-bbc4-6ab5cb9792ba

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_two_mem

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
theorem _root_.solution : (3 : R) ∈ T := by
  rw [show (3 : R) = 2 + 1 by norm_num]
  exact T.add_mem (two_mem T) T.one_mem
end Formalism.ELL.WeierstrassChordSeries
