-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.map_lineCoeffConst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:35.170685+00:00
-- url     : https://prove2.me/submissions/89b6fff1-e796-452d-a253-b6d52cf64d1d

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
variable {R' : Type*} [CommRing R'] (φ : R →+* R')
namespace Formalism.ELL.WeierstrassChordSeries
theorem _root_.solution (a3 a6 n : R) : φ (c0 a3 a6 n) = c0 (φ a3) (φ a6) (φ n) := by
  simp [c0]
end Formalism.ELL.WeierstrassChordSeries
