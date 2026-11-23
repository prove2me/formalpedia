-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.map_lineCoeffQuadratic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:37.87509+00:00
-- url     : https://prove2.me/submissions/845e734b-ae8c-4766-8853-bf0b2dcfc1ef

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
theorem _root_.solution (a1 a2 a3 a4 a6 l n : R) :
    φ (c2 a1 a2 a3 a4 a6 l n) = c2 (φ a1) (φ a2) (φ a3) (φ a4) (φ a6) (φ l) (φ n) := by
  have h2 : φ 2 = 2 := map_ofNat φ 2
  have h3 : φ 3 = 3 := map_ofNat φ 3
  simp [c2, h2, h3]
end Formalism.ELL.WeierstrassChordSeries
