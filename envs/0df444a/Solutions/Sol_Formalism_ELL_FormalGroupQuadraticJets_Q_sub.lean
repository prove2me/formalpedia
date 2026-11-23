-- Prove2me | solution 1 for Formalism.ELL.FormalGroupQuadraticJets.Q_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:42.786592+00:00
-- url     : https://prove2.me/submissions/d5b7f80f-75f9-469b-a3c1-0da7a268e8a3

import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.FormalGroupQuadraticJets
open Formalism.G.LogCR
variable {K : Type*} [CommRing K]
namespace Formalism.ELL.FormalGroupQuadraticJets
theorem _root_.solution (f g : MvPowerSeries (Fin 2) K) : Q (f - g) = Q f - Q g := by
  simp [Q, map_sub]
end Formalism.ELL.FormalGroupQuadraticJets
