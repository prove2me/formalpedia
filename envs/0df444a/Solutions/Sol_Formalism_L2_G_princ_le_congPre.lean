-- Prove2me | solution 1 for Formalism.L2.G.princ_le_congPre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:01:33.043297+00:00
-- url     : https://prove2.me/submissions/616cfdb4-5185-408d-999c-3956e2241738

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelCharts_SignBlockDeterminant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.G
variable {A R : Type} [CommRing A] [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.L2.G
theorem _root_.solution (ι : R →+* A) (I : Ideal R) (H : Subgroup (GL n (R ⧸ I))) : princ ι I ≤ congPre ι I H :=
  Subgroup.map_mono (Subgroup.comap_mono bot_le)
end Formalism.L2.G
