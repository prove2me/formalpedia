-- Prove2me | solution 1 for Formalism.IndefR.Eqv.G5.adl_norm_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:39.242584+00:00
-- url     : https://prove2.me/submissions/11b39d46-5f80-4a2f-9b9e-13b567e32144

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_ExistsDenOfIsCompactAdele
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IntAdCpctOpen
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_AdlEqZeroOfMemNbhd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.IndefR Formalism.IndefR.Eqv Formalism.IndefR.Eqv.G5
variable {F : Type} [Field F] [NumberField F]
open scoped AdeleRing
namespace Formalism.IndefR.Eqv.G5
theorem _root_.solution (x : F) (w : InfinitePlace F) :
    ‖(algebraMap F (InfiniteAdeleRing F) x) w‖ = w x := by
  simp [InfiniteAdeleRing.algebraMap_apply]
  first | rfl | simp [WithAbs.equiv, WithAbs.toAbs]
end Formalism.IndefR.Eqv.G5
