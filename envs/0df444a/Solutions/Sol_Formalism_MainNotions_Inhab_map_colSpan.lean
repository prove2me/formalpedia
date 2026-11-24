-- Prove2me | solution 1 for Formalism.MainNotions.Inhab.map_colSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:40:13.719256+00:00
-- url     : https://prove2.me/submissions/6c720ee9-4202-47ec-ab9c-2f9bd57eb09f

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_SharpRestriction_InertJacobiLevels_ExtraGat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Inhab
open Formalism.MainNotions.G MvPolynomial
variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
variable (P : Places p O Kf)
namespace Formalism.MainNotions.Inhab
theorem _root_.solution {R K : Type*} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (A g : Matrix (Fin k) (Fin k) K) :
    (colSpan R g).map ((Matrix.mulVecLin A).restrictScalars R) = colSpan R (A * g) := by
  unfold colSpan
  rw [Submodule.map_span, ← Set.range_comp]
  congr 1
end Formalism.MainNotions.Inhab
