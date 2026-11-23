-- Prove2me | solution 1 for Formalism.MainNotions.S.Loc.Model.Kk_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:30.446962+00:00
-- url     : https://prove2.me/submissions/fc959573-e232-41cb-a3cf-c23763c76429

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_Point
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ComplexConjugate
open Formalism Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
open Formalism.MainNotions.S.Loc.Model
namespace Formalism.MainNotions.S.Loc.Model
theorem _root_.solution (M : Model F E) (m : ℕ) (w w' : Pt E (m + 1)) :
    M.Kk (m + 1) w w' = ∑' c : M.Cls m, M.BB w c * conj (M.BB w' c) / (M.nAut c : ℂ) := rfl
end Formalism.MainNotions.S.Loc.Model
