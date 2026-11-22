-- Prove2me | solution 1 for Formalism.MainNotions.S.Loc.Pt.cast_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:19:50.587971+00:00
-- url     : https://prove2.me/submissions/04d9c5e9-a469-46f9-a410-78767906b587

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
open Formalism.MainNotions.S.Loc.Pt
namespace Formalism.MainNotions.S.Loc.Pt
theorem _root_.solution {n n' : ℕ} (e : n = n') (w : Pt E n) : (w.cast e).blocks = w.blocks := rfl
end Formalism.MainNotions.S.Loc.Pt
