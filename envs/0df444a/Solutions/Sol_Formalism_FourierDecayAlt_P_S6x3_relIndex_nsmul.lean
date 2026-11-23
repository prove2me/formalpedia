-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x3.relIndex_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:31.637928+00:00
-- url     : https://prove2.me/submissions/0a62fb23-b411-4d02-b0ea-63aa2d27a661

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FinrankLeOfMapLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x3
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.S6x3
theorem _root_.solution (N : Submodule ℤ E) [Module.Finite ℤ N] (g : ℕ) :
    (N.toAddSubgroup.map (nsmulAddMonoidHom (α := E) g)).relIndex N.toAddSubgroup
      = g ^ finrank ℤ N := by
  have h1 : Module.Finite ℤ ↥(AddSubgroup.toIntSubmodule N.toAddSubgroup) :=
    inferInstanceAs (Module.Finite ℤ N)
  have h2 : Module.Free ℤ ↥(AddSubgroup.toIntSubmodule N.toAddSubgroup) := inferInstance
  exact AddSubgroup.relIndex_map_nsmul g N.toAddSubgroup
end Formalism.FourierDecayAlt.P.S6x3
