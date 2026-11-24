-- Prove2me | solution 1 for Formalism.L2.Fam.IdTrans.isOpen_integers
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:56.016961+00:00
-- url     : https://prove2.me/submissions/bc0bb38a-f929-44c4-8d8f-999c7fdb5465

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAe
import Definitions.Def_Formalism_LocalToGlobal_NumberFieldFamilies_IdTransSM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Filter Topology
open Formalism Formalism.L2 Formalism.L2.Fam Formalism.L2.Fam.IdTrans
variable {L : Type} [Field L] [NumberField L]
namespace Formalism.L2.Fam.IdTrans
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L)) :
    IsOpen (v.adicCompletionIntegers L : Set (v.adicCompletion L)) := by
  exact Valued.isOpen_integer _
end Formalism.L2.Fam.IdTrans
