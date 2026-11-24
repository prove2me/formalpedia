-- Prove2me | solution 1 for Formalism.L2.DIV.c_mem_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:25:24.498547+00:00
-- url     : https://prove2.me/submissions/3f45e8f1-1060-4027-b297-70b93213d1ec

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.DIV
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "ιE" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.L2.DIV
theorem _root_.solution (x : (AfE F E)ˣ) (e : E) :
    e ∈ c_lat x ↔ ((x⁻¹ : (AfE F E)ˣ) : AfE F E) * ιE e ∈ RInt F E := Iff.rfl
end Formalism.L2.DIV
