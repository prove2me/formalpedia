-- Prove2me | solution 1 for Formalism.L2.DIV.b_mul_mem_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:26:43.424806+00:00
-- url     : https://prove2.me/submissions/a3e8b5d4-44cb-4f85-89e4-3daca37a392a

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
namespace Formalism.L2.DIV
theorem _root_.solution (P : Ideal (𝓞 E)) (c : 𝓞 E) (hc : c ∈ P) (t : RInt F E) :
    toRInt F E c * t ∈ P.map (toRInt F E) := by
  have h1 : toRInt F E c ∈ P.map (toRInt F E) := Ideal.mem_map_of_mem _ hc
  first
  | exact Ideal.mul_mem_right _ _ h1
  | exact Ideal.mul_mem_right t _ h1
  | exact Ideal.mul_mem_right t h1
  | exact (P.map (toRInt F E)).mul_mem_right t h1
end Formalism.L2.DIV
