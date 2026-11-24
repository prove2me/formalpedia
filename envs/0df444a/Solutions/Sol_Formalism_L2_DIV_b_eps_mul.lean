-- Prove2me | solution 1 for Formalism.L2.DIV.b_eps_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:26:44.211544+00:00
-- url     : https://prove2.me/submissions/431e3e1b-b710-4c87-a2ad-78efaf919699

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_UG_P_afsplit_inj
import Theorems.Thm_Formalism_UG_P_afsplit_prV_eps


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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (z : AfE F E)
    (hz : ∀ v' : HeightOneSpectrum (𝓞 F), v' ≠ v → prV (E := E) v' z = 0) : afsplitEps E v * z = z := by
  rw [← sub_eq_zero]
  apply afsplit_inj
  intro w
  by_cases h : w = v
  · subst h
    rw [map_sub, map_mul, afsplit_prV_eps, one_mul, sub_self]
  · rw [map_sub, map_mul, hz w h, mul_zero, sub_self]
end Formalism.L2.DIV
