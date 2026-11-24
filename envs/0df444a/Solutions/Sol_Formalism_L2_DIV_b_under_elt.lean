-- Prove2me | solution 1 for Formalism.L2.DIV.b_under_elt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:25:22.276612+00:00
-- url     : https://prove2.me/submissions/c058a23e-1656-4e0a-84a3-17caa33dba8f

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
theorem _root_.solution (P : HeightOneSpectrum (𝓞 E)) :
    ∃ D : 𝓞 F, D ≠ 0 ∧ algebraMap (𝓞 F) (𝓞 E) D ∈ P.asIdeal := by
  have hne : P.asIdeal.under (𝓞 F) ≠ ⊥ := Ideal.under_ne_bot (𝓞 F) P.ne_bot
  obtain ⟨D, hD, hD0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨D, hD0, hD⟩
end Formalism.L2.DIV
