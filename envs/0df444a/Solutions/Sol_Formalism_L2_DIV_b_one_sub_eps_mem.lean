-- Prove2me | solution 1 for Formalism.L2.DIV.b_one_sub_eps_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:32:28.222798+00:00
-- url     : https://prove2.me/submissions/fb81c380-e2e2-4394-af56-ba361f7dca52

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_b_off_inv
import Theorems.Thm_Formalism_L2_DIV_b_pi
import Theorems.Thm_Formalism_L2_DIV_b_mul_mem_map

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) : 1 - bEps E v ∈ P.asIdeal.map (toRInt F E) := by
  obtain ⟨π, hπ, hπv⟩ := b_pi v
  obtain ⟨ρ, hρ⟩ := b_off_inv (E := E) v π hπv
  rw [← hρ]
  rw [← hP] at hπ
  exact b_mul_mem_map P.asIdeal (algebraMap (𝓞 F) (𝓞 E) π) hπ ρ
end Formalism.L2.DIV
