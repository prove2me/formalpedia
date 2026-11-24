-- Prove2me | solution 1 for Formalism.L2.DIV.b_eps_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:34:20.973406+00:00
-- url     : https://prove2.me/submissions/a6901eba-a099-4464-b4c2-362d8cf29144

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_b_loc_inv
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
    (hP : P.asIdeal.under (𝓞 F) ≠ v.asIdeal) : bEps E v ∈ P.asIdeal.map (toRInt F E) := by
  have : P.asIdeal.IsMaximal := P.isMaximal
  have hmax : (P.asIdeal.under (𝓞 F)).IsMaximal := Ideal.IsMaximal.under (𝓞 F) P.asIdeal
  have hnle : ¬ P.asIdeal.under (𝓞 F) ≤ v.asIdeal := fun hle =>
    hP (hmax.eq_of_le v.isPrime.ne_top hle)
  obtain ⟨π, hπ, hπv⟩ := SetLike.not_le_iff_exists.mp hnle
  obtain ⟨ρ, hρ⟩ := b_loc_inv (E := E) v π hπv
  rw [← hρ]
  exact b_mul_mem_map P.asIdeal (algebraMap (𝓞 F) (𝓞 E) π) hπ ρ
end Formalism.L2.DIV
