-- Prove2me | solution 1 for Formalism.L2.DIV.fixed_field_is_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:27:43.591339+00:00
-- url     : https://prove2.me/submissions/c0e9a38e-e1c5-480f-9ec3-5f94076800b8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_tensor_conjugation_tmul
import Theorems.Thm_Formalism_L2_DIV_conjugation_fixed_mem_range
import Theorems.Thm_Formalism_L2_DIV_include_right_injective_of_field
import Theorems.Thm_Formalism_L2_DIV_conjugation_units_val
import Theorems.Thm_Formalism_L2_DIV_mem_ker_norm_quotient_iff

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
namespace Formalism.L2.DIV
theorem _root_.solution : FixedIsIdF := by
  intro F E _ _ _ _ _ σ hσ
  ext x
  rw [mem_ker_norm_quotient_iff]
  constructor
  · intro hx
    have h1 : sigR σ (FiniteAdeleRing (𝓞 F) F) (x : AfE F E) = x := by
      rw [← conjugation_units_val, hx]
    have h2 : sigR σ (FiniteAdeleRing (𝓞 F) F) ((x⁻¹ : (AfE F E)ˣ) : AfE F E) = ((x⁻¹ : (AfE F E)ˣ) : AfE F E) := by
      rw [← conjugation_units_val, map_inv, hx]
    obtain ⟨r, hr⟩ := conjugation_fixed_mem_range σ hσ _ _ h1
    obtain ⟨s, hs⟩ := conjugation_fixed_mem_range σ hσ _ _ h2
    have hrs : r * s = 1 := by
      apply include_right_injective_of_field (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
      rw [map_mul, map_one]
      erw [hr, hs]
      exact x.mul_inv
    refine ⟨⟨r, s, hrs, by rw [mul_comm]; exact hrs⟩, ?_⟩
    apply Units.ext
    exact hr
  · rintro ⟨r, rfl⟩
    apply Units.ext
    rw [conjugation_units_val]
    show sigR σ (FiniteAdeleRing (𝓞 F) F) ((1 : E) ⊗ₜ[F] (r : FiniteAdeleRing (𝓞 F) F)) = (1 : E) ⊗ₜ[F] (r : FiniteAdeleRing (𝓞 F) F)
    rw [tensor_conjugation_tmul, map_one]
end Formalism.L2.DIV
