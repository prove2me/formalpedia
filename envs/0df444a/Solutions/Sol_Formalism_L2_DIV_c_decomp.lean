-- Prove2me | solution 1 for Formalism.L2.DIV.c_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:42:50.40128+00:00
-- url     : https://prove2.me/submissions/3cdced5b-5bb1-4e84-9e4e-cfcd10215058

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_c_mem_lat
import Theorems.Thm_Formalism_UG_P_adelstab_algebraMap_ne_zero
import Theorems.Thm_Formalism_UG_P_adelstab_incl_C
import Theorems.Thm_Formalism_UG_P_csGlob_approx
import Theorems.Thm_Formalism_UG_P_csGlob_intAdApprox
import Theorems.Thm_Formalism_UG_P_levelafC_mul
import Theorems.Thm_Formalism_UG_P_levelaf_denom


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
theorem _root_.solution (x : (AfE F E)ˣ) : ∃ e₁ ∈ c_lat x, ∃ e₂ ∈ c_lat x, e₂ ≠ 0 ∧ ∃ t ∈ RInt F E,
    (x : AfE F E) = ιE e₁ + ιE e₂ * t := by
  obtain ⟨d₁, hd₁, hx₁⟩ := levelaf_denom (E := E) (x : AfE F E)
  obtain ⟨d₂, hd₂, hx₂⟩ := levelaf_denom (E := E) ((x⁻¹ : (AfE F E)ˣ) : AfE F E)
  obtain ⟨b, t, ht, hbt⟩ := csGlob_approx csGlob_intAdApprox (d₁ * d₂) (mul_ne_zero hd₁ hd₂) _ hx₁
  have hne₁ := adelstab_algebraMap_ne_zero (E := E) d₁ hd₁
  have hne₂ := adelstab_algebraMap_ne_zero (E := E) d₂ hd₂
  have h2 : algebraMap (𝓞 F) E d₂ ∈ c_lat x := by
    rw [c_mem_lat, adelstab_incl_C, mul_comm]; exact hx₂
  have hinv : ιE (algebraMap (𝓞 F) E d₁)⁻¹ * levelafC E d₁ = 1 := by
    rw [← adelstab_incl_C, ← map_mul, inv_mul_cancel₀ hne₁, map_one]
  have hx : (x : AfE F E) = ιE ((algebraMap (𝓞 F) E d₁)⁻¹ * algebraMap (𝓞 E) E b) +
      ιE (algebraMap (𝓞 F) E d₂) * t := by
    rw [levelafC_mul] at hbt
    rw [map_mul, adelstab_incl_C]
    linear_combination (ιE (algebraMap (𝓞 F) E d₁)⁻¹) * hbt + ((levelafC E d₂) * t - (x : AfE F E)) * hinv
  refine ⟨_, ?_, _, h2, hne₂, t, ht, hx⟩
  rw [c_mem_lat]
  have h3 : ιE ((algebraMap (𝓞 F) E d₁)⁻¹ * algebraMap (𝓞 E) E b) =
      (x : AfE F E) - ιE (algebraMap (𝓞 F) E d₂) * t := by rw [hx]; ring
  rw [h3, mul_sub, x.inv_mul, ← mul_assoc]
  exact sub_mem (one_mem _) (mul_mem h2 ht)
end Formalism.L2.DIV
