-- Prove2me | solution 1 for Formalism.L2.DIV.c_lat_frac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:32:21.505396+00:00
-- url     : https://prove2.me/submissions/aec8bc50-739a-422e-9290-8980cef8fe22

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_UG_P_adelstab_algebraMap_ne_zero
import Theorems.Thm_Formalism_UG_P_adelstab_incl_C
import Theorems.Thm_Formalism_UG_P_csGlob_int
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
theorem _root_.solution (x : (AfE F E)ˣ) : IsFractional (𝓞 E)⁰ (c_lat x) := by
  obtain ⟨d, hd, hdx⟩ := levelaf_denom (E := E) (x : AfE F E)
  refine ⟨algebraMap (𝓞 F) (𝓞 E) d, ?_, ?_⟩
  · rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h
    apply adelstab_algebraMap_ne_zero (E := E) d hd
    rw [IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, h, map_zero]
  · intro b hb
    have h1 : ιE (algebraMap (𝓞 F) (𝓞 E) d • b) ∈ RInt F E := by
      have : ιE (algebraMap (𝓞 F) (𝓞 E) d • b) =
          (levelafC E d * (x : AfE F E)) * (((x⁻¹ : (AfE F E)ˣ) : AfE F E) * ιE b) := by
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, adelstab_incl_C]
        have := x.mul_inv
        linear_combination (-(levelafC E d * ιE b)) * this
      rw [this]; exact mul_mem hdx hb
    have h2 := csGlob_int _ h1
    exact ⟨IsIntegralClosure.mk' (𝓞 E) _ h2, IsIntegralClosure.algebraMap_mk' _ _ _⟩
end Formalism.L2.DIV
