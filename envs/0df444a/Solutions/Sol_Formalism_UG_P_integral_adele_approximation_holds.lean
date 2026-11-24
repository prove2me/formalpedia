-- Prove2me | solution 1 for Formalism.UG.P.integral_adele_approximation_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:51:21.326847+00:00
-- url     : https://prove2.me/submissions/7f518c0d-a37f-46e5-a0f2-1087f003854e

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Theorems.Thm_Formalism_UG_P_csApprox_global
import Theorems.Thm_Formalism_UG_P_levelaf_algebraMap_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.CS.IntAdApprox := by
  intro F _ _ D hD a ha
  obtain ⟨r, hle⟩ := csApprox_global D hD a ha
  set y : FiniteAdeleRing (𝓞 F) F := algebraMap F _ (algebraMap (𝓞 F) F D)⁻¹ *
    (a - algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r) with hy
  refine ⟨r, y, fun v => ?_, ?_⟩
  · show algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F D)⁻¹ *
        (a v - algebraMap (𝓞 F) (v.adicCompletion F) r) ∈ _
    have hne : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 (levelaf_algebraMap_ne_zero v D hD)
    rw [mem_adicCompletionIntegers, Valuation.map_mul, map_inv₀, map_inv₀,
      ← IsScalarTower.algebraMap_apply]
    calc _ ≤ (Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D))⁻¹ *
          Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) := mul_le_mul_right (hle v) _
      _ = 1 := inv_mul_cancel₀ hne
  · have hD' : algebraMap (𝓞 F) F D ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hD
    rw [hy, IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F) D, ← mul_assoc,
      ← map_mul, mul_inv_cancel₀ hD', map_one, one_mul]
    ring
end Formalism.UG.P
