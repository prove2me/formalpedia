-- Prove2me | solution 1 for Formalism.L2.S.Pv.PsiTrCore.intAf_le_congSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:20:13.657551+00:00
-- url     : https://prove2.me/submissions/019da7ed-5301-4e23-a388-73f8ea3a3749

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LevelCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_PsiTrCoreApprox
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_PsiTrCoreTrace
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_PsiTrCore
import Theorems.Thm_Formalism_L2_S_Pv_PsiTrCore_one_tmul_mem
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_L2_S_Pv_PsiTrCore_exists_approx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.PsiTrCore
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace Formalism.L2.S.Pv.PsiTrCore
theorem _root_.solution (n : ℤ) (hn : n ≠ 0) : IntAf F E ≤ congSub n := by
  show Formalism.UG.tensInt (F := F) (Af F) (Formalism.UG.intOE E) (Formalism.UG.intAd F) ≤ congSub n
  unfold Formalism.UG.tensInt
  rw [Subring.closure_le]
  rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
  · obtain ⟨o, rfl⟩ := hx
    refine ⟨o, 0, zero_mem _, ?_⟩
    simp [Formalism.UG.inclE]
  · have hc' : ∀ v, c v ∈ v.adicCompletionIntegers F := hc
    have hnF : (n : F) ≠ 0 := by exact_mod_cast hn
    obtain ⟨b, hb⟩ := exists_approx c hc' (n : 𝓞 F) (by exact_mod_cast hn)
    set c' : Af F := (c - algebraMap F (Af F) (b : F)) * algebraMap F (Af F) ((n : F)⁻¹) with hc'def
    have h1 : (n : Af F) * algebraMap F (Af F) ((n : F)⁻¹) = 1 := by
      rw [← map_intCast (algebraMap F (Af F)) n, ← map_mul, mul_inv_cancel₀ hnF, map_one]
    have key : (n : Af F) * c' = c - algebraMap F (Af F) (b : F) := by
      calc (n : Af F) * c'
          = (c - algebraMap F (Af F) (b : F)) * ((n : Af F) * algebraMap F (Af F) ((n : F)⁻¹)) := by
            rw [hc'def]; ring
        _ = c - algebraMap F (Af F) (b : F) := by rw [h1, mul_one]
    have hc'int : ∀ v, c' v ∈ v.adicCompletionIntegers F := by
      intro v
      have e : c' v = (c v - algebraMap F (v.adicCompletion F) (b : F)) *
          algebraMap F (v.adicCompletion F) ((n : F)⁻¹) := by
        rw [hc'def]; rfl
      have hnv : Valued.v (algebraMap F (v.adicCompletion F) (n : F)) = v.intValuation (n : 𝓞 F) := by
        rw [← map_intCast (algebraMap (𝓞 F) F) n]
        exact (v.valuedAdicCompletion_eq_valuation' _).trans (v.valuation_of_algebraMap _)
      have hn0 : v.intValuation (n : 𝓞 F) ≠ 0 := by
        rw [← hnv, Valuation.ne_zero_iff]
        exact (map_ne_zero (algebraMap F (v.adicCompletion F))).mpr hnF
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, e, map_mul, map_inv₀, map_inv₀, hnv]
      calc Valued.v (c v - algebraMap F (v.adicCompletion F) (b : F)) * (v.intValuation (n : 𝓞 F))⁻¹
          ≤ v.intValuation (n : 𝓞 F) * (v.intValuation (n : 𝓞 F))⁻¹ := by gcongr; exact hb v
        _ = 1 := mul_inv_cancel₀ hn0
    have hB : Formalism.UG.inclE (F := F) (Af F) ((algebraMap (𝓞 F) (𝓞 E) b : 𝓞 E) : E) =
        (1 : E) ⊗ₜ[F] algebraMap F (Af F) (b : F) := by
      have hcoe : ((algebraMap (𝓞 F) (𝓞 E) b : 𝓞 E) : E) = algebraMap F E (b : F) := by
        first
        | rfl
        | simp [RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
      rw [hcoe]
      simp only [Formalism.UG.inclE, Algebra.TensorProduct.includeLeftRingHom_apply]
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    have hn' : ((n : ℤ) : E ⊗[F] Af F) = (1 : E) ⊗ₜ[F] (n : Af F) := by
      rw [← Algebra.TensorProduct.includeRight_apply, map_intCast]
    refine ⟨algebraMap (𝓞 F) (𝓞 E) b, (1 : E) ⊗ₜ[F] c', one_tmul_mem c' hc'int, ?_⟩
    rw [hB, hn', Algebra.TensorProduct.tmul_mul_tmul, one_mul, key, ← TensorProduct.tmul_add]
    congr 1
    abel
end Formalism.L2.S.Pv.PsiTrCore
