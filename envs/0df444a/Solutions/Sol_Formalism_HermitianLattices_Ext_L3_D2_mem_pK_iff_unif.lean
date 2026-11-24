-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.mem_pK_iff_unif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:58:06.507737+00:00
-- url     : https://prove2.me/submissions/9f6b79e0-0d75-49f7-911f-ea459c7da6df

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_pK
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mul_mem_pK
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_mul_dvd_unif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_unif_ne_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_unif_pow_mem_pK
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_algebraMap_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π : 𝓞 F} (hπ : π ∈ 𝔭) (hπ' : π ∉ 𝔭 ^ 2)
    {k : ℕ} {a : K} :
    a ∈ pK K 𝔭 k ↔ ∃ b ∈ pK K 𝔭 0, a = algebraMap F K (π : F) ^ k * b := by
  constructor
  · intro ha
    obtain ⟨t, ht, z, hz, e⟩ := (mem_pK h𝔭).1 ha
    obtain ⟨s, hs, hdvd⟩ := exists_mul_dvd_unif h𝔭 hπ hπ' k
    have h1 : Ideal.span {ι s} * extP K 𝔭 ^ k ≤ Ideal.span {ι (π ^ k)} := by
      have h2 : Ideal.span {s} * 𝔭 ^ k ≤ Ideal.span {π ^ k} := by
        rw [Ideal.span_singleton_mul_le_iff]
        intro x hx
        exact Ideal.mem_span_singleton.2 (hdvd x hx)
      have := Ideal.map_mono (f := ι) h2
      rwa [Ideal.map_mul, Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton,
        Ideal.map_pow] at this
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1
      (h1 (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hz))
    have hπ0 := unif_ne_zero (K := K) hπ'
    refine ⟨a / algebraMap F K (π : F) ^ k, ?_, by field_simp⟩
    refine (mem_pK h𝔭).2 ⟨s * t, fun h => (h𝔭.isPrime.mem_or_mem h).elim hs ht, w, by simp, ?_⟩
    have e2 := congrArg (algebraMap (𝓞 K) K) hw
    rw [map_mul, map_mul, e, MeanB.algebraMap_comp, MeanB.algebraMap_comp,
      show ((π ^ k : 𝓞 F) : F) = (π : F) ^ k from rfl, map_pow] at e2
    rw [show ((s * t : 𝓞 F) : F) = (s : F) * (t : F) from rfl, map_mul]
    field_simp
    linear_combination -e2
  · rintro ⟨b, hb, rfl⟩
    have := mul_mem_pK h𝔭 (unif_pow_mem_pK (K := K) hπ k) hb
    simpa using this
end Formalism.HermitianLattices.Ext.L3.D2
