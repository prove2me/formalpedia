-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.PinAA.mul_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:42:57.075541+00:00
-- url     : https://prove2.me/submissions/bcfd559c-04f3-4d00-b82c-f0ac8c4228ed

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoMeanAlphaN
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulEqZeroIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinAA_rd_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localValuationFiltration_mem_pow_vF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localValuationFiltration_notMem_pow_vF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_reductionMapsOfForms_absNorm_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Module Matrix
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.PinAA
open HermitianSublattices LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans localValuationFiltration
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
private theorem iota_mul_mem_extP_pow_iff_mem_pow_sub_vF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0)
    {k : ℕ} (hk : vF 𝔭 c ≤ k) (x : 𝓞 K) :
    ι c * x ∈ extP K 𝔭 ^ k ↔ x ∈ extP K 𝔭 ^ (k - vF 𝔭 c) := by
  constructor
  · intro h
    obtain ⟨J, hJ⟩ : 𝔭 ^ vF 𝔭 c ∣ Ideal.span {c} :=
      Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr (localValuationFiltration.mem_pow_vF h𝔭 hc))
    have hJp : ¬ J ≤ 𝔭 := by
      intro hle
      apply localValuationFiltration.notMem_pow_vF h𝔭 hc
      have hle' : Ideal.span {c} ≤ 𝔭 ^ (vF 𝔭 c + 1) := by
        rw [hJ, pow_succ]; exact Ideal.mul_mono_right hle
      exact hle' (Ideal.mem_span_singleton_self c)
    have hcop : IsCoprime 𝔭 J := by
      rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      exact hJp (le_sup_right.trans (h𝔭.eq_of_le hne le_sup_left).symm.le)
    have hcopK : IsCoprime (extP K 𝔭) (J.map ι) := by
      rw [Ideal.isCoprime_iff_sup_eq] at hcop ⊢
      show 𝔭.map ι ⊔ J.map ι = ⊤
      rw [← Ideal.map_sup, hcop, Ideal.map_top]
    have hinj : Function.Injective ι := FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)
    have h𝔭0 : 𝔭 ≠ ⊥ := by
      intro h0
      have := reductionMapsOfForms.absNorm_pos h𝔭
      rw [h0, Ideal.absNorm_bot] at this
      exact lt_irrefl _ this
    have hP0 : extP K 𝔭 ≠ ⊥ := by
      show 𝔭.map ι ≠ ⊥
      rwa [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
    have hsc : Ideal.span {ι c} = (Ideal.span {c}).map ι := by
      rw [Ideal.map_span, Set.image_singleton]
    have hspan : Ideal.span {ι c * x} =
        extP K 𝔭 ^ vF 𝔭 c * (J.map ι * Ideal.span {x}) := by
      rw [← Ideal.span_singleton_mul_span_singleton, hsc, hJ, Ideal.map_mul, Ideal.map_pow,
        mul_assoc]
      rfl
    have hle : extP K 𝔭 ^ k ∣ Ideal.span {ι c * x} :=
      Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr h)
    rw [hspan, show k = vF 𝔭 c + (k - vF 𝔭 c) by omega, pow_add] at hle
    have h2 := (mul_dvd_mul_iff_left (pow_ne_zero _ hP0)).mp hle
    have h3 := (hcopK.pow_left (m := k - vF 𝔭 c)).dvd_of_dvd_mul_left h2
    exact (Ideal.span_singleton_le_iff_mem _).mp (Ideal.dvd_iff_le.mp h3)
  · intro h
    have h' := Ideal.mul_mem_mul (localizedQuotients.ι_mem_pow (K := K) (localValuationFiltration.mem_pow_vF h𝔭 hc)) h
    rwa [← pow_add, show vF 𝔭 c + (k - vF 𝔭 c) = k by omega] at h'
variable {κ : Type} [Fintype κ] [DecidableEq κ] [Fact (IsFixF K F)]
end Formalism.HermitianLattices.Ext.L3.PinAA
end
end

set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.PinAA
open HermitianSublattices LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans localValuationFiltration
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.PinAA
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) {k : ℕ}
    (hk : vF 𝔭 c ≤ k) (z : 𝓞 K ⧸ extP K 𝔭 ^ k) :
    Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι c) * z = 0 ↔ rd K 𝔭 k (vF 𝔭 c) z = 0 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [← map_mul, rd_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem]
  exact iota_mul_mem_extP_pow_iff_mem_pow_sub_vF h𝔭 hc hk x
end Formalism.HermitianLattices.Ext.L3.PinAA
