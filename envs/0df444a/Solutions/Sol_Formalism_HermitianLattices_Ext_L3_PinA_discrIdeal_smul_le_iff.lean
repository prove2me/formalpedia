-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.PinA.discrIdeal_smul_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:50:26.079646+00:00
-- url     : https://prove2.me/submissions/f2c426e6-3786-4e31-bc4a-a9839076819c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulEqZeroIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DiscrIdealSmulLeIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinA_pow_notMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinA_gram_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_exists_gram
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_of_mul_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localValuationFiltration_mem_pow_vF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localValuationFiltration_notMem_pow_vF


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.PinA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.PinA
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0)
    (e : ℕ) :
    discrIdeal (algebraMap F K (c : F) • h) L ≤ extP K 𝔭 ^ (finrank K V * vF 𝔭 c + e) ↔
      discrIdeal h L ≤ extP K 𝔭 ^ e := by
  constructor
  · intro hle
    unfold discrIdeal
    rw [Ideal.span_le]
    rintro z ⟨x, hx, ez⟩
    apply idealPowerSpanBounds.mem_of_mul_mem h𝔭 (pow_notMem h𝔭 (localValuationFiltration.notMem_pow_vF h𝔭 hc) (finrank K V))
    apply hle
    exact Ideal.subset_span ⟨x, hx, by rw [gram_smul, map_mul, ez]⟩
  · intro hle
    unfold discrIdeal
    rw [Ideal.span_le]
    rintro z ⟨x, hx, ez⟩
    obtain ⟨g, -, hdet⟩ := LocF.exists_gram hLi x hx
    have hz : z = algebraMap (𝓞 F) (𝓞 K) (c ^ finrank K V) * g.det := by
      apply RingOfIntegers.coe_injective
      show algebraMap (𝓞 K) K z = algebraMap (𝓞 K) K _
      rw [ez, gram_smul, map_mul, hdet]
    have h1 : g.det ∈ extP K 𝔭 ^ e := hle (Ideal.subset_span ⟨x, hx, hdet⟩)
    have h2 : algebraMap (𝓞 F) (𝓞 K) (c ^ finrank K V) ∈ extP K 𝔭 ^ (finrank K V * vF 𝔭 c) := by
      apply localizedQuotients.ι_mem_pow
      rw [mul_comm, pow_mul]
      exact Ideal.pow_mem_pow (localValuationFiltration.mem_pow_vF h𝔭 hc) _
    show z ∈ _
    rw [hz, pow_add]
    exact Ideal.mul_mem_mul h2 h1
end Formalism.HermitianLattices.Ext.L3.PinA
