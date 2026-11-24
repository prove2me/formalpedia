-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.mem_noncompactPart_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:15.348885+00:00
-- url     : https://prove2.me/submissions/90460166-8491-4033-82c1-1f310dbbaf0d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SpanPowMulLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NeZeroOfNotMem
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_HU_j__ne_zero_24401b7f8ede
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_ne_zero_of_notMem
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_mem_SP
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_mem_SP
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_span_pow_mul_le
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} [h𝔭 : 𝔭.IsPrime] {π₀ s₀ : 𝓞 F} (hu : IsUnif0 𝔭 π₀ s₀) (k : ℕ)
    (a : K) : InP 𝔭 k a ↔ ∃ s ∈ SP K 𝔭, a = jK (ι π₀) ^ k * s := by
  have hp : 𝔭.IsPrime := h𝔭
  constructor
  · rintro ⟨t, ht, z, hz, e⟩
    have hmem : ι (s₀ ^ k) * z ∈ Ideal.span {ι (π₀ ^ k)} :=
      span_pow_mul_le hu.le k (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hz)
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hmem
    have htu : t * s₀ ^ k ∉ 𝔭 := fun hm =>
      (hp.mem_or_mem hm).elim ht (fun h => hu.s_notMem (hp.mem_of_pow_mem k h))
    have hd : jK (ι (t * s₀ ^ k)) ≠ 0 := jι_ne_zero (ne_zero_of_notMem htu)
    refine ⟨jK w / jK (ι (t * s₀ ^ k)), mem_SP.mpr ⟨t * s₀ ^ k, htu, w, ?_⟩, ?_⟩
    · rw [mul_div_assoc', eq_div_iff hd, mul_comm]
    · have hw' := congrArg jK hw
      simp only [map_mul, map_pow] at hw'
      rw [mul_div_assoc', eq_div_iff hd]
      simp only [map_mul, map_pow]
      linear_combination -hw' - jK (ι s₀) ^ k * e
  · rintro ⟨s, hs, rfl⟩
    have h1 : InP 𝔭 k (jK (ι π₀) ^ k) := by
      rw [← map_pow]
      exact inP_jK (Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hu.mem) k)
    have h2 := h1.mul (show InP 𝔭 0 s from hs)
    simpa using h2
end Formalism.HermitianLattices.Ext.L3.HU
