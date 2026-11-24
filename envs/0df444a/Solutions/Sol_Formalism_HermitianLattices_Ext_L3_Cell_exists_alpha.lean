-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.Cell.exists_alpha
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:58:47.232882+00:00
-- url     : https://prove2.me/submissions/dfa71d36-2677-42f2-a120-99c6b24a5ba6

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CongrPIffInI
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsAddConjTransposeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOfNormRepCountNeZero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_exists_norm_congr
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_eq_iff_mem_range
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_add_conj_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mul_notMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_ne_bot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_pow_le_span_sup
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.Cell
open LocalSpans idealPowerSpanBounds localizedQuotients WCA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)}
namespace Formalism.HermitianLattices.Ext.L3.Cell
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {a a' : 𝓞 F}
    (ha : a ∈ 𝔭) (ha2 : a ∉ 𝔭 ^ 2) (ha' : a' ∈ 𝔭) (ha'2 : a' ∉ 𝔭 ^ 2) :
    ∃ α : 𝓞 K, ∃ ν : 𝓞 F, conjO K α * α = ι ν ∧ a * ν + a' ∈ 𝔭 ^ 2 ∧ a * ν + a' ∉ 𝔭 ^ 3 := by
  have hp := h𝔭.isPrime
  have hp0 := ne_bot h𝔭
  have h1 : -a' ∈ Ideal.span {a} ⊔ 𝔭 ^ 2 :=
    pow_le_span_sup hp hp0 (c := 1) (by simpa using ha2) 2 (by simpa using ha')
  obtain ⟨c, r, hr, e⟩ := Ideal.mem_span_singleton_sup.1 h1
  have hc : c ∉ 𝔭 := by
    intro hc
    apply ha'2
    have : a' = -(c * a + r) := by rw [e]; ring
    rw [this]
    refine neg_mem (add_mem ?_ hr)
    rw [pow_two]
    exact Ideal.mul_mem_mul hc ha
  obtain ⟨α₀, ν₀, hν₀, hνc⟩ := exists_norm_congr hK hF h𝔭 hc
  have hν₀p : ν₀ ∉ 𝔭 := fun h => hc (by simpa using sub_mem h hνc)
  have h2 : a * ν₀ + a' ∈ 𝔭 ^ 2 := by
    have : a * ν₀ + a' = a * (ν₀ - c) - r := by linear_combination e
    rw [this]
    refine sub_mem ?_ hr
    rw [pow_two]
    exact Ideal.mul_mem_mul ha hνc
  by_cases h3 : a * ν₀ + a' ∈ 𝔭 ^ 3
  · obtain ⟨τ, hτ⟩ := exists_add_conj_eq hK hF (1 : 𝓞 F)
    obtain ⟨t₂, ht₂⟩ := (conjO_eq_iff_mem_range hF (conjO K τ * τ)).1 (by
      rw [map_mul, conjO_conjO, mul_comm])
    refine ⟨α₀ * (1 + ι a * τ), ν₀ * (1 + a + a * a * t₂), ?_, ?_, ?_⟩
    · rw [map_mul, map_add, map_mul, map_one, conjO_map hF, map_mul ι, map_add ι, map_add ι, map_mul ι,
        map_mul ι, map_one, ← hν₀, ht₂]
      rw [map_one] at hτ
      linear_combination (conjO K α₀ * α₀ * ι a) * hτ
    · have : a * (ν₀ * (1 + a + a * a * t₂)) + a' =
          (a * ν₀ + a') + a * a * (ν₀ * (1 + a * t₂)) := by ring
      rw [this]
      refine add_mem h2 (Ideal.mul_mem_right _ _ ?_)
      rw [pow_two]
      exact Ideal.mul_mem_mul ha ha
    · intro hcon
      have h4 : a * a * a * (ν₀ * t₂) ∈ 𝔭 ^ 3 := by
        refine Ideal.mul_mem_right _ _ ?_
        rw [pow_succ, pow_two]
        exact Ideal.mul_mem_mul (Ideal.mul_mem_mul ha ha) ha
      have ha2' : a ∉ 𝔭 ^ (1 + 1) := by simpa using ha2
      have hν' : ν₀ ∉ 𝔭 ^ (0 + 1) := by simpa using hν₀p
      have h5 : a * a * ν₀ ∉ 𝔭 ^ 3 := by
        have := mul_notMem hp hp0 (mul_notMem hp hp0 ha2' ha2') hν'
        simpa using this
      apply h5
      have : a * a * ν₀ = (a * (ν₀ * (1 + a + a * a * t₂)) + a') - (a * ν₀ + a') -
          a * a * a * (ν₀ * t₂) := by ring
      rw [this]
      exact sub_mem (sub_mem hcon h3) h4
  · exact ⟨α₀, ν₀, hν₀, h2, h3⟩
end Formalism.HermitianLattices.Ext.L3.Cell
