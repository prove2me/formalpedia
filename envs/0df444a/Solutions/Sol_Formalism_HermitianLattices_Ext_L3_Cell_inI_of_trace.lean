-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.Cell.inI_of_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:59:38.91917+00:00
-- url     : https://prove2.me/submissions/d6896c03-df3f-40cd-b7a5-4b2338e5401f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CongrPIffInI
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_InI_of_mul
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_sub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_sub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_int
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_sub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_sub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_eq_iff_mem_range
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_conjO_mem_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_exists_theta
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_of_unit_mul_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_pow_iff
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
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}
namespace Formalism.HermitianLattices.Ext.L3.Cell
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {z : K}
    (h : ∀ c : 𝓞 K, InI 𝔭 k (κ c * z + star (κ c * z))) : InI 𝔭 k z := by
  have hp := h𝔭.isPrime
  obtain ⟨θ, hθ⟩ := exists_theta hK hF h𝔭
  set δ := θ - conjO K θ with hδ
  have h1 : InI 𝔭 k (κ δ * z) := by
    have e : κ δ * z = (κ θ * z + star (κ θ * z)) - κ (conjO K θ) * (κ 1 * z + star (κ 1 * z)) := by
      have : κ (conjO K θ) = star (κ θ) := rfl
      rw [hδ, map_sub, this, map_one, one_mul, star_mul']
      ring
    rw [e]
    have h2 := InI.mul hp (InI.int hp (conjO K θ)) (h 1)
    rw [zero_add] at h2
    exact (h θ).sub hp h2
  obtain ⟨ν, hν⟩ := (conjO_eq_iff_mem_range hF (δ * conjO K δ)).1 (by
    rw [map_mul, conjO_conjO, mul_comm])
  have hνp : ν ∉ 𝔭 := by
    intro hm
    have h3 : δ * conjO K δ ∈ extP K 𝔭 ^ 1 := by rw [← hν]; exact ι_mem_pow (by simpa using hm)
    have h4 : conjO K δ ∈ extP K 𝔭 ^ 1 := mem_of_unit_mul_mem hθ h3
    have h5 : δ ∈ extP K 𝔭 ^ 1 := by
      have := conjO_mem_pow hF 𝔭 1 _ h4
      rwa [conjO_conjO] at this
    have h6 : (1 : 𝓞 K) ∈ extP K 𝔭 ^ 1 := mem_of_unit_mul_mem hθ (by rwa [mul_one])
    have h7 := (mem_pow_iff (K := K) 𝔭 1 1).1 (by rwa [map_one])
    rw [pow_one] at h7
    exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h7)
  apply InI.of_mul hp hνp
  have h8 := InI.mul hp (InI.int hp (conjO K δ)) h1
  rw [zero_add] at h8
  have : κ (ι ν) * z = κ (conjO K δ) * (κ δ * z) := by rw [hν, map_mul]; ring
  rw [this]
  exact h8
end Formalism.HermitianLattices.Ext.L3.Cell
