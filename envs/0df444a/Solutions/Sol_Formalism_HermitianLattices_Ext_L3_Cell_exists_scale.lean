-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.Cell.exists_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:13:32.494795+00:00
-- url     : https://prove2.me/submissions/dc62d35a-4a9d-44ee-af88-4d96607b61f1

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CongrPIffInI
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsAddConjTransposeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOfNormRepCountNeZero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_InI_of_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_exists_frac
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_IsE_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_ne_zero_of_notMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_div
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_div
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_ne_zero_of_notMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mul_notMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_ne_bot
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_Cell_inI___dc4ac2cc5e49
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_WCA____ne_zero_cf941fa073ca
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_localizedQuotients_star___0cafaf6bb2bd


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.Cell
open LocalSpans idealPowerSpanBounds localizedQuotients WCA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)}
namespace Formalism.HermitianLattices.Ext.L3.Cell
theorem _root_.solution (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {a₁ : 𝓞 F} {r k : ℕ}
    (h1 : a₁ ∈ 𝔭 ^ (r + r + k)) (h2 : a₁ ∉ 𝔭 ^ (r + r + k + 1)) :
    ∃ μ : K, μ ≠ 0 ∧ star μ = μ ∧ ∃ a : 𝓞 F, μ * μ * κ (ι a₁) = κ (ι a) ∧ a ∉ 𝔭 ^ (k + 1) := by
  have hp := h𝔭.isPrime
  have hp0 := ne_bot h𝔭
  obtain ⟨g, hg, hg'⟩ := Ideal.exists_mem_pow_notMem_pow_succ 𝔭 hp0 h𝔭.ne_top r
  have hgg : g * g ∉ 𝔭 ^ (r + r + 1) := mul_notMem hp hp0 hg' hg'
  have hgg0 : g * g ≠ 0 := fun h0 => hgg (h0 ▸ zero_mem _)
  have hg0 : g ≠ 0 := fun h0 => hgg0 (by rw [h0, zero_mul])
  have hκg := κι_ne_zero (K := K) hg0
  have hκgg := κι_ne_zero (K := K) hgg0
  set d := (κ (ι (g * g)))⁻¹ * κ (ι a₁) with hd
  have hd1 : InI 𝔭 k d := InI.div h𝔭 hgg0 hgg ((inI_ι h𝔭).2 h1)
  have hd2 : ¬ InI 𝔭 (k + 1) d := by
    intro hcon
    apply h2
    rw [← inI_ι (K := K) h𝔭]
    have e : κ (ι a₁) = κ (ι (g * g)) * d := by rw [hd]; field_simp
    rw [e, add_assoc]
    refine InI.mul hp ((inI_ι h𝔭).2 ?_) hcon
    rw [pow_add]
    exact Ideal.mul_mem_mul hg hg
  have hds : star d = d := by rw [hd, star_mul', star_inv₀, star_ι hF, star_ι hF]
  obtain ⟨t, δ, ht, e⟩ := exists_frac hF hds (hd1.mono (Nat.zero_le _))
  have hκt := κι_ne_zero (K := K) (ne_zero_of_notMem ht)
  refine ⟨κ (ι t) * (κ (ι g))⁻¹, mul_ne_zero hκt (inv_ne_zero hκg), ?_, t * δ, ?_, ?_⟩
  · rw [star_mul', star_inv₀, star_ι hF, star_ι hF]
  · rw [map_mul ι, map_mul κ, e, hd, map_mul ι g g, map_mul κ]
    field_simp
  · intro hcon
    apply hd2
    apply InI.of_mul hp ht
    apply InI.of_mul hp ht
    rw [← e, ← map_mul, ← map_mul]
    exact (inI_ι h𝔭).2 hcon
end Formalism.HermitianLattices.Ext.L3.Cell
