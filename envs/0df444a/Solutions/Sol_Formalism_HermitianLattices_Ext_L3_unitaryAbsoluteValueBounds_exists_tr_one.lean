-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.exists_tr_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:19.806792+00:00
-- url     : https://prove2.me/submissions/7f9733df-aae0-4e0f-a201-bd1132872f9b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemRangeLinPart
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityField
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanA_exists_mul_sub_one_mem_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_conjO
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
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
open NormLifting
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {a : 𝓞 K} (ha : a ∉ extP K 𝔭) (N : ℕ) :
    ∃ b : 𝓞 K, conjO K a * b + conjO K b * a - 1 ∈ extP K 𝔭 ^ N := by
  obtain ⟨θ, hθ⟩ := idealPowerSpanBounds.exists_theta hK hF h𝔭
  have h1 : ∃ b : 𝓞 K, conjO K a * b + conjO K b * a ∉ extP K 𝔭 := by
    by_contra hcon
    push Not at hcon
    have e1 := hcon 1
    have e2 := hcon θ
    apply ha
    have e3 : (θ - conjO K θ) * a ∈ extP K 𝔭 ^ 1 := by
      rw [pow_one]
      have := (extP K 𝔭).sub_mem ((extP K 𝔭).mul_mem_left θ e1) e2
      have e : θ * (conjO K a * 1 + conjO K 1 * a) - (conjO K a * θ + conjO K θ * a) =
          (θ - conjO K θ) * a := by rw [map_one]; ring
      rwa [e] at this
    have := idealPowerSpanBounds.mem_of_unit_mul_mem hθ e3
    rwa [pow_one] at this
  obtain ⟨b, hb⟩ := h1
  obtain ⟨c, hc⟩ := idealPowerSpanBounds.exists_tr hF (conjO K a * b)
  rw [map_mul, conjO_conjO, mul_comm a] at hc
  have hc𝔭 : c ∉ 𝔭 := by
    intro h
    apply hb
    rw [← hc]
    exact Ideal.mem_map_of_mem _ h
  obtain ⟨u, hu⟩ := MeanA.exists_mul_sub_one_mem_pow h𝔭 hc𝔭 N
  refine ⟨ι u * b, ?_⟩
  have e : conjO K a * (ι u * b) + conjO K (ι u * b) * a - 1 = ι (u * c - 1) := by
    rw [map_mul (conjO K), idealPowerSpanBounds.conjO_map hF, map_sub, map_mul, map_one, hc]
    ring
  rw [e, idealPowerSpanBounds.mem_pow_iff]
  exact hu
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
