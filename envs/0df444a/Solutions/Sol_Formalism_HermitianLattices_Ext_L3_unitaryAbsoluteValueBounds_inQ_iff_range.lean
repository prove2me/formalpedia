-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.inQ_iff_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:27.529+00:00
-- url     : https://prove2.me/submissions/880578d0-5e01-4e6a-ae2a-fdeceec52378

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityField
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CntIOneOfNotMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_mulW_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_map_pow_le_span_sup


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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {ϖ : 𝓞 F} (h1 : ϖ ∈ 𝔭) (h2 : ϖ ∉ 𝔭 ^ 2)
    (j : ℕ) (a : AQ K 𝔭 (j + 2)) : InQ 𝔭 (j + 2) a ↔ ∃ b, mulW (K := K) 𝔭 (map_mem h1) j b = a := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have h3 := idealPowerSpanBounds.map_pow_le_span_sup (K := K) h𝔭 (c := 1) h2 (j + 2) (by rwa [pow_one])
    obtain ⟨u, hu, e, he, hue⟩ := Submodule.mem_sup.1 h3
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hu
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    rw [mulW_mk, Ideal.Quotient.eq, ← hue]
    have : ι ϖ * r - (r * ι ϖ + e) = -e := by ring
    rw [this]
    exact neg_mem he
  · rintro ⟨b, rfl⟩
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨_, Ideal.mul_mem_right _ _ (map_mem h1), (mulW_mk 𝔭 _ j z).symm⟩
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
