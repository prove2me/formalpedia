-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.exists_add_conj_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:51:36.843726+00:00
-- url     : https://prove2.me/submissions/7516809f-e9dd-4d47-b1e5-9cd61170452f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SigmaCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DetMulLeftCompMulRight
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsAddConjTransposeEq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_exists_theta
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_of_unit_mul_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_pow_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_trF_spec


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (a : 𝓞 F) :
    ∃ z : 𝓞 K, z + conjO K z = algebraMap (𝓞 F) (𝓞 K) a := by
  have htop : LinearMap.range (idealPowerSpanBounds.trF hF) = ⊤ := by
    by_contra hne
    obtain ⟨𝔭, h𝔭, hle⟩ := Ideal.exists_le_maximal (LinearMap.range (idealPowerSpanBounds.trF hF)) hne
    obtain ⟨θ, hθ⟩ := idealPowerSpanBounds.exists_theta hK hF h𝔭
    have hmem : ∀ z : 𝓞 K, z + conjO K z ∈ extP K 𝔭 := fun z => by
      rw [← idealPowerSpanBounds.trF_spec hF]
      exact Ideal.mem_map_of_mem _ (hle ⟨z, rfl⟩)
    have h2 : (2 : 𝓞 K) ∈ extP K 𝔭 := by
      have := hmem 1
      rwa [map_one, one_add_one_eq_two] at this
    have hsq : (θ - conjO K θ) * (θ - conjO K θ) ∈ extP K 𝔭 := by
      have : (θ - conjO K θ) * (θ - conjO K θ) =
          (θ + conjO K θ) * (θ + conjO K θ) - 2 * (2 * (θ * conjO K θ)) := by ring
      rw [this]
      exact sub_mem (Ideal.mul_mem_left _ _ (hmem θ)) (Ideal.mul_mem_right _ _ h2)
    have h1 : (θ - conjO K θ) ∈ extP K 𝔭 ^ 1 := idealPowerSpanBounds.mem_of_unit_mul_mem hθ (by rwa [pow_one])
    have h0 : (1 : 𝓞 K) ∈ extP K 𝔭 ^ 1 := idealPowerSpanBounds.mem_of_unit_mul_mem hθ (by rwa [mul_one])
    have h3 := (idealPowerSpanBounds.mem_pow_iff (K := K) 𝔭 1 1).1 (by rwa [map_one])
    rw [pow_one] at h3
    exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h3)
  obtain ⟨z, hz⟩ : a ∈ LinearMap.range (idealPowerSpanBounds.trF hF) := htop ▸ Submodule.mem_top
  exact ⟨z, by rw [← idealPowerSpanBounds.trF_spec hF, hz]⟩
end Formalism.HermitianLattices.Ext.L3
