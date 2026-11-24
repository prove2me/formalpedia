-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.J.exists_skew_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:57:03.970022+00:00
-- url     : https://prove2.me/submissions/faed579a-e91d-480c-acc2-cf395e9cfec3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulSpanIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulMemPrimePower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqMapMulKer
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_algebraMap_mem_pK
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_pK
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_coe
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_eq_iff_mem_range
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.D2.J
namespace Formalism.HermitianLattices.Ext.L3.D2.J
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) :
    ∃ δ : K, star δ = -δ ∧ δ ≠ 0 ∧ δ ∈ pK K 𝔭 0 ∧ δ⁻¹ ∈ pK K 𝔭 0 := by
  obtain ⟨θ, hθ⟩ := idealPowerSpanBounds.exists_theta hK hF h𝔭
  set d : 𝓞 K := θ - conjO K θ with hd
  have hcd : conjO K d = -d := by
    rw [hd, map_sub, conjO_conjO, neg_sub]
  obtain ⟨n, hn⟩ := (conjO_eq_iff_mem_range hF (d * conjO K d)).1 (by
    rw [map_mul, conjO_conjO, mul_comm])
  have hone : (1 : 𝓞 K) ∉ extP K 𝔭 := by
    intro h1
    have h3 := (idealPowerSpanBounds.mem_pow_iff (K := K) 𝔭 1 1).1 (by rwa [map_one, pow_one])
    rw [pow_one] at h3
    exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h3)
  have hn𝔭 : n ∉ 𝔭 := by
    intro hmem
    have h1 : d * conjO K d ∈ extP K 𝔭 ^ 1 := by
      rw [← hn, pow_one]
      exact Ideal.mem_map_of_mem _ hmem
    have h2 := idealPowerSpanBounds.mem_of_unit_mul_mem hθ h1
    have h3 : d * 1 ∈ extP K 𝔭 ^ 1 := by
      rw [hcd] at h2
      simpa using h2
    have h4 := idealPowerSpanBounds.mem_of_unit_mul_mem hθ h3
    rw [pow_one] at h4
    exact hone h4
  have hd0 : d ≠ 0 := by
    intro h0
    apply hn𝔭
    have : algebraMap (𝓞 F) (𝓞 K) n = algebraMap (𝓞 F) (𝓞 K) 0 := by rw [hn, h0]; simp
    rw [idealPowerSpanBounds.ι_inj this]
    exact 𝔭.zero_mem
  have hdK : ((d : 𝓞 K) : K) ≠ 0 := by
    intro h0
    exact hd0 (RingOfIntegers.ext (h0.trans (map_zero (algebraMap (𝓞 K) K)).symm))
  refine ⟨(d : K), ?_, hdK, algebraMap_mem_pK 𝔭 d, ?_⟩
  · rw [← conjO_coe, hcd]
    exact map_neg (algebraMap (𝓞 K) K) _
  · refine (mem_pK h𝔭).2 ⟨n, hn𝔭, conjO K d, by simp, ?_⟩
    have e : algebraMap F K (n : F) = (d : K) * ((conjO K d : 𝓞 K) : K) := by
      have := congrArg (algebraMap (𝓞 K) K) hn
      rw [map_mul] at this
      rw [← this]
      rfl
    rw [e]
    field_simp
end Formalism.HermitianLattices.Ext.L3.D2.J
