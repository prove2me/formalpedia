-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences.exists_trace_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:08.822812+00:00
-- url     : https://prove2.me/submissions/9b07f974-95d2-421e-90e6-4d07817da88f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySeventh
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_conjO_mem_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_exists_inv_theta
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_exists_theta
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_of_unit_mul_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_star_def
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences
open idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (N : ℕ) : ∃ a : 𝓞 K, a + star a - 1 ∈ extP K 𝔭 ^ N := by
  obtain ⟨θ, hθ⟩ := exists_theta hK hF h𝔭
  obtain ⟨e, he⟩ := exists_inv_theta hθ N
  refine ⟨θ * e, ?_⟩
  have hJ := conjO_mem_pow hF 𝔭 N
  have h1 : (conjO K θ - θ) * conjO K e - 1 ∈ extP K 𝔭 ^ N := by
    have h := hJ _ he
    simp only [map_sub, map_mul, map_one] at h
    rw [L3.conjO_conjO θ] at h
    exact h
  have h2 : (θ - conjO K θ) * (e + conjO K e) ∈ extP K 𝔭 ^ N := by
    have e2 : (θ - conjO K θ) * (e + conjO K e) =
        ((θ - conjO K θ) * e - 1) - ((conjO K θ - θ) * conjO K e - 1) := by ring
    rw [e2]
    exact Ideal.sub_mem _ he h1
  have h3 : e + conjO K e ∈ extP K 𝔭 ^ N := mem_of_unit_mul_mem hθ h2
  have e3 : θ * e + star (θ * e) - 1 =
      ((θ - conjO K θ) * e - 1) + conjO K θ * (e + conjO K e) := by
    rw [idealPowerSpanBounds.star_def, map_mul]
    ring
  rw [e3]
  exact Ideal.add_mem _ he (Ideal.mul_mem_left _ _ h3)
end Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences
