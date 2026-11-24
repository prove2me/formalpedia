-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences.exists_tr_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:46.708427+00:00
-- url     : https://prove2.me/submissions/9fb45399-045a-43da-ab33-49b66498a5c5

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySeventh
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_conjO_mem_pow
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
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences
open idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {N : ℕ} {z : 𝓞 K} (hz : z ∉ extP K 𝔭 ^ N) :
    ∃ b : 𝓞 K, trF hF (b * z) ∉ 𝔭 ^ N := by
  by_contra hall
  push_neg at hall
  obtain ⟨θ, hθ⟩ := exists_theta hK hF h𝔭
  have htr : ∀ b : 𝓞 K, b * z + conjO K (b * z) ∈ extP K 𝔭 ^ N := by
    intro b
    rw [← trF_spec hF]
    exact (mem_pow_iff 𝔭 N _).mpr (hall b)
  have h1 := htr 1
  have h2 := htr θ
  rw [one_mul] at h1
  rw [map_mul] at h2
  have h3 : (θ - conjO K θ) * conjO K z ∈ extP K 𝔭 ^ N := by
    have e : (θ - conjO K θ) * conjO K z =
        θ * (z + conjO K z) - (θ * z + conjO K θ * conjO K z) := by ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ h1) h2
  have h4 : conjO K z ∈ extP K 𝔭 ^ N := mem_of_unit_mul_mem hθ h3
  apply hz
  have h5 := conjO_mem_pow hF 𝔭 N _ h4
  rwa [L3.conjO_conjO z] at h5
end Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences
