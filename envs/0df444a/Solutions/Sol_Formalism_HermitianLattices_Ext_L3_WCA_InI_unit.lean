-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WCA.InI.unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:31:51.575563+00:00
-- url     : https://prove2.me/submissions/a3f9aea8-9dbb-48d6-afac-3e87e0574319

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AkCountEqRedCountMul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinitePrimesOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_WCA____ne_zero_cf941fa073ca
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_ne_zero_of_notMem
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_ne_zero_of_notMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_eq_iff_mem_range
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_conjO_mem_pow
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WCA
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}
namespace Formalism.HermitianLattices.Ext.L3.WCA
namespace InI
theorem _root_.solution (h𝔭 : 𝔭.IsMaximal) (hF : IsFixF K F) {ε : K} (hε : InI 𝔭 1 ε) :
    1 + ε ≠ 0 ∧ InI 𝔭 0 ((1 + ε)⁻¹) := by
  obtain ⟨t, ht, z, hz, e⟩ := hε
  set a : 𝓞 K := ι t + z with ha
  have hκa : κ a = κ (ι t) * (1 + ε) := by rw [ha, map_add, e]; ring
  obtain ⟨b, hb⟩ := (conjO_eq_iff_mem_range hF (a * conjO K a)).1 (by
    rw [map_mul, conjO_conjO, mul_comm])
  have hz' : conjO K z ∈ extP K 𝔭 ^ 1 := conjO_mem_pow hF 𝔭 1 z hz
  have hbp : b ∉ 𝔭 := by
    intro hbp
    have h1 : ι b ∈ extP K 𝔭 ^ 1 := ι_mem_pow (by simpa using hbp)
    have h2 : ι (t * t) ∈ extP K 𝔭 ^ 1 := by
      have : ι (t * t) = ι b - (ι t * conjO K z + z * ι t + z * conjO K z) := by
        rw [hb, ha, map_add, conjO_map hF, map_mul]; ring
      rw [this]
      exact sub_mem h1 (add_mem (add_mem (Ideal.mul_mem_left _ _ hz') (Ideal.mul_mem_right _ _ hz))
        (Ideal.mul_mem_right _ _ hz))
    have h3 : t * t ∈ 𝔭 := by simpa using (mem_pow_iff (K := K) 𝔭 1 (t * t)).1 h2
    exact (h𝔭.isPrime.mem_or_mem h3).elim ht ht
  have hκb : κ (ι b) = κ a * κ (conjO K a) := by rw [hb, map_mul]
  have hne : 1 + ε ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hκa
    rw [hκa, zero_mul] at hκb
    exact κι_ne_zero (K := K) (ne_zero_of_notMem hbp) hκb
  refine ⟨hne, b, hbp, ι t * conjO K a, by simp, ?_⟩
  rw [hκb, hκa, map_mul]
  field_simp
end InI
end Formalism.HermitianLattices.Ext.L3.WCA
