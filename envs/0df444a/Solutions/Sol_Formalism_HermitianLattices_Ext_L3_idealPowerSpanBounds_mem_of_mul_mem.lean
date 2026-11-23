-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.mem_of_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:57:19.492649+00:00
-- url     : https://prove2.me/submissions/395e51cb-fc73-4584-9010-130cc1ce2d40

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_ne_bot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_map_ne_bot_of_isMaximal
import Theorems.Thm_Formalism_H_dualEquiv_apply
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {d : 𝓞 F} {v j : ℕ}
    (hd : d ∉ 𝔭 ^ (v + 1)) {z : 𝓞 K} (hz : ι d * z ∈ extP K 𝔭 ^ (v + j)) : z ∈ extP K 𝔭 ^ j := by
  have hpr : Prime 𝔭 := Ideal.prime_of_isPrime (ne_bot h𝔭) h𝔭.isPrime
  have hdvd : Ideal.span {d} ⊔ 𝔭 ^ (v + j) ∣ 𝔭 ^ (v + j) := Ideal.dvd_iff_le.mpr le_sup_right
  obtain ⟨m, -, hm⟩ := (dvd_prime_pow hpr (v + j)).mp hdvd
  rw [associated_iff_eq] at hm
  have hdm : d ∈ 𝔭 ^ m := by
    rw [← hm]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self d)
  have hmv : m ≤ v := by
    by_contra h
    exact hd (Ideal.pow_le_pow_right (by omega) hdm)
  have hS : Ideal.span {ι d} ⊔ extP K 𝔭 ^ (v + j) = extP K 𝔭 ^ m := by
    have h1 := congrArg (Ideal.map ι) hm
    simp only [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_pow] at h1
    exact h1
  have hle : extP K 𝔭 ^ m * Ideal.span {z} ≤ extP K 𝔭 ^ (v + j) := by
    rw [← hS, Ideal.sup_mul]
    refine sup_le ?_ (by first | exact Ideal.mul_le_left | exact Ideal.mul_le_right)
    rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_le_iff_mem]
    exact hz
  have hdiv : extP K 𝔭 ^ m * extP K 𝔭 ^ (v + j - m) ∣ extP K 𝔭 ^ m * Ideal.span {z} := by
    rw [← pow_add, show m + (v + j - m) = v + j by omega]
    exact Ideal.dvd_iff_le.mpr hle
  have h0 : extP K 𝔭 ^ m ≠ 0 :=
    pow_ne_zero _ (by rw [Ne, Ideal.zero_eq_bot]; exact map_ne_bot_of_isMaximal h𝔭)
  have h2 := (mul_dvd_mul_iff_left h0).mp hdiv
  exact Ideal.dvd_span_singleton.mp (dvd_trans (pow_dvd_pow _ (by omega)) h2)
end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
