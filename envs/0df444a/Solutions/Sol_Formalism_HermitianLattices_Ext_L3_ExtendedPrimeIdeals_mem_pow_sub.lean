-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals.mem_pow_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:12:27.882976+00:00
-- url     : https://prove2.me/submissions/94cc2100-29c7-40b3-92d4-0c83bc09270d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountExtP
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsBasisLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DiscrIdealLeIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_ExtendedPrimeIdeals_ne_bot_of_isMaximal

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {s n : 𝓞 F} {k v : ℕ}
    (hn : n ∈ 𝔭 ^ v) (hn' : n ∉ 𝔭 ^ (v + 1)) (h : s * n ∈ 𝔭 ^ k) : s ∈ 𝔭 ^ (k - v) := by
  have hne := ne_bot_of_isMaximal h𝔭
  have hpr : Prime 𝔭 := Ideal.prime_of_isPrime hne h𝔭.isPrime
  by_cases hkv : k ≤ v
  · rw [Nat.sub_eq_zero_of_le hkv, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  obtain ⟨J, hJ⟩ : 𝔭 ^ v ∣ Ideal.span {n} := by
    rw [Ideal.dvd_span_singleton]
    exact hn
  have hJ' : ¬ 𝔭 ∣ J := by
    rintro ⟨C, rfl⟩
    apply hn'
    rw [← Ideal.dvd_span_singleton, hJ, pow_succ, ← mul_assoc]
    exact Dvd.intro _ rfl
  have h2 : 𝔭 ^ k ∣ Ideal.span {s} * Ideal.span {n} := by
    rw [Ideal.span_singleton_mul_span_singleton, Ideal.dvd_span_singleton]
    exact h
  have ek : k = v + (k - v) := by omega
  rw [hJ, ek, pow_add, mul_left_comm] at h2
  have h3 := (mul_dvd_mul_iff_left (pow_ne_zero v hne)).1 h2
  rw [← Ideal.dvd_span_singleton]
  exact hpr.pow_dvd_of_dvd_mul_right _ hJ' h3
end Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals
