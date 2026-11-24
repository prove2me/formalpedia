-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.exists_mul_dvd_unif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:47:59.883719+00:00
-- url     : https://prove2.me/submissions/d0984f01-9ab2-4bf6-8ff0-92a7396b9a8a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π : 𝓞 F} (hπ : π ∈ 𝔭)
    (hπ' : π ∉ 𝔭 ^ 2) (k : ℕ) : ∃ s : 𝓞 F, s ∉ 𝔭 ∧ ∀ x ∈ 𝔭 ^ k, π ^ k ∣ s * x := by
  obtain ⟨𝔟, hb⟩ : 𝔭 ∣ Ideal.span {π} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hπ
  have hnb : ¬ 𝔟 ≤ 𝔭 := by
    intro hle
    apply hπ'
    have : Ideal.span {π} ≤ 𝔭 ^ 2 := by
      rw [hb, sq]; exact Ideal.mul_mono_right hle
    exact this (Ideal.mem_span_singleton_self π)
  obtain ⟨s, hs, hs'⟩ := SetLike.not_le_iff_exists.mp hnb
  refine ⟨s ^ k, fun h => hs' (h𝔭.isPrime.mem_of_pow_mem k h), fun x hx => ?_⟩
  rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow, hb, mul_pow, mul_comm (s ^ k)]
  exact Ideal.mul_mem_mul hx (Ideal.pow_mem_pow hs k)
end Formalism.HermitianLattices.Ext.L3.D2
