-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.NO.exists_mul_eq_unif_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:45:53.599837+00:00
-- url     : https://prove2.me/submissions/0633d523-e40b-4522-9fdd-db067ff3021e

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_pK
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
open Formalism.HermitianLattices.Ext.L3.D2.NO
namespace Formalism.HermitianLattices.Ext.L3.D2.NO
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π : 𝓞 F} (hπ : π ∈ 𝔭) {z : K}
    (hz : z ∈ pK K 𝔭 0) (hz0 : z ≠ 0) :
    ∃ (m : ℕ) (w : K), w ∈ pK K 𝔭 0 ∧ z * w = algebraMap F K (π : F) ^ m := by
  obtain ⟨t, ht, z₀, -, e⟩ := (mem_pK h𝔭).1 hz
  have ht0 : (t : F) ≠ 0 := by
    intro h
    apply ht
    rw [show t = 0 from RingOfIntegers.ext h]
    exact 𝔭.zero_mem
  have hz₀ : z₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at e
    rcases mul_eq_zero.1 e.symm with h | h
    · exact ht0 ((map_eq_zero _).1 h)
    · exact hz0 h
  set n : ℕ := Ideal.absNorm (Ideal.span {z₀}) with hn
  have hn0 : n ≠ 0 := by
    rw [hn, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hz₀
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {z₀}))
  have hc' : Ideal.span {(n : 𝓞 F)} ≠ (0 : Ideal (𝓞 F)) := by
    simpa using hn0
  have hun : ¬ IsUnit 𝔭 := by
    rw [Ideal.isUnit_iff]
    exact h𝔭.ne_top
  obtain ⟨𝔟, hb, hnd⟩ := (FiniteMultiplicity.of_not_isUnit hun hc').exists_eq_pow_mul_and_not_dvd
  rw [Ideal.dvd_iff_le] at hnd
  obtain ⟨s, hsb, hsp⟩ := SetLike.not_le_iff_exists.mp hnd
  set m := multiplicity 𝔭 (Ideal.span {(n : 𝓞 F)}) with hm
  have h1 : π ^ m * s ∈ Ideal.span {(n : 𝓞 F)} := by
    rw [hb]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hπ m) hsb
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h1
  have hs0 : (s : F) ≠ 0 := by
    intro h
    apply hsp
    rw [show s = 0 from RingOfIntegers.ext h]
    exact 𝔭.zero_mem
  have hs0' : algebraMap F K (s : F) ≠ 0 := (map_ne_zero _).2 hs0
  have hu' : algebraMap (𝓞 K) K u * algebraMap (𝓞 K) K z₀ = (n : K) := by
    rw [← map_mul, hu, map_natCast]
  have hr' : algebraMap F K (r : F) * (n : K) =
      algebraMap F K (π : F) ^ m * algebraMap F K (s : F) := by
    have := congrArg (fun x : 𝓞 F => algebraMap F K (x : F)) hr
    simpa using this
  refine ⟨m, (algebraMap F K (s : F))⁻¹ * (algebraMap F K (r : F) * algebraMap (𝓞 K) K u *
    algebraMap F K (t : F)), ?_, ?_⟩
  · refine (mem_pK h𝔭).2 ⟨s, hsp, algebraMap (𝓞 F) (𝓞 K) r * u * algebraMap (𝓞 F) (𝓞 K) t, by simp, ?_⟩
    rw [mul_inv_cancel_left₀ hs0', map_mul, map_mul]
    rfl
  · have : z * (algebraMap F K (r : F) * algebraMap (𝓞 K) K u * algebraMap F K (t : F)) =
        algebraMap F K (π : F) ^ m * algebraMap F K (s : F) := by
      rw [← hr', ← hu', e]
      ring
    rw [mul_left_comm, this, mul_left_comm, inv_mul_cancel₀ hs0', mul_one]
end Formalism.HermitianLattices.Ext.L3.D2.NO
