-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.NormOneGroup.mem_of_cond
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:56.349396+00:00
-- url     : https://prove2.me/submissions/3b52506b-bfa3-4597-8c4e-d6600f09092b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SmulGenMemIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormOneMkIff
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.NormOneGroup
open Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals Formalism.HermitianLattices.Ext.L3.EndomorphismScalars
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {e : V} {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.NormOneGroup
theorem _root_.solution (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F}
    (hn : h e e = algebraMap F K (n : F)) {v k : ℕ} (hv : n ∈ 𝔭 ^ v) (hv' : n ∉ 𝔭 ^ (v + 1))
    {b : 𝓞 K} (H : CongrP 𝔭 k (h (b • e) (b • e)) (h e e)) :
    conjO K b * b - 1 ∈ extP K 𝔭 ^ (k - v) := by
  obtain ⟨t, ht, z, hz, hzeq⟩ := H
  have e1 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := rfl
  have e2 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) n) = algebraMap F K (n : F) := rfl
  have e3 : algebraMap (𝓞 K) K (conjO K b) = star (algebraMap (𝓞 K) K b) := rfl
  have hbe : h (b • e) (b • e) = star (algebraMap (𝓞 K) K b) * algebraMap (𝓞 K) K b * h e e := by
    rw [← algebraMap_smul K b e, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul,
      starRingEnd_apply, mul_assoc]
  have hz' : z = algebraMap (𝓞 F) (𝓞 K) t * algebraMap (𝓞 F) (𝓞 K) n * (conjO K b * b - 1) := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [hzeq, hbe, hn, map_mul, map_mul, map_sub, map_mul, map_one, e1, e2, e3]
    ring
  rcases le_or_gt k v with hkv | hvk
  · rw [Nat.sub_eq_zero_of_le hkv, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  have hne : 𝔭 ≠ ⊥ := ne_bot_of_isMaximal h𝔭
  have hcop : ∀ I : Ideal (𝓞 F), ¬ I ≤ 𝔭 → 𝔭 ⊔ I = ⊤ := fun I hI => by
    by_contra hne'
    exact hI (le_sup_right.trans (h𝔭.eq_of_le hne' le_sup_left).ge)
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hv)
  have hJp : ¬ J ≤ 𝔭 := by
    intro hle
    apply hv'
    rw [← Ideal.span_singleton_le_iff_mem, hJ, pow_succ]
    exact Ideal.mul_mono_right hle
  have htp : ¬ Ideal.span {t} ≤ 𝔭 := fun hle => ht ((Ideal.span_singleton_le_iff_mem _).mp hle)
  have hcopF : IsCoprime 𝔭 (Ideal.span {t} * J) :=
    (Ideal.isCoprime_iff_sup_eq.mpr (hcop _ htp)).mul_right (Ideal.isCoprime_iff_sup_eq.mpr (hcop _ hJp))
  have hX : IsCoprime (extP K 𝔭) ((Ideal.span {t} * J).map (algebraMap (𝓞 F) (𝓞 K))) := by
    rw [Ideal.isCoprime_iff_sup_eq] at hcopF ⊢
    rw [extP, ← Ideal.map_sup, hcopF, Ideal.map_top]
  have hspan : Ideal.span {z} = extP K 𝔭 ^ v * Ideal.span {conjO K b * b - 1} *
      (Ideal.span {t} * J).map (algebraMap (𝓞 F) (𝓞 K)) := by
    have hn' : Ideal.span {algebraMap (𝓞 F) (𝓞 K) n} =
        Ideal.map (algebraMap (𝓞 F) (𝓞 K)) (𝔭 ^ v) * Ideal.map (algebraMap (𝓞 F) (𝓞 K)) J := by
      rw [← Ideal.map_mul, ← hJ, Ideal.map_span, Set.image_singleton]
    rw [hz', ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
      Ideal.map_mul, extP, ← Ideal.map_pow, hn', Ideal.map_span, Set.image_singleton]
    ring
  have hdvd : extP K 𝔭 ^ k ∣ extP K 𝔭 ^ v * Ideal.span {conjO K b * b - 1} *
      (Ideal.span {t} * J).map (algebraMap (𝓞 F) (𝓞 K)) := by
    rw [← hspan]
    exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hz)
  have hdvd2 := (hX.pow_left (m := k)).dvd_of_dvd_mul_right hdvd
  have hP0 : extP K 𝔭 ^ v ≠ 0 := by
    apply pow_ne_zero
    rw [extP, Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]
    exact hne
  rw [show k = v + (k - v) by omega, pow_add] at hdvd2
  have h3 := (mul_dvd_mul_iff_left hP0).mp hdvd2
  exact (Ideal.span_singleton_le_iff_mem _).mp (Ideal.dvd_iff_le.mp h3)
end Formalism.HermitianLattices.Ext.L3.NormOneGroup
