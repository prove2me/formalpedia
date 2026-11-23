-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocF.isUnitIn_algebraMap_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:09:45.265978+00:00
-- url     : https://prove2.me/submissions/6ae89fcd-eaba-4b26-8eea-25166c36f5e7

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthUnitFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_GmapLocEqOfFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LinearIndependentOfGramDetNeZero
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_mem_locR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Module Matrix
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.LocF
open Formalism.HermitianLattices.Ext.L3.WA
section Units
variable {K : Type*} [Field K] {S : Subring K}
end Units
section Ring
variable {K : Type} [Field K] [NumberField K] [StarRing K]
private lemma exists_int_algebraMap_eq_star (x : 𝓞 K) : ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = star (algebraMap (𝓞 K) K x) := by
  have hx : IsIntegral ℤ (algebraMap (𝓞 K) K x) := x.isIntegral_coe
  have : IsIntegral ℤ (star (algebraMap (𝓞 K) K x)) := hx.map (starRingEnd K).toIntAlgHom
  exact IsIntegralClosure.isIntegral_iff.mp this
private lemma hcompl_mem_prime_ideal_property {p : Ideal (𝓞 K)} (hp : p.IsPrime) {s : 𝓞 K} (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) :
    s ∉ p ∧ ∀ t : 𝓞 K, algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K s) → t ∉ p := by
  induction hs using Submonoid.closure_induction with
  | mem x hx => exact hx
  | one =>
    refine ⟨fun h => hp.ne_top ((Ideal.eq_top_iff_one p).mpr h), fun t ht h => hp.ne_top ((Ideal.eq_top_iff_one p).mpr ?_)⟩
    have : t = 1 := IsFractionRing.injective (𝓞 K) K (by rw [ht, map_one, star_one])
    rwa [this] at h
  | mul x y _ _ hx hy =>
    refine ⟨fun h => (hp.mem_or_mem h).elim hx.1 hy.1, fun t ht h => ?_⟩
    obtain ⟨x', hx'⟩ := exists_int_algebraMap_eq_star x
    obtain ⟨y', hy'⟩ := exists_int_algebraMap_eq_star y
    have : t = x' * y' := IsFractionRing.injective (𝓞 K) K (by
      rw [ht, map_mul, map_mul, hx', hy', star_mul, mul_comm])
    rw [this] at h
    exact (hp.mem_or_mem h).elim (hx.2 x' hx') (hy.2 y' hy')
end Ring
section Gram
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ}
end Gram
section Cramer
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ}
end Cramer
end Formalism.HermitianLattices.Ext.L3.LocF
end
end

set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocF
open Formalism.HermitianLattices.Ext.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLattices.Ext.L3.LocF
theorem _root_.solution {p : Ideal (𝓞 K)} (hp : p.IsPrime) (r : 𝓞 K) :
    IsUnitIn (locRing p) (algebraMap (𝓞 K) K r) ↔ r ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
  have inj := IsFractionRing.injective (𝓞 K) K
  constructor
  · rintro ⟨h0, -, hinv⟩
    have hinv' : (algebraMap (𝓞 K) K r)⁻¹ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := hinv
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR] at hinv'
    obtain ⟨s, hs, hsr⟩ := hinv'
    obtain ⟨t, ht⟩ := Submodule.mem_one.mp hsr
    have hst : s = t * r := inj (by rw [map_mul, ht, mul_assoc, inv_mul_cancel₀ h0, mul_one])
    obtain ⟨hs1, hs2⟩ := hcompl_mem_prime_ideal_property hp hs
    refine Submonoid.subset_closure ⟨fun h => hs1 (hst ▸ p.mul_mem_left t h), fun u hu hup => ?_⟩
    obtain ⟨t', ht'⟩ := exists_int_algebraMap_eq_star t
    apply hs2 (t' * u) _ (p.mul_mem_left t' hup)
    rw [map_mul, ht', hu, hst, map_mul, star_mul, mul_comm]
  · intro hr
    obtain ⟨hr1, -⟩ := hcompl_mem_prime_ideal_property hp hr
    have h0 : algebraMap (𝓞 K) K r ≠ 0 := fun h0 =>
      hr1 (by rw [(map_eq_zero_iff _ inj).mp h0]; exact p.zero_mem)
    refine ⟨h0, ?_, ?_⟩
    · show _ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p
      rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
      exact ⟨1, Submonoid.one_mem _, Submodule.mem_one.mpr ⟨r, by rw [map_one, one_mul]⟩⟩
    · show _ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p
      rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
      exact ⟨r, hr, Submodule.mem_one.mpr ⟨1, by rw [map_one, mul_inv_cancel₀ h0]⟩⟩
end Formalism.HermitianLattices.Ext.L3.LocF
