-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocF.fixed_nonunit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:29.966821+00:00
-- url     : https://prove2.me/submissions/d632427e-8214-4f15-9986-411cf1175ef6

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
private lemma hcompl_unit_property_of_isPrime {p : Ideal (𝓞 K)} (hp : p.IsPrime) {N S : 𝓞 K} (hS : S ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p)
    (hN : N ∉ p) (hfix : star (algebraMap (𝓞 K) K N / algebraMap (𝓞 K) K S) =
      algebraMap (𝓞 K) K N / algebraMap (𝓞 K) K S) :
    IsUnitIn (locRing p) (algebraMap (𝓞 K) K N / algebraMap (𝓞 K) K S) := by
  have inj := IsFractionRing.injective (𝓞 K) K
  obtain ⟨hS1, hS2⟩ := hcompl_mem_prime_ideal_property hp hS
  have ne0 : ∀ {u : 𝓞 K}, u ∉ p → algebraMap (𝓞 K) K u ≠ 0 := fun hu h0 =>
    hu (by rw [(map_eq_zero_iff _ inj).mp h0]; exact p.zero_mem)
  obtain ⟨S', hS'⟩ := exists_int_algebraMap_eq_star S
  obtain ⟨N', hN'⟩ := exists_int_algebraMap_eq_star N
  have hS'p := hS2 S' hS'

  have key : N' * S = N * S' := inj (by
    have h := hfix
    rw [star_div₀, div_eq_div_iff (by rw [← hS']; exact ne0 hS'p) (ne0 hS1)] at h
    rw [map_mul, map_mul, hN', hS', h])
  have hN'p : N' ∉ p := fun h =>
    (hp.mem_or_mem (show N * S' ∈ p from key ▸ p.mul_mem_right S h)).elim hN hS'p
  have hNc : N ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p :=
    Submonoid.subset_closure ⟨hN, fun t ht => by rw [inj (ht.trans hN'.symm)]; exact hN'p⟩
  refine ⟨div_ne_zero (ne0 hN) (ne0 hS1), ?_, ?_⟩
  · show _ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
    exact ⟨S, hS, Submodule.mem_one.mpr ⟨N, by rw [mul_div_cancel₀ _ (ne0 hS1)]⟩⟩
  · show _ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR, inv_div]
    exact ⟨N, hNc, Submodule.mem_one.mpr ⟨S, by rw [mul_div_cancel₀ _ (ne0 hN)]⟩⟩
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
theorem _root_.solution {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K} (ha : a ∈ locRing p)
    (hfix : star a = a) (hnu : ¬ IsUnitIn (locRing p) a) :
    ∃ r ∈ p, ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p,
      a = algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s := by
  have ha' : a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := ha
  rw [Formalism.HermitianLatticesTheory.locDual_mem_locR] at ha'
  obtain ⟨s, hs, hsa⟩ := ha'
  obtain ⟨t, ht⟩ := Submodule.mem_one.mp hsa
  have hs0 : algebraMap (𝓞 K) K s ≠ 0 := fun h0 => (hcompl_mem_prime_ideal_property hp hs).1
    (by rw [(map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mp h0]; exact p.zero_mem)
  have hat : a = algebraMap (𝓞 K) K t / algebraMap (𝓞 K) K s := by
    rw [ht, mul_div_cancel_left₀ a hs0]
  refine ⟨t, ?_, s, hs, hat⟩
  by_contra htp
  rw [hat] at hnu hfix
  exact hnu (hcompl_unit_property_of_isPrime hp hs htp hfix)
end Formalism.HermitianLattices.Ext.L3.LocF
