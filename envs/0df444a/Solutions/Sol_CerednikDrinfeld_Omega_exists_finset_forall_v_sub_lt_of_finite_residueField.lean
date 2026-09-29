-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_finset_forall_v_sub_lt_of_finite_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/e6fe966c-4735-5e8c-abcc-3549ef5e5b31

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_finset_forall_v_sub_lt_of_finite_residueField

set_option autoImplicit false
set_option linter.unusedVariables false

p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_exists_finset_forall_v_sub_lt_of_finite_residueField.CerednikDrinfeld CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_finset_forall_v_sub_lt_of_finite_residueField.CerednikDrinfeld.Omega"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.PseudoUniformizer"
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "PseudoUniformizer"
namespace HFin
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

theorem exists_finset_repr (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    [Finite (IsLocalRing.ResidueField R₀)] (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) :
    ∀ m : ℕ, ∃ S : Finset R₀, ∀ r : R₀, ∃ s ∈ S, ϖ₀ ^ m ∣ r - s := by
  classical

  have hmax : IsLocalRing.maximalIdeal R₀ = Ideal.span {ϖ₀} := hϖ₀.maximalIdeal_eq
  haveI : Fintype (IsLocalRing.ResidueField R₀) := Fintype.ofFinite _
  have hsurj : Function.Surjective (IsLocalRing.residue R₀) := Ideal.Quotient.mk_surjective
  obtain ⟨S₁, hS₁⟩ : ∃ S₁ : Finset R₀, ∀ r : R₀, ∃ s ∈ S₁, ϖ₀ ∣ r - s := by
    refine ⟨(Finset.univ : Finset (IsLocalRing.ResidueField R₀)).image (Function.surjInv hsurj), fun r => ?_⟩
    refine ⟨Function.surjInv hsurj (IsLocalRing.residue R₀ r), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have h1 : IsLocalRing.residue R₀ (r - Function.surjInv hsurj (IsLocalRing.residue R₀ r)) = 0 := by
      rw [map_sub, Function.surjInv_eq hsurj, sub_self]
    rw [IsLocalRing.residue_eq_zero_iff, hmax, Ideal.mem_span_singleton] at h1
    exact h1
  intro m
  induction m with
  | zero => exact ⟨{0}, fun r => ⟨0, Finset.mem_singleton_self _, by simp⟩⟩
  | succ m ih =>
    obtain ⟨S, hS⟩ := ih
    refine ⟨(S ×ˢ S₁).image (fun p => p.1 + ϖ₀ ^ m * p.2), fun r => ?_⟩
    obtain ⟨s, hs, ⟨q, hq⟩⟩ := hS r
    obtain ⟨s', hs', ⟨q', hq'⟩⟩ := hS₁ q
    refine ⟨s + ϖ₀ ^ m * s', Finset.mem_image.2 ⟨(s, s'), Finset.mem_product.2 ⟨hs, hs'⟩, rfl⟩, ⟨q', ?_⟩⟩
    calc r - (s + ϖ₀ ^ m * s') = (r - s) - ϖ₀ ^ m * s' := by ring
      _ = ϖ₀ ^ m * q - ϖ₀ ^ m * s' := by rw [hq]
      _ = ϖ₀ ^ m * (q - s') := by ring
      _ = ϖ₀ ^ m * (ϖ₀ * q') := by rw [hq']
      _ = ϖ₀ ^ (m + 1) * q' := by ring

end CerednikDrinfeld.Omega.HFin

theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ K x) ≤ 1)
    (ϖ : Omega.PseudoUniformizer K₀ K) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ) :
    ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n := by
  classical
  intro n

  have hp0 : 0 < Valued.v (algebraMap K₀ K ϖ.ϖ) := ϖ.pos
  have hp1 : Valued.v (algebraMap K₀ K ϖ.ϖ) < 1 := ϖ.lt_one
  have hϖK0 : ϖ.ϖ ≠ 0 := by
    intro h
    have : Valued.v (algebraMap K₀ K ϖ.ϖ) = 0 := by rw [h, map_zero, map_zero]
    rw [this] at hp0
    exact lt_irrefl _ hp0
  have hvint : ∀ q : R₀, Valued.v (algebraMap K₀ K (algebraMap R₀ K₀ q)) ≤ 1 := fun q =>
    (hR₀ _).1 ⟨q, rfl⟩

  obtain ⟨S, hS⟩ := CerednikDrinfeld.Omega.HFin.exists_finset_repr R₀ ϖ₀ hϖ₀ (2 * n + 1)
  refine ⟨S.image (fun s => algebraMap R₀ K₀ s * (ϖ.ϖ ^ n)⁻¹), fun a ha => ?_⟩

  have hint : Valued.v (algebraMap K₀ K (ϖ.ϖ ^ n * a)) ≤ 1 := by
    rw [map_mul, map_mul, map_pow, map_pow]
    calc Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n * Valued.v (algebraMap K₀ K a)
        ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n * (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n := mul_le_mul_right ha _
      _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ hp0.ne', one_pow]
  obtain ⟨r, hr⟩ := (hR₀ _).2 hint
  obtain ⟨s, hs, ⟨q, hq⟩⟩ := hS r
  refine ⟨algebraMap R₀ K₀ s * (ϖ.ϖ ^ n)⁻¹, Finset.mem_image_of_mem _ hs, ?_⟩

  have hπn : (ϖ.ϖ ^ n : K₀) ≠ 0 := pow_ne_zero _ hϖK0
  have key : a - algebraMap R₀ K₀ s * (ϖ.ϖ ^ n)⁻¹ = ϖ.ϖ ^ (n + 1) * algebraMap R₀ K₀ q := by
    have ha' : a = algebraMap R₀ K₀ r * (ϖ.ϖ ^ n)⁻¹ := by
      rw [hr, mul_comm, ← mul_assoc, inv_mul_cancel₀ hπn, one_mul]
    rw [ha', ← sub_mul, ← map_sub, hq, map_mul, map_pow, hϖ]
    field_simp
    ring
  rw [← map_sub, key, map_mul, map_mul, map_pow, map_pow]
  calc Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1) * Valued.v (algebraMap K₀ K (algebraMap R₀ K₀ q))
      ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1) * 1 := mul_le_mul_right (hvint q) _
    _ = Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1) := mul_one _
    _ < Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n := pow_lt_pow_right_of_lt_one₀ hp0 hp1 (Nat.lt_succ_self n)

end S_CerednikDrinfeld_Omega_exists_finset_forall_v_sub_lt_of_finite_residueField
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_finset_forall_v_sub_lt_of_finite_residueField (solution)
