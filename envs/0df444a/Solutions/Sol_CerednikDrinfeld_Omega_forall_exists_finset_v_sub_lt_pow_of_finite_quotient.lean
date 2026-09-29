-- Prove2me | solution 1 for CerednikDrinfeld.Omega.forall_exists_finset_v_sub_lt_pow_of_finite_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/fc535474-1f91-5263-b844-748410016be6

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_forall_exists_finset_v_sub_lt_pow_of_finite_quotient

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_forall_exists_finset_v_sub_lt_pow_of_finite_quotient.CerednikDrinfeld.Omega"

noncomputable section

namespace CerednikDrinfeld
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "PseudoUniformizer"
namespace HFin
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

theorem exists_finset_sub_eq_pow_mul
    {R : Type} [CommRing R] (ϖ : R) [Finite (R ⧸ Ideal.span {ϖ})] (k : ℕ) :
    ∃ S : Finset R, ∀ b : R, ∃ s ∈ S, ∃ e : R, b - s = ϖ ^ k * e := by
  classical

  have h1 : ∃ S₁ : Finset R, ∀ d : R, ∃ s ∈ S₁, ∃ e : R, d - s = ϖ * e := by
    haveI : Fintype (R ⧸ Ideal.span {ϖ}) := Fintype.ofFinite _
    refine ⟨Finset.univ.image (Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {ϖ}))),
      fun d => ⟨Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {ϖ})) (Ideal.Quotient.mk _ d),
        Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩⟩
    have hs : Ideal.Quotient.mk (Ideal.span {ϖ}) d =
        Ideal.Quotient.mk (Ideal.span {ϖ}) (Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {ϖ}))
          (Ideal.Quotient.mk _ d)) :=
      (Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := Ideal.span {ϖ})) _).symm
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at hs
    obtain ⟨e, he⟩ := hs
    exact ⟨e, he⟩
  induction k with
  | zero => exact ⟨{0}, fun b => ⟨0, Finset.mem_singleton_self 0, b, by simp⟩⟩
  | succ k ih =>
    obtain ⟨S, hS⟩ := ih
    obtain ⟨S₁, hS₁⟩ := h1
    refine ⟨(S ×ˢ S₁).image (fun p => p.1 + ϖ ^ k * p.2), fun b => ?_⟩
    obtain ⟨s, hs, e, he⟩ := hS b
    obtain ⟨s', hs', e', he'⟩ := hS₁ e
    refine ⟨s + ϖ ^ k * s', Finset.mem_image.mpr ⟨(s, s'), Finset.mem_product.mpr ⟨hs, hs'⟩, rfl⟩, e', ?_⟩
    rw [pow_succ]
    linear_combination he + ϖ ^ k * he'

theorem hfin_of_finite_residueField
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (ϖ₁ : PseudoUniformizer K₀ K) (n : ℕ) :
    ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ₁.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ₁.ϖ)) ^ n := by
  classical

  have hc0 : 0 < Valued.v (algebraMap K₀ K ϖ₁.ϖ) := ϖ₁.pos
  have hc1 : Valued.v (algebraMap K₀ K ϖ₁.ϖ) < 1 := ϖ₁.lt_one
  have hcn : Valued.v (algebraMap K₀ K ϖ₁.ϖ) ^ n ≠ 0 := pow_ne_zero _ hc0.ne'
  have hcn1 : Valued.v (algebraMap K₀ K ϖ₁.ϖ) ^ (n + 1) ≠ 0 := pow_ne_zero _ hc0.ne'

  obtain ⟨N, hN⟩ := hq _ hcn
  obtain ⟨M, hM⟩ := hq _ hcn1
  obtain ⟨S, hS⟩ := exists_finset_sub_eq_pow_mul ϖ (N + M)
  have hϖ0 : algebraMap R K₀ ϖ ≠ 0 := fun h =>
    hϖ.ne_zero ((IsFractionRing.to_map_eq_zero_iff (K := K₀)).mp h)
  refine ⟨S.image (fun s => (algebraMap R K₀ ϖ)⁻¹ ^ N * algebraMap R K₀ s), fun a ha => ?_⟩

  have hint' : Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ ^ N * a)) ≤ 1 := by
    rw [map_mul, map_pow, Valuation.map_mul, Valuation.map_pow]
    calc Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N * Valued.v (algebraMap K₀ K a)
        ≤ Valued.v (algebraMap K₀ K ϖ₁.ϖ) ^ n * (Valued.v (algebraMap K₀ K ϖ₁.ϖ))⁻¹ ^ n := mul_le_mul' hN ha
      _ = 1 := by rw [inv_pow, mul_inv_cancel₀ hcn]
  obtain ⟨b, hb⟩ := hv _ hint'

  obtain ⟨s, hs, e, he⟩ := hS b
  refine ⟨(algebraMap R K₀ ϖ)⁻¹ ^ N * algebraMap R K₀ s, Finset.mem_image_of_mem _ hs, ?_⟩
  have ha' : a = (algebraMap R K₀ ϖ)⁻¹ ^ N * algebraMap R K₀ b := by
    rw [hb, inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero N hϖ0), one_mul]
  have hat : a - (algebraMap R K₀ ϖ)⁻¹ ^ N * algebraMap R K₀ s =
      algebraMap R K₀ ϖ ^ M * algebraMap R K₀ e := by
    rw [ha', ← mul_sub, ← map_sub, he, map_mul, map_pow, pow_add, inv_pow, ← mul_assoc, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero N hϖ0), one_mul]
  rw [← map_sub, hat, map_mul, map_pow, Valuation.map_mul, Valuation.map_pow]
  calc Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ M * Valued.v (algebraMap K₀ K (algebraMap R K₀ e))
      ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ M * 1 := mul_le_mul_right (hint e) _
    _ = Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ M := mul_one _
    _ ≤ Valued.v (algebraMap K₀ K ϖ₁.ϖ) ^ (n + 1) := hM
    _ < Valued.v (algebraMap K₀ K ϖ₁.ϖ) ^ n := pow_lt_pow_right_of_lt_one₀ hc0 hc1 (Nat.lt_succ_self n)

end CerednikDrinfeld.Omega.HFin

theorem solution
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (ϖ₁ : PseudoUniformizer K₀ K) :
    ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ₁.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ₁.ϖ)) ^ n :=
  fun n => CerednikDrinfeld.Omega.HFin.hfin_of_finite_residueField R K₀ ϖ hϖ K hint hv hq ϖ₁ n

end

end S_CerednikDrinfeld_Omega_forall_exists_finset_v_sub_lt_pow_of_finite_quotient
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_forall_exists_finset_v_sub_lt_pow_of_finite_quotient (solution)
