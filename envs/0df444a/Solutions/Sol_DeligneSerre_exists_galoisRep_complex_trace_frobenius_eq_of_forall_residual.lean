-- Prove2me | solution 1 for DeligneSerre.exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/9c91d5e4-f5bc-50ec-91ed-305db06b0999

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Theorems.Thm_Representation_exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard
import Theorems.Thm_GaloisRep_exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel
import Theorems.Thm_CommRing_infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_isFrobeniusAt_ratAlgClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DeligneSerre_exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual
p2m_attr_erase "instance" "FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec BrauerNesbitt.actionEndoHom_apply BrauerNesbitt.actionTrace_apply BrauerNesbitt.actionEndo_apply"

set_option autoImplicit false

open Polynomial
open scoped MatrixGroups

namespace DeligneSerre86

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem finite_range_of_factorsThroughFiniteLevel {M : Type} [Group M] (ρ : Γℚ →* M)
    (hρ : GaloisFactorsThroughFiniteLevel ρ) : Finite (MonoidHom.range ρ) := by
  classical
  obtain ⟨L, hL, hker⟩ := hρ
  haveI := hL
  let F : Γℚ → (L →ₐ[ℚ] AlgebraicClosure ℚ) := fun σ => σ.toAlgHom.comp L.val
  have hF : ∀ σ τ : Γℚ, F σ = F τ → ρ σ = ρ τ := by
    intro σ τ h
    have hfix : ∀ x ∈ L, (τ⁻¹ * σ) x = x := by
      intro x hx
      have hx' := congrArg (fun φ : L →ₐ[ℚ] AlgebraicClosure ℚ => φ ⟨x, hx⟩) h
      simp only [F, AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_algHom] at hx'
      change σ x = τ x at hx'
      rw [AlgEquiv.mul_apply, hx']
      exact τ.symm_apply_apply x
    have h1 : ρ (τ⁻¹ * σ) = 1 := hker _ hfix
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  let g : (L →ₐ[ℚ] AlgebraicClosure ℚ) → M := fun v =>
    if h : ∃ σ : Γℚ, F σ = v then ρ h.choose else 1
  have hsub : (MonoidHom.range ρ : Set M) ⊆ Set.range g := by
    rintro _ ⟨σ, rfl⟩
    refine ⟨F σ, ?_⟩
    have h : ∃ σ' : Γℚ, F σ' = F σ := ⟨σ, rfl⟩
    simp only [g, dif_pos h]
    exact hF _ _ h.choose_spec
  exact Set.Finite.subset (Set.finite_range g) hsub |>.to_subtype

theorem exists_int_ne_zero_mem_span {R : Subalgebra ℤ ℂ} {x : R} (hint : IsIntegral ℤ x)
    (hx : x ≠ 0) : ∃ c : ℤ, c ≠ 0 ∧ ∃ y : R, (c : R) = x * y := by
  obtain ⟨p, hpm, hpx⟩ := hint
  have hp0 : p ≠ 0 := hpm.ne_zero
  obtain ⟨q, hpq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp0 0
  rw [map_zero, sub_zero] at hpq hq
  rw [Polynomial.X_dvd_iff] at hq

  have hqx : Polynomial.aeval x q = 0 := by
    have h : Polynomial.aeval x p = 0 := hpx
    rw [hpq, map_mul, map_pow, Polynomial.aeval_X] at h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (eq_zero_of_pow_eq_zero' h) hx
    · exact h

  refine ⟨q.coeff 0, hq, ?_⟩
  have hdecomp : q = C (q.coeff 0) + X * q.divX := by
    rw [add_comm, Polynomial.X_mul_divX_add]
  refine ⟨-(Polynomial.aeval x q.divX), ?_⟩
  have h2 : Polynomial.aeval x q = (q.coeff 0 : R) + x * Polynomial.aeval x q.divX := by
    conv_lhs => rw [hdecomp]
    rw [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    simp
  rw [hqx] at h2
  linear_combination -h2
where
  eq_zero_of_pow_eq_zero' {n : ℕ} (h : (x : R) ^ n = 0) : x = 0 := pow_eq_zero_iff'.mp h |>.1

theorem finite_setOf_prime_exists_apply_eq_zero (R : Subalgebra ℤ ℂ) [Module.Finite ℤ R]
    {x : R} (hx : x ≠ 0) :
    {ℓ : ℕ | ℓ.Prime ∧ ∃ φ : R →+* ZMod ℓ, φ x = 0}.Finite := by
  have hint : IsIntegral ℤ x := Algebra.IsIntegral.isIntegral x
  obtain ⟨c, hc, y, hy⟩ := exists_int_ne_zero_mem_span hint hx
  refine (c.natAbs.primeFactors.finite_toSet).subset ?_
  rintro ℓ ⟨hℓ, φ, hφ⟩
  simp only [Finset.mem_coe, Nat.mem_primeFactors, ne_eq, Int.natAbs_eq_zero]
  refine ⟨hℓ, ?_, hc⟩
  have h1 : (c : ZMod ℓ) = 0 := by
    have := congrArg φ hy
    rw [map_intCast, map_mul, hφ, zero_mul] at this
    exact this
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
  exact Int.natCast_dvd.mp h1

theorem eq_of_infinite_setOf_apply_eq (R : Subalgebra ℤ ℂ) [Module.Finite ℤ R] {x y : R}
    (h : {ℓ : ℕ | ℓ.Prime ∧ ∃ φ : R →+* ZMod ℓ, φ x = φ y}.Infinite) : x = y := by
  by_contra hne
  have hne' : x - y ≠ 0 := sub_ne_zero.mpr hne
  refine h ((finite_setOf_prime_exists_apply_eq_zero R hne').subset ?_)
  rintro ℓ ⟨hℓ, φ, hφ⟩
  exact ⟨hℓ, φ, by rw [map_sub, hφ, sub_self]⟩

theorem root_of_unity_of_charpoly {A : Matrix (Fin 2) (Fin 2) ℂ} {n : ℕ} (hA : A ^ n = 1)
    {z : ℂ} (hz : z ^ 2 - A.trace * z + A.det = 0) : z ^ n = 1 := by
  have hroot : IsRoot A.charpoly z := by
    rw [Matrix.charpoly_fin_two, IsRoot.def]
    simp only [eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C]
    exact hz
  have hmem : z ∈ spectrum ℂ A := Matrix.mem_spectrum_of_isRoot_charpoly hroot
  have hpow : z ^ n ∈ spectrum ℂ (A ^ n) := spectrum.pow_mem_pow A n hmem
  rw [hA, spectrum.one_eq, Set.mem_singleton_iff] at hpow
  exact hpow

theorem exists_trace_eq_add_of_pow_eq_one {A : Matrix (Fin 2) (Fin 2) ℂ} {n : ℕ} (hA : A ^ n = 1) :
    ∃ α β : ℂ, α ^ n = 1 ∧ β ^ n = 1 ∧ A.trace = α + β ∧ A.det = α * β := by

  let q : ℂ[X] := X ^ 2 - C A.trace * X + C A.det
  have hq : q.degree = 2 := by
    simp only [q]
    compute_degree!
  obtain ⟨α, hα⟩ := Complex.exists_root (show 0 < q.degree by rw [hq]; norm_num)
  have hα' : α ^ 2 - A.trace * α + A.det = 0 := by
    simp only [q, IsRoot.def, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C] at hα
    exact hα
  refine ⟨α, A.trace - α, root_of_unity_of_charpoly hA hα', root_of_unity_of_charpoly hA ?_, by ring,
    ?_⟩
  · linear_combination hα'
  · linear_combination hα'

theorem coeff_quadratic {S : Type*} [CommRing S] (u v : S) :
    (X ^ 2 - C u * X + C v : S[X]).coeff 1 = -u ∧ (X ^ 2 - C u * X + C v : S[X]).coeff 0 = v := by
  constructor
  · simp [coeff_X_pow, coeff_X, coeff_C]
  · simp [coeff_X_pow, coeff_C]

theorem exists_lift_at
    {N : ℕ} (R : Subalgebra ℤ ℂ) {m : ℕ} (hm : 0 < m) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m)
    (hζR : ζ ∈ R) {t d : ℕ → ℂ} (ht : ∀ p : ℕ, p.Prime → ¬ p ∣ N → t p ∈ R)
    (hd : ∀ p : ℕ, p.Prime → ¬ p ∣ N → d p ∈ R)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓm : ¬ ℓ ∣ m) (φ : R →+* ZMod ℓ)
    (ρbar : Γℚ →* GL (Fin 2) (ZMod ℓ)) (hfl : GaloisFactorsThroughFiniteLevel ρbar)
    (hcard : Nat.card (MonoidHom.range ρbar) ∣ m)
    (hfrob : ∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N), p ≠ ℓ →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρbar σ = 1) ∧
        ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
          ((ρbar σ : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).charpoly =
            X ^ 2 - C (φ ⟨t p, ht p hp hpN⟩) * X + C (φ ⟨d p, hd p hp hpN⟩)) :
    ∃ ρ : Γℚ →* GL (Fin 2) ℂ, GaloisFactorsThroughFiniteLevel ρ ∧
      ∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N), p ≠ ℓ →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
          ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
            ∃ a b : ℂ, a ^ m = 1 ∧ b ^ m = 1 ∧
              ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace = a + b ∧
              ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det = a * b ∧
              ∃ (hab : a + b ∈ R) (hab' : a * b ∈ R),
                φ ⟨a + b, hab⟩ = φ ⟨t p, ht p hp hpN⟩ ∧
                φ ⟨a * b, hab'⟩ = φ ⟨d p, hd p hp hpN⟩ := by
  classical
  set G := MonoidHom.range ρbar with hG
  haveI : Finite G := finite_range_of_factorsThroughFiniteLevel ρbar hfl
  have hℓG : ¬ ℓ ∣ Nat.card G := fun h => hℓm (h.trans hcard)
  have hGm : ∀ g : G, g ^ m = 1 := fun g =>
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard g).trans hcard)
  obtain ⟨ρG, hρG⟩ :=
    Representation.exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard G ℓ hℓG (ZMod ℓ) 2 m
      hm hℓm hGm R ζ hζ hζR φ G.subtype
  have hρ1 : ∀ σ : Γℚ, ρbar σ = 1 → (ρG.comp ρbar.rangeRestrict) σ = 1 := by
    intro σ hσ
    have h1 : ρbar.rangeRestrict σ = 1 := Subtype.ext (by simp [hσ])
    rw [MonoidHom.comp_apply, h1, map_one]
  refine ⟨ρG.comp ρbar.rangeRestrict, ?_, ?_⟩
  · obtain ⟨L, hL, hker⟩ := hfl
    exact ⟨L, hL, fun σ hσ => hρ1 σ (hker σ hσ)⟩
  · intro p hp hpN hpℓ A hA
    obtain ⟨hin, hfr⟩ := hfrob p hp hpN hpℓ A hA
    refine ⟨fun σ hσ => hρ1 σ (hin σ hσ), fun σ hσ => ?_⟩
    set g : G := ρbar.rangeRestrict σ with hg
    have hgσ : ((G.subtype g : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) =
        ((ρbar σ : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) := rfl
    have hρσ : (ρG.comp ρbar.rangeRestrict) σ = ρG g := rfl
    rw [hρσ]

    have hpow : ((ρG g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) ^ m = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hGm g, map_one, Units.val_one]
    obtain ⟨a, b, ha, hb, htr, hdet⟩ := exists_trace_eq_add_of_pow_eq_one hpow
    refine ⟨a, b, ha, hb, htr, hdet, ?_⟩

    obtain ⟨P, hPℂ, hPφ⟩ := hρG g
    rw [Matrix.charpoly_fin_two, htr, hdet] at hPℂ
    rw [hgσ, hfr σ hσ] at hPφ
    have hcoe : ∀ z : R, algebraMap R ℂ z = (z : ℂ) := fun z => rfl

    have h1ℂ := congrArg (fun Q : ℂ[X] => Q.coeff 1) hPℂ
    have h1φ := congrArg (fun Q : (ZMod ℓ)[X] => Q.coeff 1) hPφ
    have h0ℂ := congrArg (fun Q : ℂ[X] => Q.coeff 0) hPℂ
    have h0φ := congrArg (fun Q : (ZMod ℓ)[X] => Q.coeff 0) hPφ
    simp only [Polynomial.coeff_map, (coeff_quadratic _ _).1, (coeff_quadratic _ _).2, hcoe] at h1ℂ h1φ h0ℂ h0φ

    have hab_eq : a + b = ((-P.coeff 1 : R) : ℂ) := by
      rw [Subalgebra.coe_neg, h1ℂ, neg_neg]
    have hab'_eq : a * b = ((P.coeff 0 : R) : ℂ) := h0ℂ.symm
    have hab : a + b ∈ R := by rw [hab_eq]; exact (-P.coeff 1).2
    have hab' : a * b ∈ R := by rw [hab'_eq]; exact (P.coeff 0).2
    refine ⟨hab, hab', ?_, ?_⟩
    · have : (⟨a + b, hab⟩ : R) = -P.coeff 1 := Subtype.ext hab_eq
      rw [this, map_neg, h1φ, neg_neg]
    · have : (⟨a * b, hab'⟩ : R) = P.coeff 0 := Subtype.ext hab'_eq
      rw [this, h0φ]

theorem infinite_setOf_prime_nonempty (R : Subalgebra ℤ ℂ) [Module.Finite ℤ R] :
    {ℓ : ℕ | ℓ.Prime ∧ Nonempty (R →+* ZMod ℓ)}.Infinite :=
  CommRing.infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int R

theorem exists_eq_add_eq_mul
    {N : ℕ} (R : Subalgebra ℤ ℂ) [Module.Finite ℤ R] {m : ℕ} (hm : 0 < m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (hζR : ζ ∈ R) {t d : ℕ → ℂ}
    (ht : ∀ p : ℕ, p.Prime → ¬ p ∣ N → t p ∈ R) (hd : ∀ p : ℕ, p.Prime → ¬ p ∣ N → d p ∈ R)
    (hfam : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (φ : R →+* ZMod ℓ),
      ∃ ρ : Γℚ →* GL (Fin 2) (ZMod ℓ), GaloisFactorsThroughFiniteLevel ρ ∧
        Nat.card (MonoidHom.range ρ) ∣ m ∧
        ∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N), p ≠ ℓ →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
            (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
            ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
              ((ρ σ : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).charpoly =
                X ^ 2 - C (φ ⟨t p, ht p hp hpN⟩) * X + C (φ ⟨d p, hd p hp hpN⟩))
    (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    ∃ a b : ℂ, a ^ m = 1 ∧ b ^ m = 1 ∧ t p = a + b ∧ d p = a * b := by
  classical
  haveI : NeZero m := ⟨hm.ne'⟩
  set zR : R := ⟨ζ, hζR⟩ with hzR
  set tR : R := ⟨t p, ht p hp hpN⟩ with htR
  set dR : R := ⟨d p, hd p hp hpN⟩ with hdR

  let Q : ℕ → ℕ × ℕ → Prop := fun ℓ ij => ∃ φ : R →+* ZMod ℓ,
    φ (zR ^ ij.1 + zR ^ ij.2) = φ tR ∧ φ (zR ^ ij.1 * zR ^ ij.2) = φ dR
  let box : Finset (ℕ × ℕ) := Finset.range m ×ˢ Finset.range m

  let PR : Set ℕ := {ℓ : ℕ | ℓ.Prime ∧ Nonempty (R →+* ZMod ℓ)}
  let PR' : Set ℕ := PR \ ↑(insert p m.primeFactors)
  have hPR' : PR'.Infinite := (infinite_setOf_prime_nonempty R).diff (Finset.finite_toSet _)

  have hcover : ∀ ℓ ∈ PR', ∃ ij ∈ box, Q ℓ ij := by
    rintro ℓ ⟨⟨hℓ, ⟨φ⟩⟩, hℓ'⟩
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, Nat.mem_primeFactors,
      not_or, not_and] at hℓ'
    have hℓp : p ≠ ℓ := fun h => hℓ'.1 h.symm
    have hℓm : ¬ ℓ ∣ m := fun h => hℓ'.2 hℓ h hm.ne'
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    obtain ⟨ρbar, hfl, hcard, hfrob⟩ := hfam ℓ φ
    obtain ⟨ρ, -, hρ⟩ := exists_lift_at R hm hζ hζR ht hd hℓm φ ρbar hfl hcard hfrob
    obtain ⟨A, σ, hA, hσ⟩ := ValuationSubring.exists_liesOverPrime_isFrobeniusAt_ratAlgClosure ⟨p, hp⟩
    obtain ⟨a, b, ha, hb, -, -, hab, hab', hφ1, hφ2⟩ := (hρ p hp hpN hℓp A hA).2 σ hσ
    obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one ha
    obtain ⟨j, hj, rfl⟩ := hζ.eq_pow_of_pow_eq_one hb
    refine ⟨(i, j), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi, Finset.mem_range.mpr hj⟩,
      φ, ?_, ?_⟩
    · have : zR ^ i + zR ^ j = ⟨ζ ^ i + ζ ^ j, hab⟩ := Subtype.ext (by simp [zR])
      rw [this]; exact hφ1
    · have : zR ^ i * zR ^ j = ⟨ζ ^ i * ζ ^ j, hab'⟩ := Subtype.ext (by simp [zR])
      rw [this]; exact hφ2

  have hpigeon : ∃ ij ∈ box, {ℓ : ℕ | ℓ.Prime ∧ Q ℓ ij}.Infinite := by
    by_contra hcon
    push Not at hcon
    apply hPR'
    refine (Set.Finite.biUnion (Finset.finite_toSet box) fun ij hij => hcon ij hij).subset ?_
    intro ℓ hℓ
    obtain ⟨ij, hij, hQ⟩ := hcover ℓ hℓ
    exact Set.mem_biUnion hij ⟨hℓ.1.1, hQ⟩
  obtain ⟨⟨i, j⟩, -, hinf⟩ := hpigeon

  have h1 : zR ^ i + zR ^ j = tR := by
    refine eq_of_infinite_setOf_apply_eq R (hinf.mono ?_)
    rintro ℓ ⟨hℓ, φ, hφ, -⟩
    exact ⟨hℓ, φ, hφ⟩
  have h2 : zR ^ i * zR ^ j = dR := by
    refine eq_of_infinite_setOf_apply_eq R (hinf.mono ?_)
    rintro ℓ ⟨hℓ, φ, -, hφ⟩
    exact ⟨hℓ, φ, hφ⟩
  refine ⟨ζ ^ i, ζ ^ j, by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow],
    by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow], ?_, ?_⟩
  · have := congrArg Subtype.val h1
    simpa [zR, tR] using this.symm
  · have := congrArg Subtype.val h2
    simpa [zR, dR] using this.symm

theorem exists_good_lift
    {N : ℕ} (R : Subalgebra ℤ ℂ) [Module.Finite ℤ R] {m : ℕ} (hm : 0 < m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (hζR : ζ ∈ R) {t d : ℕ → ℂ}
    (ht : ∀ p : ℕ, p.Prime → ¬ p ∣ N → t p ∈ R) (hd : ∀ p : ℕ, p.Prime → ¬ p ∣ N → d p ∈ R)
    (hfam : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (φ : R →+* ZMod ℓ),
      ∃ ρ : Γℚ →* GL (Fin 2) (ZMod ℓ), GaloisFactorsThroughFiniteLevel ρ ∧
        Nat.card (MonoidHom.range ρ) ∣ m ∧
        ∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N), p ≠ ℓ →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
            (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
            ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
              ((ρ σ : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).charpoly =
                X ^ 2 - C (φ ⟨t p, ht p hp hpN⟩) * X + C (φ ⟨d p, hd p hp hpN⟩))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓm : ¬ ℓ ∣ m) (φ : R →+* ZMod ℓ)
    (hinj_add : ∀ i j i' j' : ℕ,
      φ ((⟨ζ, hζR⟩ : R) ^ i + (⟨ζ, hζR⟩ : R) ^ j) = φ ((⟨ζ, hζR⟩ : R) ^ i' + (⟨ζ, hζR⟩ : R) ^ j') →
        (⟨ζ, hζR⟩ : R) ^ i + (⟨ζ, hζR⟩ : R) ^ j = (⟨ζ, hζR⟩ : R) ^ i' + (⟨ζ, hζR⟩ : R) ^ j')
    (hinj_mul : ∀ i j i' j' : ℕ,
      φ ((⟨ζ, hζR⟩ : R) ^ i * (⟨ζ, hζR⟩ : R) ^ j) = φ ((⟨ζ, hζR⟩ : R) ^ i' * (⟨ζ, hζR⟩ : R) ^ j') →
        (⟨ζ, hζR⟩ : R) ^ i * (⟨ζ, hζR⟩ : R) ^ j = (⟨ζ, hζR⟩ : R) ^ i' * (⟨ζ, hζR⟩ : R) ^ j') :
    ∃ ρ : Γℚ →* GL (Fin 2) ℂ, GaloisFactorsThroughFiniteLevel ρ ∧
      ∀ (p : ℕ), p.Prime → ¬ p ∣ N → p ≠ ℓ →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
          ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
            ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace = t p ∧
            ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det = d p := by
  classical
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  set zR : R := ⟨ζ, hζR⟩ with hzR
  obtain ⟨ρbar, hfl, hcard, hfrob⟩ := hfam ℓ φ
  obtain ⟨ρ, hρfl, hρ⟩ := exists_lift_at R hm hζ hζR ht hd hℓm φ ρbar hfl hcard hfrob
  refine ⟨ρ, hρfl, fun p hp hpN hpℓ A hA => ?_⟩
  obtain ⟨hin, hfr⟩ := hρ p hp hpN hpℓ A hA
  refine ⟨hin, fun σ hσ => ?_⟩
  obtain ⟨a, b, ha, hb, htr, hdet, hab, hab', hφ1, hφ2⟩ := hfr σ hσ
  obtain ⟨a', b', ha', hb', ht', hd'⟩ := exists_eq_add_eq_mul R hm hζ hζR ht hd hfam p hp hpN
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one ha
  obtain ⟨j, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hb
  obtain ⟨i', -, rfl⟩ := hζ.eq_pow_of_pow_eq_one ha'
  obtain ⟨j', -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hb'
  have e1 : (⟨ζ ^ i + ζ ^ j, hab⟩ : R) = zR ^ i + zR ^ j := Subtype.ext (by simp [zR])
  have e2 : (⟨t p, ht p hp hpN⟩ : R) = zR ^ i' + zR ^ j' := Subtype.ext (by simp [zR, ht'])
  have e3 : (⟨ζ ^ i * ζ ^ j, hab'⟩ : R) = zR ^ i * zR ^ j := Subtype.ext (by simp [zR])
  have e4 : (⟨d p, hd p hp hpN⟩ : R) = zR ^ i' * zR ^ j' := Subtype.ext (by simp [zR, hd'])
  rw [e1, e2] at hφ1
  rw [e3, e4] at hφ2
  have k1 := congrArg Subtype.val (hinj_add i j i' j' hφ1)
  have k2 := congrArg Subtype.val (hinj_mul i j i' j' hφ2)
  simp only [zR, Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_pow] at k1 k2
  exact ⟨by rw [htr, k1, ht'], by rw [hdet, k2, hd']⟩

theorem finite_setOf_prime_exists_apply_eq (R : Subalgebra ℤ ℂ) [Module.Finite ℤ R] (z w : R) :
    {ℓ : ℕ | ℓ.Prime ∧ z ≠ w ∧ ∃ φ : R →+* ZMod ℓ, φ z = φ w}.Finite := by
  by_cases hzw : z = w
  · convert Set.finite_empty
    ext ℓ
    simp [hzw]
  · refine (finite_setOf_prime_exists_apply_eq_zero R (sub_ne_zero.mpr hzw)).subset ?_
    rintro ℓ ⟨hℓ, -, φ, hφ⟩
    exact ⟨hℓ, φ, by rw [map_sub, hφ, sub_self]⟩

end DeligneSerre86

open DeligneSerre86 in

theorem solution
    (N : ℕ) (R : Subalgebra ℤ ℂ) [Module.Finite ℤ R]
    (m : ℕ) (hm : 0 < m) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (hζR : ζ ∈ R)
    (t d : ℕ → ℂ) (ht : ∀ p : ℕ, p.Prime → ¬ p ∣ N → t p ∈ R)
    (hd : ∀ p : ℕ, p.Prime → ¬ p ∣ N → d p ∈ R)
    (hfam : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (φ : R →+* ZMod ℓ),
      ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) (ZMod ℓ),
        GaloisFactorsThroughFiniteLevel ρ ∧
        Nat.card (MonoidHom.range ρ) ∣ m ∧
        ∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N), p ≠ ℓ →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
            (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
            ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ p →
              ((ρ σ : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).charpoly =
                X ^ 2 - C (φ ⟨t p, ht p hp hpN⟩) * X + C (φ ⟨d p, hd p hp hpN⟩)) :
    ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) ℂ,
      GaloisFactorsThroughFiniteLevel ρ ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
          ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ p →
            ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace = t p ∧
            ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det = d p := by
  classical

  by_cases hN : N = 0
  · subst hN
    refine ⟨1, ⟨⊥, inferInstance, fun σ _ => rfl⟩, fun p hp hpN => absurd (dvd_zero p) hpN⟩
  haveI : NeZero m := ⟨hm.ne'⟩
  set zR : R := ⟨ζ, hζR⟩ with hzR
  have hzm : zR ^ m = 1 := Subtype.ext (by simp [zR, hζ.pow_eq_one])
  have hzmod : ∀ i : ℕ, zR ^ i = zR ^ (i % m) := fun i => by
    conv_lhs => rw [← Nat.mod_add_div i m, pow_add, pow_mul, hzm, one_pow, mul_one]

  let box : Finset (ℕ × ℕ) := Finset.range m ×ˢ Finset.range m
  let Zfin : Finset R :=
    box.image (fun ij => zR ^ ij.1 + zR ^ ij.2) ∪ box.image (fun ij => zR ^ ij.1 * zR ^ ij.2)
  have hbox : ∀ i j : ℕ, (i % m, j % m) ∈ box := fun i j =>
    Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt i hm), Finset.mem_range.mpr (Nat.mod_lt j hm)⟩
  have hmem_add : ∀ i j : ℕ, zR ^ i + zR ^ j ∈ Zfin := fun i j => by
    refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i % m, j % m), hbox i j, ?_⟩)
    rw [hzmod i, hzmod j]
  have hmem_mul : ∀ i j : ℕ, zR ^ i * zR ^ j ∈ Zfin := fun i j => by
    refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i % m, j % m), hbox i j, ?_⟩)
    rw [hzmod i, hzmod j]

  let Bad : Set ℕ := {ℓ : ℕ | ℓ.Prime ∧ ∃ z ∈ Zfin, ∃ w ∈ Zfin, z ≠ w ∧ ∃ φ : R →+* ZMod ℓ, φ z = φ w}
  have hBad : Bad.Finite := by
    refine (Set.Finite.biUnion (Finset.finite_toSet Zfin) fun z _ =>
      Set.Finite.biUnion (Finset.finite_toSet Zfin) fun w _ =>
        finite_setOf_prime_exists_apply_eq R z w).subset ?_
    rintro ℓ ⟨hℓ, z, hz, w, hw, hzw, φ, hφ⟩
    exact Set.mem_biUnion hz (Set.mem_biUnion hw ⟨hℓ, hzw, φ, hφ⟩)

  let Good : Set ℕ := {ℓ : ℕ | ℓ.Prime ∧ Nonempty (R →+* ZMod ℓ)} \ (Bad ∪ ↑m.primeFactors)
  have hGood : Good.Infinite :=
    (infinite_setOf_prime_nonempty R).diff (hBad.union (Finset.finite_toSet _))

  have hgood : ∀ ℓ ∈ Good, ℓ.Prime ∧
      ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) ℂ,
        GaloisFactorsThroughFiniteLevel ρ ∧
        ∀ (p : ℕ), p.Prime → ¬ p ∣ N → p ≠ ℓ →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
            (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
            ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ p →
              ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace = t p ∧
              ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det = d p := by
    rintro ℓ ⟨⟨hℓ, ⟨φ⟩⟩, hℓ'⟩
    simp only [Set.mem_union, Finset.mem_coe, Nat.mem_primeFactors, not_or] at hℓ'
    have hℓm : ¬ ℓ ∣ m := fun h => hℓ'.2 ⟨hℓ, h, hm.ne'⟩
    have hinj : ∀ z ∈ Zfin, ∀ w ∈ Zfin, φ z = φ w → z = w := by
      intro z hz w hw hzw
      by_contra hne
      exact hℓ'.1 ⟨hℓ, z, hz, w, hw, hne, φ, hzw⟩
    refine ⟨hℓ, exists_good_lift R hm hζ hζR ht hd hfam hℓ hℓm φ ?_ ?_⟩
    · intro i j i' j' h
      exact hinj _ (hmem_add i j) _ (hmem_add i' j') h
    · intro i j i' j' h
      exact hinj _ (hmem_mul i j) _ (hmem_mul i' j') h

  obtain ⟨ℓ₀, hℓ₀G⟩ := hGood.nonempty
  obtain ⟨ℓ₁, hℓ₁G, hℓ₁₀⟩ := (hGood.diff (Set.finite_singleton ℓ₀)).nonempty
  rw [Set.mem_singleton_iff] at hℓ₁₀
  obtain ⟨hℓ₀, ρ₀, hρ₀fl, hρ₀⟩ := hgood ℓ₀ hℓ₀G
  obtain ⟨hℓ₁, ρ₁, hρ₁fl, hρ₁⟩ := hgood ℓ₁ hℓ₁G

  obtain ⟨P, hP⟩ :=
    GaloisRep.exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel ρ₀ ρ₁ hρ₀fl
      hρ₁fl (insert ℓ₀ (insert ℓ₁ N.primeFactors)) (by
        intro p hp hpS A hA σ hσ
        simp only [Finset.mem_insert, Nat.mem_primeFactors, not_or] at hpS
        have hpN : ¬ p ∣ N := fun h => hpS.2.2 ⟨hp, h, hN⟩
        obtain ⟨t0, d0⟩ := (hρ₀ p hp hpN hpS.1 A hA).2 σ hσ
        obtain ⟨t1, d1⟩ := (hρ₁ p hp hpN hpS.2.1 A hA).2 σ hσ
        rw [Matrix.charpoly_fin_two, Matrix.charpoly_fin_two, t0, d0, t1, d1])

  refine ⟨ρ₀, hρ₀fl, fun p hp hpN A hA => ?_⟩
  by_cases hp0 : p = ℓ₀
  · have hp1 : p ≠ ℓ₁ := fun h => hℓ₁₀ (h.symm.trans hp0)
    obtain ⟨hin1, hfr1⟩ := hρ₁ p hp hpN hp1 A hA
    have hconj : ∀ σ, ρ₀ σ = P⁻¹ * ρ₁ σ * P := fun σ => by rw [hP σ]; group
    refine ⟨fun σ hσ => by rw [hconj σ, hin1 σ hσ, mul_one, inv_mul_cancel], fun σ hσ => ?_⟩
    obtain ⟨t1, d1⟩ := hfr1 σ hσ
    rw [hconj σ, Units.val_mul, Units.val_mul]
    refine ⟨?_, ?_⟩
    · rw [Matrix.trace_units_conj', t1]
    · rw [Matrix.det_mul, Matrix.det_mul, d1, mul_comm _ (d p), mul_assoc, ← Matrix.det_mul,
        Units.inv_mul, Matrix.det_one, mul_one]
  · exact hρ₀ p hp hpN hp0 A hA

end S_DeligneSerre_exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual
end P2MW
export P2MW.S_DeligneSerre_exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual (solution)
