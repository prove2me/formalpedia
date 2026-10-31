-- Prove2me | solution 1 for DiazModulus.ringKrullDim_quotient_sectionIdeal_le
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T10:03:53.179577+00:00
-- url     : https://prove2.me/submissions/e2745c0f-5f69-4f48-9932-3f3a6247d542

import Mathlib
import Definitions.Def_DiazMultiplicity

open Complex ComplexConjugate

/-! # The section quotient has dimension at most `|H| + |J|`

Let `S = K[X, Y, Z] ⧸ 𝔞` with `𝔞 = sectionIdeal ℓ ψ`, and let `P = K[t_H, s_J]` act on `S` by `t_h ↦ X_h`,
`s_j ↦ Y_j + Z_j`. Then `S` is integral over `P` (design B, H2), so `dim S ≤ dim P = |H| + |J|`
(`ringKrullDim_le_of_isIntegral`: comap along an integral extension is strictly monotone,
`Ideal.comap_lt_comap_of_integral_mem_sdiff`; then `MvPolynomial.ringKrullDim_of_isNoetherianRing`).
Integrality is checked on the generators `X_v` (by `MvPolynomial.induction_on`):
* `X_h`, `h ∈ H`, is in the image of `P`; for `h ∉ H` the form `ℓ_h ∈ 𝔞` is `X_h + Σ_{h' ∈ H} ℓ_h h' X_h'`.
* Since `Y_iZ_i − 1 ∈ 𝔞`, `Y_i` is a unit `u_i` of `S` with inverse `Z_i`. For `j ∈ J`, `Y_j` and `Z_j` are roots
  of `T² − (Y_j + Z_j)T + 1`, so every `u_j^m` (`m ∈ ℤ`) is integral.
* For `i ∉ J`, `torusMono ψ_i − 1 ∈ 𝔞` reads `Π_k u_k^{ψ_i k} = 1`, and triangularity leaves
  `u_i^{ψ_i i} = Π_{j ∈ J} u_j^{−ψ_i j}`: so `u_i^{±ψ_i i}` are integral, and `Y_i`, `Z_i` follow by
  `IsIntegral.of_pow` with exponent `|ψ_i i| > 0`. -/

namespace C13_H2
open DiazModulus MvPolynomial

/-- Integral extensions do not raise the Krull dimension (going-up incomparability). -/
theorem ringKrullDim_le_of_isIntegral {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] : ringKrullDim S ≤ ringKrullDim R := by
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
  intro P Q hlt
  have hlt' : P.asIdeal < Q.asIdeal := hlt
  obtain ⟨hle, x, hxQ, hxP⟩ := SetLike.lt_iff_le_and_exists.mp hlt'
  show Ideal.comap (algebraMap R S) P.asIdeal < Ideal.comap (algebraMap R S) Q.asIdeal
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff (R := R) hle ⟨hxQ, hxP⟩
    (Algebra.IsIntegral.isIntegral x)

/-- `y^{m⁺} (y⁻¹)^{m⁻} = y^m` for a unit `y`. -/
theorem units_pow_toNat_mul {S : Type*} [CommRing S] (u : Sˣ) (m : ℤ) :
    (u : S) ^ m.toNat * ((u⁻¹ : Sˣ) : S) ^ (-m).toNat = ((u ^ m : Sˣ) : S) := by
  rcases le_or_gt 0 m with hm | hm
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    have : (-(k : ℤ)).toNat = 0 := by omega
    simp [this]
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, m = -k := ⟨(-m).toNat, by omega⟩
    subst hk
    have : (-(k : ℤ)).toNat = 0 := by omega
    simp [this, zpow_neg, zpow_natCast]

end C13_H2

open DiazModulus C13_H2 MvPolynomial in
theorem solution {K A₀ A₁ : Type*} [Field K] [Fintype A₀] [Fintype A₁] (H : Finset A₀) (J : Finset A₁)
    (ℓ : A₀ → A₀ → K) (ψ : A₁ → A₁ → ℤ) (hℓ : ∀ h ∉ H, ℓ h h = 1 ∧ ∀ h' ∉ H, h' ≠ h → ℓ h h' = 0)
    (hψ : ∀ i ∉ J, ψ i i ≠ 0 ∧ ∀ i' ∉ J, i' ≠ i → ψ i i' = 0) :
    ringKrullDim ((MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) ⧸ sectionIdeal ℓ ψ) ≤ ((H.card + J.card : ℕ) : WithBot ℕ∞) := by
  classical

  set 𝔞 := sectionIdeal (K := K) ℓ ψ with h𝔞
  let S := MvPolynomial (A₀ ⊕ (A₁ × Bool)) K ⧸ 𝔞
  let mk : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K →ₐ[K] S := Ideal.Quotient.mkₐ K 𝔞
  let P := MvPolynomial (↥H ⊕ ↥J) K
  let φ : P →ₐ[K] S := MvPolynomial.aeval (Sum.elim (fun h => mk (X (Sum.inl h.1)))
    fun j => mk (X (Sum.inr (j.1, true))) + mk (X (Sum.inr (j.1, false))))
  let _ : Algebra P S := φ.toRingHom.toAlgebra
  have hmem : ∀ f ∈ 𝔞, mk f = 0 := fun f hf => Ideal.Quotient.eq_zero_iff_mem.mpr hf
  -- the units `u_i = Y_i`
  have hYZ : ∀ i : A₁, mk (X (Sum.inr (i, true))) * mk (X (Sum.inr (i, false))) = 1 := by
    intro i
    have : (X (Sum.inr (i, true)) * X (Sum.inr (i, false)) - 1 : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) ∈ 𝔞 :=
      Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))
    have h := hmem _ this
    rw [map_sub, map_mul, map_one, sub_eq_zero] at h
    exact h
  let u : A₁ → Sˣ := fun i => Units.mkOfMulEqOne _ _ (hYZ i)
  have hu : ∀ i, (u i : S) = mk (X (Sum.inr (i, true))) := fun i => rfl
  have huinv : ∀ i, ((u i)⁻¹ : Sˣ) = mk (X (Sum.inr (i, false))) := fun i => rfl
  have hφX : ∀ v, IsIntegral P (algebraMap P S v) := fun v => isIntegral_algebraMap
  have halg : ∀ v, algebraMap P S v = MvPolynomial.aeval (Sum.elim (fun h : ↥H => mk (X (Sum.inl h.1)))
      fun j : ↥J => mk (X (Sum.inr (j.1, true))) + mk (X (Sum.inr (j.1, false)))) v := fun v => rfl
  have hconst : ∀ c : K, IsIntegral P (algebraMap K S c) := by
    intro c
    have := hφX (C c)
    rwa [halg, MvPolynomial.aeval_C] at this
  -- `X_h`, `h ∈ H`
  have hXH : ∀ h ∈ H, IsIntegral P (mk (X (Sum.inl h))) := by
    intro h hh
    have := hφX (X (Sum.inl ⟨h, hh⟩))
    rwa [halg, aeval_X, Sum.elim_inl] at this
  -- `u_j^{±1}`, `j ∈ J`
  have hroot : ∀ j ∈ J, ∀ b : Bool, IsIntegral P (mk (X (Sum.inr (j, b)))) := by
    intro j hj b
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (X (Sum.inr ⟨j, hj⟩) : P) * Polynomial.X + 1, ?_, ?_⟩
    · have : (Polynomial.X ^ 2 - Polynomial.C (X (Sum.inr ⟨j, hj⟩) : P) * Polynomial.X + 1) =
          Polynomial.X ^ 2 + (-(Polynomial.C (X (Sum.inr ⟨j, hj⟩) : P) * Polynomial.X) + 1) := by ring
      rw [this]
      apply Polynomial.monic_X_pow_add
      calc _ ≤ max (-(Polynomial.C (X (Sum.inr ⟨j, hj⟩) : P) * Polynomial.X)).degree (1 : Polynomial P).degree :=
            Polynomial.degree_add_le _ _
        _ < 2 := by
          rw [Polynomial.degree_neg, Polynomial.degree_one]
          refine max_lt (lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by norm_num)) (by norm_num)
    · have hs : algebraMap P S (X (Sum.inr ⟨j, hj⟩)) =
          mk (X (Sum.inr (j, true))) + mk (X (Sum.inr (j, false))) := by
        rw [halg, aeval_X, Sum.elim_inr]
      have h1 := hYZ j
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X,
        Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_one, hs]
      cases b
      · linear_combination (-1 : S) * h1
      · linear_combination (-1 : S) * h1
  have hunitJ : ∀ j ∈ J, ∀ m : ℤ, IsIntegral P ((u j ^ m : Sˣ) : S) := by
    intro j hj m
    rcases Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩
    · simpa [zpow_natCast, hu] using (hroot j hj true).pow k
    · simpa [zpow_neg, zpow_natCast, ← inv_pow, huinv] using (hroot j hj false).pow k
  have hprodJ : ∀ m : A₁ → ℤ, IsIntegral P ((∏ j ∈ J, u j ^ m j : Sˣ) : S) := by
    intro m
    rw [Units.coe_prod]
    exact (integralClosure P S).prod_mem fun j hj => hunitJ j hj (m j)
  -- the relation `Π_k u_k^{ψ_i k} = 1`
  have hrel : ∀ i, ∏ k, u k ^ ψ i k = 1 := by
    intro i
    have hin : (torusMono (A₀ := A₀) (K := K) (ψ i) - 1) ∈ 𝔞 :=
      Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
    have h := hmem _ hin
    rw [map_sub, map_one, sub_eq_zero, torusMono, map_prod] at h
    apply Units.ext
    rw [Units.coe_prod, Units.val_one, ← h]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← units_pow_toNat_mul, map_mul, map_pow, map_pow, hu, huinv]
  have hunitOut : ∀ i ∉ J, IsIntegral P ((u i ^ ψ i i : Sˣ) : S) ∧
      IsIntegral P ((u i ^ (-ψ i i) : Sˣ) : S) := by
    intro i hi
    have hsplit : ∏ k, u k ^ ψ i k = u i ^ ψ i i * ∏ j ∈ J, u j ^ ψ i j := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      congr 1
      refine (Finset.prod_subset (fun j hj => Finset.mem_erase.mpr ⟨by rintro rfl; exact hi hj,
        Finset.mem_univ _⟩) fun k hk hkJ => ?_).symm
      rw [(hψ i hi).2 k hkJ (Finset.ne_of_mem_erase hk), zpow_zero]
    have h1 := hrel i
    rw [hsplit] at h1
    have hQ : (∏ j ∈ J, u j ^ (-ψ i j)) * ∏ j ∈ J, u j ^ ψ i j = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun j _ => by rw [← zpow_add, neg_add_cancel, zpow_zero]
    have e1 : u i ^ ψ i i = ∏ j ∈ J, u j ^ (-ψ i j) :=
      (eq_inv_of_mul_eq_one_left h1).trans (eq_inv_of_mul_eq_one_left hQ).symm
    have e2 : u i ^ (-ψ i i) = ∏ j ∈ J, u j ^ ψ i j := by
      rw [zpow_neg]; exact (eq_inv_of_mul_eq_one_right h1).symm
    rw [e1, e2]; exact ⟨hprodJ _, hprodJ _⟩
  have hOut : ∀ i ∉ J, ∀ b : Bool, IsIntegral P (mk (X (Sum.inr (i, b)))) := by
    intro i hi b
    have hn := (hψ i hi).1
    have hpos : 0 < (ψ i i).natAbs := Int.natAbs_pos.mpr hn
    obtain ⟨h1, h2⟩ := hunitOut i hi
    cases b
    · rw [← huinv]
      refine IsIntegral.of_pow hpos ?_
      rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, inv_zpow']
      rcases Int.natAbs_eq (ψ i i) with h | h
      · rw [← h]; exact h2
      · rw [show -((ψ i i).natAbs : ℤ) = ψ i i by omega]; exact h1
    · rw [← hu]
      refine IsIntegral.of_pow hpos ?_
      rw [← Units.val_pow_eq_pow_val, ← zpow_natCast]
      rcases Int.natAbs_eq (ψ i i) with h | h
      · rw [← h]; exact h1
      · rw [show ((ψ i i).natAbs : ℤ) = -ψ i i by omega]; exact h2
  -- `X_h`, `h ∉ H`
  have hXout : ∀ h ∉ H, IsIntegral P (mk (X (Sum.inl h))) := by
    intro h hh
    have hin : linForm (A₁ := A₁) (ℓ h) ∈ 𝔞 :=
      Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨h, rfl⟩))
    have h0 := hmem _ hin
    rw [linForm, map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ h), map_mul, algHom_C,
      (hℓ h hh).1, map_one, one_mul, add_eq_zero_iff_eq_neg] at h0
    rw [h0]
    refine IsIntegral.neg ((integralClosure P S).sum_mem fun h' hh' => ?_)
    rw [map_mul, algHom_C]
    by_cases h'H : h' ∈ H
    · exact (hconst _).mul (hXH h' h'H)
    · rw [(hℓ h hh).2 h' h'H (Finset.ne_of_mem_erase hh'), map_zero, zero_mul]
      exact isIntegral_zero
  have hall : ∀ f : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K, IsIntegral P (mk f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C c => rw [algHom_C]; exact hconst c
    | add p q hp hq => rw [map_add]; exact hp.add hq
    | mul_X p v hp =>
      rw [map_mul]
      refine hp.mul ?_
      rcases v with h | ⟨i, b⟩
      · by_cases hh : h ∈ H
        · exact hXH h hh
        · exact hXout h hh
      · by_cases hi : i ∈ J
        · exact hroot i hi b
        · exact hOut i hi b
  have : Algebra.IsIntegral P S := ⟨fun x => by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact hall f⟩
  calc ringKrullDim S ≤ ringKrullDim P := ringKrullDim_le_of_isIntegral
    _ = _ := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
        Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]
