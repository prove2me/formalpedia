-- Prove2me | solution 1 for CollapsibleCubics.legendre_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-04T02:22:12.023975+00:00
-- url     : https://prove2.me/submissions/1785e52f-975a-40d4-8659-d8babb2f4cdd

import Mathlib

open Polynomial

/-- If a prime `p ∤ Δ` divides some norm `F(a_j,b_j)` of a collapsing, then `Δ` is a square
modulo `p`.  Elementary proof: reduce the identity `∏(b_i X - a_i) = m·h + c` modulo `p`; the
root `ρ = a_j/b_j` of `m` kills `c`, so the cofactor quadratic `g = X² + ρX + ρ² + d` divides
the product of linear forms; `g` is irreducible when `Δ ≡ (3ρ²+d)²(-3ρ²-4d)` is a non-residue,
and an irreducible quadratic divides no product of nonzero linear forms. -/
theorem solution (d e : ℤ)
    (hirr : Irreducible (X ^ 3 + C (d : ℚ) * X + C (e : ℚ) : ℚ[X]))
    (α : ℂ) (hα : α ^ 3 + (d : ℂ) * α + (e : ℂ) = 0)
    (n : ℕ) (a b : Fin n → ℤ) (hb : ∀ i, b i ≠ 0) (hab : ∀ i, IsCoprime (a i) (b i))
    (c : ℚ) (hprod : ∏ i, ((b i : ℂ) * α - (a i : ℂ)) = (c : ℂ))
    (p : ℕ) [Fact p.Prime] (hp : Odd p) (hpΔ : ¬ (p : ℤ) ∣ (-4 * d ^ 3 - 27 * e ^ 2))
    (j : Fin n) (hpF : (p : ℤ) ∣ a j ^ 3 + d * a j * b j ^ 2 + e * b j ^ 3) :
    legendreSym p (-4 * d ^ 3 - 27 * e ^ 2) = 1 := by
  classical
  have hpprime : p.Prime := Fact.out
  -- coprimality: p cannot divide both a i and b i
  have hcop : ∀ i, ¬ ((p : ℤ) ∣ a i ∧ (p : ℤ) ∣ b i) := by
    rintro i ⟨h1, h2⟩
    have hu := (hab i).isUnit_of_dvd' h1 h2
    rw [Int.isUnit_iff] at hu
    have := hpprime.two_le
    omega
  ------------------------------------------------------------------
  -- Step 1: the integer polynomial identity  fZ = C cZ + mZ * hZ
  ------------------------------------------------------------------
  set mZ : ℤ[X] := X ^ 3 + C d * X + C e with hmZ_def
  set fZ : ℤ[X] := ∏ i, (C (b i) * X - C (a i)) with hfZ_def
  have hmZ_monic : mZ.Monic := by
    rw [hmZ_def]; monicity!
  set φ : ℤ →+* ℚ := Int.castRingHom ℚ with hφ_def
  have hφinj : Function.Injective φ := φ.injective_int
  set mQ : ℚ[X] := X ^ 3 + C (d : ℚ) * X + C (e : ℚ) with hmQ_def
  have hmQ_map : mZ.map φ = mQ := by
    simp [hmZ_def, hmQ_def, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X, hφ_def]
  have hmQ_monic : mQ.Monic := by
    rw [hmQ_def]; monicity!
  have hmQ_deg : mQ.natDegree = 3 := by
    rw [hmQ_def]; compute_degree!
  have hmQ_aeval : aeval α mQ = 0 := by
    simp [hmQ_def, hα]
  have hminpoly : mQ = minpoly ℚ α := minpoly.eq_of_irreducible_of_monic hirr hmQ_aeval hmQ_monic
  set fQ : ℚ[X] := fZ.map φ with hfQ_def
  have hfQ_aeval : aeval α fQ = (c : ℂ) := by
    rw [← hprod, hfQ_def, hfZ_def, Polynomial.map_prod, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [hφ_def]
  have hdvd : mQ ∣ fQ - C c := by
    rw [hminpoly]
    apply minpoly.dvd
    simp [hfQ_aeval]
  obtain ⟨hQ, hhQ⟩ := hdvd
  have hmodQ : fQ %ₘ mQ = C c := by
    have := div_modByMonic_unique (f := fQ) (g := mQ) hQ (C c) hmQ_monic ⟨by rw [← hhQ]; ring, ?_⟩
    · exact this.2
    · calc degree (C c) ≤ 0 := degree_C_le
        _ < 3 := by norm_num
        _ = degree mQ := by rw [degree_eq_natDegree hmQ_monic.ne_zero, hmQ_deg]; rfl
  have hmodZ_map : (fZ %ₘ mZ).map φ = C c := by
    rw [map_modByMonic φ hmZ_monic, hmQ_map, ← hfQ_def, hmodQ]
  have hmodZ_deg : degree (fZ %ₘ mZ) ≤ 0 := by
    rw [← degree_map_eq_of_injective hφinj, hmodZ_map]
    exact degree_C_le
  set cZ : ℤ := (fZ %ₘ mZ).coeff 0 with hcZ_def
  have hmodZ : fZ %ₘ mZ = C cZ := eq_C_of_degree_le_zero hmodZ_deg
  have hidZ : fZ = C cZ + mZ * (fZ /ₘ mZ) := by
    rw [← hmodZ]; exact (modByMonic_add_div fZ mZ).symm
  ------------------------------------------------------------------
  -- Step 2: reduce modulo p
  ------------------------------------------------------------------
  set ψ : ℤ →+* ZMod p := Int.castRingHom (ZMod p) with hψ_def
  set fP : (ZMod p)[X] := ∏ i, (C (b i : ZMod p) * X - C (a i : ZMod p)) with hfP_def
  set mP : (ZMod p)[X] := X ^ 3 + C (d : ZMod p) * X + C (e : ZMod p) with hmP_def
  have hfP_map : fZ.map ψ = fP := by
    rw [hfZ_def, hfP_def, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [hψ_def]
  have hmP_map : mZ.map ψ = mP := by
    simp [hmZ_def, hmP_def, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X, hψ_def]
  have hidP : fP = C (cZ : ZMod p) + mP * (fZ /ₘ mZ).map ψ := by
    have := congrArg (Polynomial.map ψ) hidZ
    rw [hfP_map, Polynomial.map_add, Polynomial.map_mul, hmP_map, Polynomial.map_C] at this
    simpa [hψ_def] using this
  -- the root ρ = a_j / b_j of m modulo p
  have hbj : (b j : ZMod p) ≠ 0 := by
    intro h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    apply hcop j
    refine ⟨?_, h⟩
    have h3 : (p : ℤ) ∣ a j ^ 3 := by
      have hS : (p : ℤ) ∣ d * a j * b j ^ 2 + e * b j ^ 3 :=
        dvd_add (dvd_mul_of_dvd_right (dvd_pow h two_ne_zero) _)
          (dvd_mul_of_dvd_right (dvd_pow h three_ne_zero) _)
      have hsplit : a j ^ 3 = (a j ^ 3 + d * a j * b j ^ 2 + e * b j ^ 3)
          - (d * a j * b j ^ 2 + e * b j ^ 3) := by ring
      rw [hsplit]; exact dvd_sub hpF hS
    exact Int.Prime.dvd_pow' hpprime h3
  set ρ : ZMod p := (a j : ZMod p) * (b j : ZMod p)⁻¹ with hρ_def
  have hF : ((a j ^ 3 + d * a j * b j ^ 2 + e * b j ^ 3 : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hpF
  push_cast at hF
  have hroot : ρ ^ 3 + (d : ZMod p) * ρ + (e : ZMod p) = 0 := by
    have h1 : (ρ ^ 3 + (d : ZMod p) * ρ + (e : ZMod p)) * (b j : ZMod p) ^ 3 =
        (a j : ZMod p) ^ 3 + (d : ZMod p) * (a j : ZMod p) * (b j : ZMod p) ^ 2
          + (e : ZMod p) * (b j : ZMod p) ^ 3 := by
      rw [hρ_def]; field_simp
    rw [hF] at h1
    rcases mul_eq_zero.1 h1 with h | h
    · exact h
    · exact absurd (pow_eq_zero_iff three_ne_zero |>.1 h) hbj
  have hmP_eval : mP.eval ρ = 0 := by
    simp [hmP_def, hroot]
  have hfP_eval : fP.eval ρ = 0 := by
    rw [hfP_def, eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp only [eval_sub, eval_mul, eval_C, eval_X, hρ_def]
    rw [mul_comm (b j : ZMod p), mul_assoc, inv_mul_cancel₀ hbj, mul_one, sub_self]
  have hcP : (cZ : ZMod p) = 0 := by
    have := congrArg (eval ρ) hidP
    rw [hfP_eval, eval_add, eval_mul, hmP_eval, eval_C] at this
    simpa using this.symm
  have hmP_dvd : mP ∣ fP := by
    rw [hidP, hcP, map_zero, zero_add]
    exact dvd_mul_right _ _
  ------------------------------------------------------------------
  -- Step 3: the cofactor quadratic g and the discriminant
  ------------------------------------------------------------------
  set gP : (ZMod p)[X] := X ^ 2 + C ρ * X + C (ρ ^ 2 + (d : ZMod p)) with hgP_def
  have he : (e : ZMod p) = -ρ ^ 3 - (d : ZMod p) * ρ := by linear_combination hroot
  have hfactor : mP = (X - C ρ) * gP := by
    rw [hmP_def, hgP_def, he]
    simp only [map_sub, map_neg, map_pow, map_mul, map_add]
    ring
  have hgP_dvd : gP ∣ fP := (Dvd.intro_left _ hfactor.symm).trans hmP_dvd
  have hgP_deg : gP.natDegree = 2 := by
    rw [hgP_def]; compute_degree!
  have hgP_ne : gP ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hgP_deg; exact absurd hgP_deg (by norm_num)
  -- discriminant identity: Δ ≡ (3ρ²+d)² (-3ρ²-4d)
  set ρZ : ℤ := (ρ.cast : ℤ) with hρZ_def
  have hρZ : (ρZ : ZMod p) = ρ := ZMod.intCast_zmod_cast ρ
  have hΔ_cast : ((-4 * d ^ 3 - 27 * e ^ 2 : ℤ) : ZMod p) =
      (((3 * ρZ ^ 2 + d) ^ 2 * (-3 * ρZ ^ 2 - 4 * d) : ℤ) : ZMod p) := by
    push_cast
    rw [hρZ, he]
    ring
  set A : ℤ := 3 * ρZ ^ 2 + d with hA_def
  set δ : ℤ := -3 * ρZ ^ 2 - 4 * d with hδ_def
  have hΔ_ne : ((-4 * d ^ 3 - 27 * e ^ 2 : ℤ) : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hA_ne : (A : ZMod p) ≠ 0 := by
    intro h; apply hΔ_ne; rw [hΔ_cast]; push_cast; rw [h]; ring
  have hδ_ne : (δ : ZMod p) ≠ 0 := by
    intro h; apply hΔ_ne; rw [hΔ_cast]; push_cast; rw [h]; ring
  have hleg : legendreSym p (-4 * d ^ 3 - 27 * e ^ 2) = legendreSym p δ := by
    have h1 : legendreSym p (-4 * d ^ 3 - 27 * e ^ 2) = legendreSym p (A ^ 2 * δ) := by
      unfold legendreSym
      rw [hΔ_cast]
    rw [h1, legendreSym.mul, legendreSym.sq_one' p hA_ne, one_mul]
  rw [hleg]
  by_contra hne
  have hneg : legendreSym p δ = -1 := by
    rcases legendreSym.eq_one_or_neg_one (p := p) hδ_ne with h | h
    · exact absurd h hne
    · exact h
  have hnsq : ¬ IsSquare (δ : ZMod p) := (legendreSym.eq_neg_one_iff (p := p)).1 hneg
  -- g has no root modulo p
  have hnoroot : ∀ t : ZMod p, ¬ gP.IsRoot t := by
    intro t ht
    apply hnsq
    refine ⟨2 * t + ρ, ?_⟩
    have ht' : t ^ 2 + ρ * t + (ρ ^ 2 + (d : ZMod p)) = 0 := by
      simpa [hgP_def] using ht
    show ((-3 * ρZ ^ 2 - 4 * d : ℤ) : ZMod p) = (2 * t + ρ) * (2 * t + ρ)
    push_cast
    rw [hρZ]
    linear_combination (-4 : ZMod p) * ht'
  have hgP_irr : Irreducible gP := by
    rw [irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro t ht
    exact hnoroot t ((mem_roots hgP_ne).1 ht)
  have hgP_prime : Prime gP := hgP_irr.prime
  ------------------------------------------------------------------
  -- Step 4: an irreducible quadratic cannot divide a product of linear forms
  ------------------------------------------------------------------
  rw [hfP_def] at hgP_dvd
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hgP_prime _).1 hgP_dvd
  have hqi_ne : (C (b i : ZMod p) * X - C (a i : ZMod p) : (ZMod p)[X]) ≠ 0 := by
    intro h
    have h1 := congrArg (fun q : (ZMod p)[X] => q.coeff 1) h
    have h0 := congrArg (fun q : (ZMod p)[X] => q.coeff 0) h
    simp only [coeff_sub, coeff_C_mul, coeff_X_one, coeff_X_zero, coeff_C_zero, coeff_C, mul_one,
      mul_zero, one_ne_zero, if_false, sub_zero, zero_sub, neg_eq_zero, coeff_zero] at h1 h0
    apply hcop i
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h0, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h1⟩
  have hle := natDegree_le_of_dvd hi hqi_ne
  have hqi_deg : (C (b i : ZMod p) * X - C (a i : ZMod p) : (ZMod p)[X]).natDegree ≤ 1 := by
    compute_degree
  omega

