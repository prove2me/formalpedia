-- Prove2me | solution 1 for DiazModulus.quadratic_ratio_progression_space_eq_involution_pencil_space
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T19:27:34.687424+00:00
-- url     : https://prove2.me/submissions/3a820b7e-666f-4a4a-aa30-de6d5c0ebd68

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A quadratic-ratio progression space of dimension 5 is an involution-pencil space

Put `h = p(u)/q(u)`; `h ∉ Q̄` (else `p = t q`, impossible for coprime `p, q` of degree 2), so `h` is
transcendental. `H = ⟨1, u, u⁻¹⟩` and `P = ⟨c hᵏ⟩` have dimensions 3 and 4, so `dim (H ⊓ P) ≥ 2`
(Grassmann) and two independent elements give `c u φᵢ(h) = Rᵢ(u)` with `φᵢ ∈ Q̄[T]≤3` independent and
`Rᵢ ∈ Q̄[X]≤2`. Write `φᵢ = g ψᵢ` with `ψ₁, ψ₂` coprime (`extract_gcd`) and `m = max deg ψᵢ ≥ 1`. The
binary forms `Ψᵢ = Σ ψᵢⱼ pʲ qᵐ⁻ʲ` satisfy `Ψ₁ R₂ = Ψ₂ R₁`; they have no common zero in `ℂ` (since `p, q`
have none), so they are coprime and `Rᵢ = Ψᵢ ρ`. Their `X²ᵐ`-coefficients are the forms at
`(p₂, q₂) ≠ 0`, so one `Ψᵢ` has degree `2m ≤ 2`: `m = 1`, `ρ = κ ∈ Q̄*`, and `c u g(h) = κ q(u)` with
`deg g ≤ 2`. Factoring `g = (a₁T + b₁)(a₂T + b₂)` over `Q̄` (roots via `ℂ`) gives pencil members
`lᵢ = aᵢ p + bᵢ q` with `c = κ q(u)³ / (u l₁(u) l₂(u))`, i.e. `c hᵏ = κ pᵏ q³⁻ᵏ / (u l₁ l₂)`, and the
two spans agree. -/

namespace R13_pencil

open DiazModulus Polynomial

theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) :
    P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem exists_root {p : (↥Qbar)[X]} (hp : 0 < p.natDegree) : ∃ b : ↥Qbar, p.IsRoot b := by
  have hp0 : p ≠ 0 := ne_zero_of_natDegree_gt hp
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero_of_injective (k := ℂ)
    (R := ↥Qbar) Subtype.val_injective p (by
      rw [degree_eq_natDegree hp0]; exact_mod_cast hp.ne')
  by_cases hzq : z ∈ Qbar
  · refine ⟨⟨z, hzq⟩, ?_⟩
    have : aeval (algebraMap (↥Qbar) ℂ ⟨z, hzq⟩) p = 0 := hz
    rw [aeval_algebraMap_apply, coe_aeval_eq_eval] at this
    exact Subtype.val_injective (by simpa using this)
  · exact absurd (aeval_eq_zero hzq hz) hp0

theorem cubic_zero {u : ℂ} (hu : u ∉ Qbar) (a₀ a₁ a₂ a₃ : ↥Qbar)
    (h : (a₀ : ℂ) + a₁ * u + a₂ * u ^ 2 + a₃ * u ^ 3 = 0) :
    a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 := by
  have hP := aeval_eq_zero hu (P := C a₀ + C a₁ * X + C a₂ * X ^ 2 + C a₃ * X ^ 3)
    (by simpa [am] using h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using congrArg (coeff · 0) hP
  · simpa using congrArg (coeff · 1) hP
  · simpa using congrArg (coeff · 2) hP
  · simpa using congrArg (coeff · 3) hP

/-- The binary form `Σ φⱼ pʲ qᵐ⁻ʲ` attached to `φ` of virtual degree `m`. -/
noncomputable def hom (p q : (↥Qbar)[X]) (m : ℕ) (φ : (↥Qbar)[X]) : (↥Qbar)[X] :=
  ∑ j ∈ Finset.range (m + 1), C (φ.coeff j) * p ^ j * q ^ (m - j)

/-- The same binary form evaluated at a point `(a, b)` of `ℂ²`. -/
noncomputable def bf (m : ℕ) (φ : (↥Qbar)[X]) (a b : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (m + 1), (φ.coeff j : ℂ) * a ^ j * b ^ (m - j)

theorem aeval_hom (p q φ : (↥Qbar)[X]) (m : ℕ) (z : ℂ) :
    aeval z (hom p q m φ) = bf m φ (aeval z p) (aeval z q) := by
  simp [hom, bf, map_sum, am]

theorem coeff_hom {p q : (↥Qbar)[X]} (hp : p.natDegree ≤ 2) (hq : q.natDegree ≤ 2) (m : ℕ)
    (φ : (↥Qbar)[X]) : ((hom p q m φ).coeff (2 * m) : ℂ) = bf m φ (p.coeff 2) (q.coeff 2) := by
  simp only [hom, bf, finsetSum_coeff]
  push_cast
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj : j ≤ m := by simpa [Nat.lt_succ_iff] using hj
  rw [mul_assoc, coeff_C_mul, show 2 * m = j * 2 + (m - j) * 2 by omega,
    coeff_mul_add_eq_of_natDegree_le (natDegree_pow_le_of_le _ hp) (natDegree_pow_le_of_le _ hq),
    coeff_pow_of_natDegree_le hp, coeff_pow_of_natDegree_le hq]
  push_cast; ring

theorem bf_of_ne {m : ℕ} {φ : (↥Qbar)[X]} (hφ : φ.natDegree ≤ m) {a b : ℂ} (hb : b ≠ 0) :
    bf m φ a b = b ^ m * aeval (a / b) φ := by
  rw [aeval_eq_sum_range' (n := m + 1) (by omega), bf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj : j ≤ m := by simpa [Nat.lt_succ_iff] using hj
  have e : b ^ m = b ^ (m - j) * b ^ j := by rw [← pow_add, Nat.sub_add_cancel hj]
  rw [e, Algebra.smul_def, am, div_pow]
  field_simp

theorem bf_zero (m : ℕ) (φ : (↥Qbar)[X]) (a : ℂ) : bf m φ a 0 = φ.coeff m * a ^ m := by
  rw [bf, Finset.sum_range_succ, Finset.sum_eq_zero]
  · simp
  intro j hj
  have : m - j ≠ 0 := by simp at hj; omega
  simp [zero_pow this]

/-- Two coprime forms of virtual degree `m` (one of exact degree `m`) have no common zero. -/
theorem bf_ne {ψ₁ ψ₂ : (↥Qbar)[X]} (hc : IsCoprime ψ₁ ψ₂) {m : ℕ} (h1 : ψ₁.natDegree ≤ m)
    (h2 : ψ₂.natDegree ≤ m) (hl : ψ₁.coeff m ≠ 0 ∨ ψ₂.coeff m ≠ 0) {a b : ℂ}
    (hab : a ≠ 0 ∨ b ≠ 0) : bf m ψ₁ a b ≠ 0 ∨ bf m ψ₂ a b ≠ 0 := by
  by_cases hb : b = 0
  · subst hb
    have ha : a ≠ 0 := hab.resolve_right (by simp)
    rw [bf_zero, bf_zero]
    rcases hl with h | h
    · exact Or.inl (mul_ne_zero (by exact_mod_cast h) (pow_ne_zero _ ha))
    · exact Or.inr (mul_ne_zero (by exact_mod_cast h) (pow_ne_zero _ ha))
  · rw [bf_of_ne h1 hb, bf_of_ne h2 hb]
    rcases aeval_ne_zero_of_isCoprime hc (a / b) with h | h
    · exact Or.inl (mul_ne_zero (pow_ne_zero _ hb) h)
    · exact Or.inr (mul_ne_zero (pow_ne_zero _ hb) h)

theorem hom_coprime {p q : (↥Qbar)[X]} (hpq : IsCoprime p q) {ψ₁ ψ₂ : (↥Qbar)[X]}
    (hc : IsCoprime ψ₁ ψ₂) {m : ℕ} (h1 : ψ₁.natDegree ≤ m) (h2 : ψ₂.natDegree ≤ m)
    (hl : ψ₁.coeff m ≠ 0 ∨ ψ₂.coeff m ≠ 0) : IsCoprime (hom p q m ψ₁) (hom p q m ψ₂) := by
  refine (isCoprime_iff_aeval_ne_zero_of_isAlgClosed (↥Qbar) ℂ _ _).2 fun z => ?_
  rw [aeval_hom, aeval_hom]
  exact bf_ne hc h1 h2 hl (aeval_ne_zero_of_isCoprime hpq z)

theorem h_not_mem {u : ℂ} (hu : u ∉ Qbar) {p q : (↥Qbar)[X]} (hpq : IsCoprime p q)
    (hdeg : 1 ≤ max p.natDegree q.natDegree) (hq : aeval u q ≠ 0) :
    aeval u p / aeval u q ∉ Qbar := by
  intro ht
  have e : p = C (⟨_, ht⟩ : ↥Qbar) * q := by
    apply sub_eq_zero.1; apply aeval_eq_zero hu
    simp only [map_sub, map_mul, aeval_C, am]
    field_simp; ring
  rw [e] at hpq hdeg
  have hU : IsUnit q := isCoprime_self.1 (IsCoprime.mul_left_iff.1 hpq).2
  have h0 := natDegree_eq_zero_of_isUnit hU
  have h1 := natDegree_C_mul_le (⟨_, ht⟩ : ↥Qbar) q
  omega

theorem pencil_ne {u : ℂ} {p q : (↥Qbar)[X]} (hq : aeval u q ≠ 0)
    (hh : aeval u p / aeval u q ∉ Qbar) {a b : ↥Qbar} (hab : a ≠ 0 ∨ b ≠ 0) :
    C a * p + C b * q ≠ 0 := by
  intro e
  have e' := congrArg (aeval u) e
  simp only [map_add, map_mul, aeval_C, am, map_zero] at e'
  have hP := aeval_eq_zero hh (P := C a * X + C b) (by
    simp only [map_add, map_mul, aeval_C, am, aeval_X]
    field_simp; linear_combination e')
  have ha := congrArg (coeff · 1) hP
  have hb := congrArg (coeff · 0) hP
  simp at ha hb
  rcases hab with h | h <;> contradiction

theorem aeval_pencil (u : ℂ) (p q : (↥Qbar)[X]) (hq : aeval u q ≠ 0) (a b : ↥Qbar) :
    aeval u (C a * p + C b * q) = aeval u q * (a * (aeval u p / aeval u q) + b) := by
  simp only [map_add, map_mul, aeval_C, am]
  field_simp

theorem factor2 {g : (↥Qbar)[X]} (hg : g ≠ 0) (hg2 : g.natDegree ≤ 2) (z : ℂ) :
    ∃ a₁ b₁ a₂ b₂ : ↥Qbar, (a₁ ≠ 0 ∨ b₁ ≠ 0) ∧ (a₂ ≠ 0 ∨ b₂ ≠ 0) ∧
      aeval z g = (a₁ * z + b₁) * (a₂ * z + b₂) := by
  have lin : ∀ e : (↥Qbar)[X], e ≠ 0 → e.natDegree ≤ 1 →
      (e.coeff 1 ≠ 0 ∨ e.coeff 0 ≠ 0) ∧ aeval z e = e.coeff 1 * z + e.coeff 0 := by
    intro e he he1
    constructor
    · by_contra hc
      push Not at hc
      apply he
      rw [eq_X_add_C_of_natDegree_le_one he1, hc.1, hc.2]
      simp
    · conv_lhs => rw [eq_X_add_C_of_natDegree_le_one he1]
      simp [am]
  by_cases h1 : g.natDegree ≤ 1
  · obtain ⟨hn, he⟩ := lin g hg h1
    exact ⟨0, 1, g.coeff 1, g.coeff 0, by simp, hn, by rw [he]; simp⟩
  · obtain ⟨t, ht⟩ := exists_root (p := g) (by omega)
    have hpp : (X - C t) * (g /ₘ (X - C t)) = g := mul_divByMonic_eq_iff_isRoot.2 ht
    have he0 : g /ₘ (X - C t) ≠ 0 := by
      intro e; rw [e, mul_zero] at hpp; exact hg hpp.symm
    have hed : (g /ₘ (X - C t)).natDegree ≤ 1 := by
      rw [natDegree_divByMonic _ (monic_X_sub_C t), natDegree_X_sub_C]; omega
    generalize g /ₘ (X - C t) = E at hpp he0 hed
    obtain ⟨hn, he⟩ := lin _ he0 hed
    refine ⟨1, -t, _, _, by simp, hn, ?_⟩
    rw [← hpp, map_mul, he]
    simp only [map_sub, aeval_X, aeval_C, am]
    push_cast
    ring

/-- Core: two independent relations `ν φᵢ(h) = Rᵢ(u)` force `ν g(h) = κ q(u)` with `deg g ≤ 2`. -/
theorem core {u : ℂ} (hu : u ∉ Qbar) {p q : (↥Qbar)[X]} (hpq : IsCoprime p q)
    (hp2 : p.natDegree ≤ 2) (hq2 : q.natDegree ≤ 2) (h2 : p.coeff 2 ≠ 0 ∨ q.coeff 2 ≠ 0)
    (hq : aeval u q ≠ 0) (hh : aeval u p / aeval u q ∉ Qbar) (ν : ℂ)
    {φ₁ φ₂ R₁ R₂ : (↥Qbar)[X]} (hφ1 : φ₁.natDegree ≤ 3) (hφ2 : φ₂.natDegree ≤ 3)
    (h10 : φ₁ ≠ 0) (hind : ∀ l : ↥Qbar, φ₂ ≠ C l * φ₁)
    (hR1 : R₁.natDegree ≤ 2) (hR2 : R₂.natDegree ≤ 2) (hR10 : R₁ ≠ 0)
    (e1 : ν * aeval (aeval u p / aeval u q) φ₁ = aeval u R₁)
    (e2 : ν * aeval (aeval u p / aeval u q) φ₂ = aeval u R₂) :
    ∃ g : (↥Qbar)[X], g ≠ 0 ∧ g.natDegree ≤ 2 ∧ ∃ κ : ↥Qbar, κ ≠ 0 ∧
      ν * aeval (aeval u p / aeval u q) g = κ * aeval u q := by
  set h := aeval u p / aeval u q with hhdef
  have hev : ∀ f : (↥Qbar)[X], f ≠ 0 → aeval h f ≠ 0 := fun f hf e => hf (aeval_eq_zero hh e)
  obtain ⟨ψ₁, ψ₂, hd1, hd2, hU⟩ := extract_gcd φ₁ φ₂
  generalize gcd φ₁ φ₂ = g at hd1 hd2
  have hcop : IsCoprime ψ₁ ψ₂ := isRelPrime_iff_isCoprime.1 (gcd_isUnit_iff_isRelPrime.1 hU)
  have hφ20 : φ₂ ≠ 0 := fun e => hind 0 (by simp [e])
  have hg0 : g ≠ 0 := fun e => h10 (by rw [hd1, e, zero_mul])
  have hψ10 : ψ₁ ≠ 0 := fun e => h10 (by rw [hd1, e, mul_zero])
  have hψ20 : ψ₂ ≠ 0 := fun e => hφ20 (by rw [hd2, e, mul_zero])
  have hdg1 : g.natDegree + ψ₁.natDegree ≤ 3 := by rw [← natDegree_mul hg0 hψ10, ← hd1]; exact hφ1
  have hdg2 : g.natDegree + ψ₂.natDegree ≤ 3 := by rw [← natDegree_mul hg0 hψ20, ← hd2]; exact hφ2
  set m := max ψ₁.natDegree ψ₂.natDegree with hm
  have hm1 := le_max_left ψ₁.natDegree ψ₂.natDegree
  have hm2 := le_max_right ψ₁.natDegree ψ₂.natDegree
  have hl : ψ₁.coeff m ≠ 0 ∨ ψ₂.coeff m ≠ 0 := by
    rcases max_choice ψ₁.natDegree ψ₂.natDegree with e | e
    · left; rw [← hm] at e; rw [e]; exact mt leadingCoeff_eq_zero.1 hψ10
    · right; rw [← hm] at e; rw [e]; exact mt leadingCoeff_eq_zero.1 hψ20
  have hmpos : 1 ≤ m := by
    by_contra hm0
    have z1 : ψ₁.natDegree = 0 := by omega
    have z2 : ψ₂.natDegree = 0 := by omega
    rw [eq_C_of_natDegree_eq_zero z1] at hd1 hψ10
    rw [eq_C_of_natDegree_eq_zero z2] at hd2
    have c10 : ψ₁.coeff 0 ≠ 0 := fun e => hψ10 (by rw [e, map_zero])
    apply hind (ψ₂.coeff 0 / ψ₁.coeff 0)
    rw [hd1, hd2, mul_left_comm, ← C_mul, div_mul_cancel₀ _ c10]
  -- the relation between the two forms
  have e1' : ν * (aeval h g * aeval h ψ₁) = aeval u R₁ := by rw [← e1, hd1, map_mul]
  have e2' : ν * (aeval h g * aeval h ψ₂) = aeval u R₂ := by rw [← e2, hd2, map_mul]
  have hν : ν ≠ 0 := by
    intro e; rw [e, zero_mul] at e1'; exact hR10 (aeval_eq_zero hu e1'.symm)
  have key : aeval h ψ₁ * aeval u R₂ = aeval h ψ₂ * aeval u R₁ := by
    have : ν * aeval h g * (aeval h ψ₁ * aeval u R₂ - aeval h ψ₂ * aeval u R₁) = 0 := by
      rw [← e1', ← e2']; ring
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (mul_ne_zero hν (hev g hg0)))
  have hevu : ∀ ψ : (↥Qbar)[X], ψ.natDegree ≤ m → aeval u (hom p q m ψ) = aeval u q ^ m * aeval h ψ :=
    fun ψ hψ => by rw [aeval_hom, bf_of_ne hψ hq]
  have hpoly : hom p q m ψ₁ * R₂ = hom p q m ψ₂ * R₁ := by
    apply sub_eq_zero.1; apply aeval_eq_zero hu
    rw [map_sub, map_mul, map_mul, hevu ψ₁ hm1, hevu ψ₂ hm2]
    linear_combination (aeval u q ^ m) * key
  have hc := hom_coprime hpq hcop hm1 hm2 hl
  obtain ⟨ρ, hρ⟩ : hom p q m ψ₁ ∣ R₁ := hc.dvd_of_dvd_mul_left ⟨R₂, by linear_combination -hpoly⟩
  have hH10 : hom p q m ψ₁ ≠ 0 := fun e => hR10 (by rw [hρ, e, zero_mul])
  have hρ0 : ρ ≠ 0 := fun e => hR10 (by rw [hρ, e, mul_zero])
  have hρ2 : R₂ = hom p q m ψ₂ * ρ := mul_left_cancel₀ hH10 (by rw [hpoly, hρ]; ring)
  have hdeg : ∀ ψ R : (↥Qbar)[X], R = hom p q m ψ * ρ → R.natDegree ≤ 2 →
      (hom p q m ψ).coeff (2 * m) ≠ 0 → m ≤ 1 ∧ ρ.natDegree = 0 := by
    intro ψ R hR hR2 hc0
    have hH0 : hom p q m ψ ≠ 0 := fun e => hc0 (by rw [e, coeff_zero])
    have := le_natDegree_of_ne_zero hc0
    rw [hR, natDegree_mul hH0 hρ0] at hR2
    omega
  have hpq2 : (p.coeff 2 : ℂ) ≠ 0 ∨ (q.coeff 2 : ℂ) ≠ 0 := by
    rcases h2 with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  have hb : m ≤ 1 ∧ ρ.natDegree = 0 := by
    rcases bf_ne hcop hm1 hm2 hl hpq2 with h | h
    · exact hdeg ψ₁ R₁ hρ hR1 (fun e => h (by rw [← coeff_hom hp2 hq2, e]; rfl))
    · exact hdeg ψ₂ R₂ hρ2 hR2 (fun e => h (by rw [← coeff_hom hp2 hq2, e]; rfl))
  have hm' : m = 1 := by omega
  refine ⟨g, hg0, by omega, ρ.coeff 0, fun e => hρ0 ?_, ?_⟩
  · rw [eq_C_of_natDegree_eq_zero hb.2, e, map_zero]
  · have e3 := e1'
    rw [hρ, map_mul, hevu ψ₁ hm1, eq_C_of_natDegree_eq_zero hb.2, aeval_C, am, hm', pow_one] at e3
    apply mul_right_cancel₀ (hev ψ₁ hψ10)
    linear_combination e3

end R13_pencil

open DiazModulus R13_pencil Polynomial in
theorem solution
    (u : ℂ) (hu : u ∉ Qbar) (p q : Polynomial ↥Qbar) (hcop : IsCoprime p q)
    (hdeg : max p.natDegree q.natDegree = 2) (c : ℂ) (hc : c ≠ 0)
    (hdim : Module.finrank (↥Qbar) (Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪
      Set.range (fun k : Fin 4 => c * (Polynomial.aeval u p / Polynomial.aeval u q) ^ (k : ℕ)))) = 5) :
    ∃ l₁ l₂ : Polynomial ↥Qbar,
      l₁ ∈ Submodule.span ↥Qbar ({p, q} : Set (Polynomial ↥Qbar)) ∧ l₁ ≠ 0 ∧
      l₂ ∈ Submodule.span ↥Qbar ({p, q} : Set (Polynomial ↥Qbar)) ∧ l₂ ≠ 0 ∧
      Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪
      Set.range (fun k : Fin 4 => c * (Polynomial.aeval u p / Polynomial.aeval u q) ^ (k : ℕ))) =
        Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪ Set.range (fun i : Fin 4 =>
          Polynomial.aeval u p ^ (i : ℕ) * Polynomial.aeval u q ^ (3 - (i : ℕ)) /
            (u * Polynomial.aeval u l₁ * Polynomial.aeval u l₂))) := by
  have hu0 : u ≠ 0 := fun e => hu (e ▸ zero_mem _)
  have hp2 : p.natDegree ≤ 2 := by have := le_max_left p.natDegree q.natDegree; omega
  have hq2 : q.natDegree ≤ 2 := by have := le_max_right p.natDegree q.natDegree; omega
  have h2 : p.coeff 2 ≠ 0 ∨ q.coeff 2 ≠ 0 := by
    rcases max_choice p.natDegree q.natDegree with e | e <;> rw [e] at hdeg
    · left; intro h0
      have : p.leadingCoeff = 0 := by rw [leadingCoeff, hdeg, h0]
      rw [leadingCoeff_eq_zero.1 this, natDegree_zero] at hdeg; omega
    · right; intro h0
      have : q.leadingCoeff = 0 := by rw [leadingCoeff, hdeg, h0]
      rw [leadingCoeff_eq_zero.1 this, natDegree_zero] at hdeg; omega
  have hq0 : q ≠ 0 := by
    intro e
    rw [e] at hcop hdeg
    have := natDegree_eq_zero_of_isUnit (isCoprime_zero_right.1 hcop)
    rw [natDegree_zero, max_eq_left (Nat.zero_le _)] at hdeg; omega
  have hqu : aeval u q ≠ 0 := fun e => hq0 (aeval_eq_zero hu e)
  have hh := h_not_mem hu hcop (by omega) hqu
  set h := aeval u p / aeval u q with hhdef
  set W := Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪
    Set.range (fun k : Fin 4 => c * h ^ (k : ℕ))) with hW
  have h1 : (1 : ℂ) ∈ W := Submodule.subset_span (Or.inl (by simp))
  have hu1 : u ∈ W := Submodule.subset_span (Or.inl (by simp))
  have hui : u⁻¹ ∈ W := Submodule.subset_span (Or.inl (by simp))
  -- `H = ⟨1, u, u⁻¹⟩`, `P = ⟨c hᵏ⟩`, `dim (H ⊓ P) ≥ 2`
  set H := Submodule.span (↥Qbar) (Set.range ![(1 : ℂ), u, u⁻¹]) with hH
  set P := Submodule.span (↥Qbar) (Set.range (fun k : Fin 4 => c * h ^ (k : ℕ))) with hP
  have hHli : LinearIndependent (↥Qbar) ![(1 : ℂ), u, u⁻¹] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Subfield.smul_def, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, smul_eq_mul, Matrix.tail_cons] at hg
    have := cubic_zero hu (g 2) (g 0) (g 1) 0 (by
      have hu' : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0
      push_cast
      linear_combination u * hg - (g 2 : ℂ) * hu')
    intro i; fin_cases i
    exacts [this.2.1, this.2.2.1, this.1]
  have hPli : LinearIndependent (↥Qbar) (fun k : Fin 4 => c * h ^ (k : ℕ)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_four, Subfield.smul_def, smul_eq_mul,
      show ((0 : Fin 4) : ℕ) = 0 from rfl, show ((1 : Fin 4) : ℕ) = 1 from rfl,
      show ((2 : Fin 4) : ℕ) = 2 from rfl, show ((3 : Fin 4) : ℕ) = 3 from rfl] at hg
    have := cubic_zero hh (g 0) (g 1) (g 2) (g 3) (by
      have : c * ((g 0 : ℂ) + g 1 * h + g 2 * h ^ 2 + g 3 * h ^ 3) = 0 := by
        linear_combination hg
      exact (mul_eq_zero.1 this).resolve_left hc)
    intro i; fin_cases i
    exacts [this.1, this.2.1, this.2.2.1, this.2.2.2]
  have : FiniteDimensional (↥Qbar) H := FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have : FiniteDimensional (↥Qbar) P := FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have : FiniteDimensional (↥Qbar) W :=
    FiniteDimensional.span_of_finite _ ((Set.toFinite _).union (Set.finite_range _))
  have hfH : Module.finrank (↥Qbar) H = 3 := by rw [hH, finrank_span_eq_card hHli]; simp
  have hfP : Module.finrank (↥Qbar) P = 4 := by rw [hP, finrank_span_eq_card hPli]; simp
  have hle : H ⊔ P ≤ W := by
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      exacts [h1, hu1, hui]
    · rintro _ ⟨j, rfl⟩
      exact Submodule.subset_span (Or.inr ⟨j, rfl⟩)
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq H P
  have hmono := Submodule.finrank_mono hle
  rw [hdim] at hmono
  have hI : 2 ≤ Module.finrank (↥Qbar) ↥(H ⊓ P) := by omega
  have hne : H ⊓ P ≠ ⊥ := by intro e; rw [e, finrank_bot] at hI; omega
  obtain ⟨x₁, hx₁, hx₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hlt : (↥Qbar) ∙ x₁ < H ⊓ P := Submodule.lt_of_le_of_finrank_lt_finrank
    ((Submodule.span_singleton_le_iff_mem _ _).2 hx₁) (by rw [finrank_span_singleton hx₁0]; omega)
  obtain ⟨x₂, hx₂, hx₂n⟩ := SetLike.exists_of_lt hlt
  have hx₂0 : x₂ ≠ 0 := fun e => hx₂n (e ▸ zero_mem _)
  -- each `x ∈ H ⊓ P` gives a relation `c u φ(h) = R(u)`
  have extract : ∀ x ∈ H ⊓ P, x ≠ 0 → ∃ φ R : (↥Qbar)[X], φ.natDegree ≤ 3 ∧ R.natDegree ≤ 2 ∧
      R ≠ 0 ∧ x = c * aeval h φ ∧ c * u * aeval h φ = aeval u R := by
    intro x hx hx0
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (↥Qbar)).1 (Submodule.mem_inf.1 hx).1
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun (↥Qbar)).1 (Submodule.mem_inf.1 hx).2
    simp only [Fin.sum_univ_three, Subfield.smul_def, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, smul_eq_mul, Matrix.tail_cons] at ha
    simp only [Fin.sum_univ_four, Subfield.smul_def, smul_eq_mul,
      show ((0 : Fin 4) : ℕ) = 0 from rfl, show ((1 : Fin 4) : ℕ) = 1 from rfl,
      show ((2 : Fin 4) : ℕ) = 2 from rfl, show ((3 : Fin 4) : ℕ) = 3 from rfl] at hb
    have hx' : x = c * aeval h (C (b 0) + C (b 1) * X + C (b 2) * X ^ 2 + C (b 3) * X ^ 3) := by
      simp only [map_add, map_mul, aeval_C, am, map_pow, aeval_X]
      linear_combination -hb
    have hR : aeval u (C (a 2) + C (a 0) * X + C (a 1) * X ^ 2) = u * x := by
      simp only [map_add, map_mul, aeval_C, am, map_pow, aeval_X]
      rw [← ha]; field_simp; ring
    refine ⟨C (b 0) + C (b 1) * X + C (b 2) * X ^ 2 + C (b 3) * X ^ 3,
      C (a 2) + C (a 0) * X + C (a 1) * X ^ 2, by compute_degree!, by compute_degree!,
      fun e => ?_, hx', ?_⟩
    · rw [e, map_zero] at hR; exact hx0 ((mul_eq_zero.1 hR.symm).resolve_left hu0)
    · rw [hR, hx']; ring
  obtain ⟨φ₁, R₁, hφ1, hR1, hR10, hx1, e1⟩ := extract x₁ hx₁ hx₁0
  obtain ⟨φ₂, R₂, hφ2, hR2, -, hx2, e2⟩ := extract x₂ hx₂ hx₂0
  have h10 : φ₁ ≠ 0 := fun e => hx₁0 (by rw [hx1, e, map_zero, mul_zero])
  have hind : ∀ l : ↥Qbar, φ₂ ≠ C l * φ₁ := by
    intro l e
    apply hx₂n
    rw [Submodule.mem_span_singleton]
    exact ⟨l, by rw [hx2, e, map_mul, aeval_C, am, hx1, Subfield.smul_def]; ring⟩
  obtain ⟨g, hg0, hg2, κ, hκ, hgκ⟩ :=
    core hu hcop hp2 hq2 h2 hqu hh (c * u) hφ1 hφ2 h10 hind hR1 hR2 hR10 e1 e2
  -- `g(h) = (a₁h + b₁)(a₂h + b₂)` and `lᵢ = aᵢ p + bᵢ q`
  obtain ⟨a₁, b₁, a₂, b₂, hab1, hab2, hfac⟩ := factor2 hg0 hg2 h
  have hl1 : aeval u (C a₁ * p + C b₁ * q) = aeval u q * (a₁ * h + b₁) :=
    aeval_pencil u p q hqu a₁ b₁
  have hl2 : aeval u (C a₂ * p + C b₂ * q) = aeval u q * (a₂ * h + b₂) :=
    aeval_pencil u p q hqu a₂ b₂
  have hn1 : aeval u (C a₁ * p + C b₁ * q) ≠ 0 := fun e => pencil_ne hqu hh hab1 (aeval_eq_zero hu e)
  have hn2 : aeval u (C a₂ * p + C b₂ * q) ≠ 0 := fun e => pencil_ne hqu hh hab2 (aeval_eq_zero hu e)
  refine ⟨C a₁ * p + C b₁ * q, C a₂ * p + C b₂ * q,
    Submodule.mem_span_pair.2 ⟨a₁, b₁, by simp [smul_eq_C_mul]⟩, pencil_ne hqu hh hab1,
    Submodule.mem_span_pair.2 ⟨a₂, b₂, by simp [smul_eq_C_mul]⟩, pencil_ne hqu hh hab2, ?_⟩
  have hcκ : c * u * ((a₁ * h + b₁) * (a₂ * h + b₂)) = κ * aeval u q := by rw [← hfac]; exact hgκ
  have hpu : aeval u p = h * aeval u q := by rw [hhdef]; field_simp
  have hgen : ∀ k : Fin 4, c * h ^ (k : ℕ) = (κ : ℂ) * (aeval u p ^ (k : ℕ) * aeval u q ^ (3 - (k : ℕ)) /
      (u * aeval u (C a₁ * p + C b₁ * q) * aeval u (C a₂ * p + C b₂ * q))) := by
    intro k
    have hk : (k : ℕ) ≤ 3 := by omega
    have e3 : aeval u q ^ (3 - (k : ℕ)) * aeval u q ^ (k : ℕ) = aeval u q ^ 3 := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    rw [mul_div_assoc', eq_div_iff (mul_ne_zero (mul_ne_zero hu0 hn1) hn2), hl1, hl2, hpu, mul_pow]
    linear_combination (h ^ (k : ℕ) * aeval u q ^ 2) * hcκ - (κ * h ^ (k : ℕ)) * e3
  have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro x (hx | ⟨k, rfl⟩)
    · exact Submodule.subset_span (Or.inl hx)
    · show c * h ^ (k : ℕ) ∈ _
      rw [hgen k]
      exact Submodule.smul_mem _ κ (Submodule.subset_span (Or.inr ⟨k, rfl⟩))
  · refine Submodule.span_le.2 ?_
    rintro x (hx | ⟨k, rfl⟩)
    · exact Submodule.subset_span (Or.inl hx)
    · show aeval u p ^ (k : ℕ) * aeval u q ^ (3 - (k : ℕ)) /
        (u * aeval u (C a₁ * p + C b₁ * q) * aeval u (C a₂ * p + C b₂ * q)) ∈ W
      have e : aeval u p ^ (k : ℕ) * aeval u q ^ (3 - (k : ℕ)) /
          (u * aeval u (C a₁ * p + C b₁ * q) * aeval u (C a₂ * p + C b₂ * q)) =
          (κ⁻¹ : ↥Qbar) * (c * h ^ (k : ℕ)) := by
        rw [hgen k]; push_cast; field_simp
      rw [e]
      exact Submodule.smul_mem _ κ⁻¹ (Submodule.subset_span (Or.inr ⟨k, rfl⟩))
