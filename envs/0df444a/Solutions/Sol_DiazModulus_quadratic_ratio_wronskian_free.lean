-- Prove2me | solution 1 for DiazModulus.quadratic_ratio_wronskian_free
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T07:34:28.427769+00:00
-- url     : https://prove2.me/submissions/e82c8160-e565-4bcf-adb4-0de9e7bb298f

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_quadratic_pencil_wronskian_identities
import Theorems.Thm_DiazModulus_quadratic_pencil_resultant_ne_zero

open Complex ComplexConjugate

/-! # `1` and `w = J(u)/q(u)` are free over `Q̄(h)`

Let `h = p(u)/q(u)` with `p, q ∈ Q̄[X]` coprime, `max(deg p, deg q) = 2`, `u ∉ Q̄`, and let
`w = J(u)/q(u)` with `J = p′q − pq′`. Then `q ≠ 0`, `q(u) ≠ 0`, and `h ∉ Q̄` (else `p = c·q`, and
coprimality makes both constant), so `h` is transcendental over `Q̄`. Dividing the second identity
of `quadratic_pencil_wronskian_identities` by `q(u)²` gives `w² = Δ(h)`, with
`Δ = d₂X² + d₁X + d₀`. If `A(h) + B(h)w = 0`, then `A(h)² = B(h)²Δ(h)`, so `A² = B²Δ` in `Q̄[X]`.
If `B = 0` this gives `A = 0`. Otherwise `B² ∣ A²` gives `B ∣ A` (`pow_dvd_pow_iff_dvd`), so
`Δ = R²` with `deg R ≤ 1`. Comparing coefficients with `R = r₁X + r₀`, `d₁² − 4d₂d₀ = 0`; but this
is `16·Res`, which `quadratic_pencil_resultant_ne_zero` says is non-zero. ∎
-/

namespace R20_wfree

open DiazModulus Polynomial

theorem tr_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : Transcendental (↥Qbar) u := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact (Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1 fun h' => hu (mem_Qbar_iff.2 h')

/-- The ratio of a coprime quadratic pencil at a transcendental point is not algebraic. -/
theorem ratio_not_mem {u : ℂ} (hu : u ∉ Qbar) {p q : (↥Qbar)[X]} (hcop : IsCoprime p q)
    (hdeg : max p.natDegree q.natDegree = 2) (hqu : aeval u q ≠ 0) :
    aeval u p / aeval u q ∉ Qbar := by
  intro hmem
  have hpoly : p - C ⟨_, hmem⟩ * q = 0 := by
    apply transcendental_iff.1 (tr_of_not_mem hu)
    rw [map_sub, map_mul, aeval_C]
    change aeval u p - (aeval u p / aeval u q) * aeval u q = 0
    rw [div_mul_cancel₀ _ hqu, sub_self]
  have hp : p = C ⟨_, hmem⟩ * q := sub_eq_zero.1 hpoly
  have hu' : IsUnit q := isCoprime_self.1 (hp ▸ hcop).of_mul_left_right
  have h1 := natDegree_eq_zero_of_isUnit hu'
  have h2 : p.natDegree ≤ q.natDegree := hp ▸ natDegree_C_mul_le _ _
  omega

end R20_wfree

open DiazModulus R20_wfree Polynomial in
theorem solution (u : ℂ) (hu : u ∉ Qbar) (p q : (↥Qbar)[X])
    (hcop : IsCoprime p q) (hdeg : max p.natDegree q.natDegree = 2) (A B : (↥Qbar)[X])
    (hAB : aeval (aeval u p / aeval u q) A + aeval (aeval u p / aeval u q) B *
        (aeval u (derivative p * q - p * derivative q) / aeval u q) = 0) :
    A = 0 ∧ B = 0 := by
  have hp : p.natDegree ≤ 2 := hdeg ▸ le_max_left _ _
  have hq : q.natDegree ≤ 2 := hdeg ▸ le_max_right _ _
  obtain ⟨-, hJ2⟩ := DiazModulus.quadratic_pencil_wronskian_identities p q hp hq
  have hRes := DiazModulus.quadratic_pencil_resultant_ne_zero p q hcop hdeg
  set J := derivative p * q - p * derivative q with hJdef
  have hq0 : q ≠ 0 := by
    rintro rfl
    have := natDegree_eq_zero_of_isUnit (isCoprime_zero_right.1 hcop)
    simp [this] at hdeg
  have hqu : aeval u q ≠ 0 := fun h0 => hq0 (transcendental_iff.1 (tr_of_not_mem hu) q h0)
  have htr := tr_of_not_mem (ratio_not_mem hu hcop hdeg hqu)
  set h := aeval u p / aeval u q with hh
  set w := aeval u J / aeval u q with hw
  clear_value h w
  set Δ : (↥Qbar)[X] := C (q.coeff 1 ^ 2 - 4 * q.coeff 2 * q.coeff 0) * X ^ 2
      + C (4 * (p.coeff 2 * q.coeff 0 + p.coeff 0 * q.coeff 2) - 2 * p.coeff 1 * q.coeff 1) * X
      + C (p.coeff 1 ^ 2 - 4 * p.coeff 2 * p.coeff 0) with hΔdef
  have hΔ : aeval h Δ = w ^ 2 := by
    have e := congrArg (aeval u) hJ2
    simp only [map_pow, map_add, map_mul, aeval_C] at e
    have hP : aeval u p = h * aeval u q := by rw [hh, div_mul_cancel₀ _ hqu]
    rw [hP] at e
    simp only [hΔdef, map_add, map_mul, map_pow, aeval_C, aeval_X]
    rw [hw, div_pow, eq_div_iff (pow_ne_zero 2 hqu), e]
    ring
  have hpoly : aeval h (A ^ 2 - B ^ 2 * Δ) = 0 := by
    rw [map_sub, map_mul, map_pow, map_pow, hΔ]
    linear_combination (aeval h A - aeval h B * w) * hAB
  have hA2 : A ^ 2 = B ^ 2 * Δ := sub_eq_zero.1 (transcendental_iff.1 htr _ hpoly)
  by_cases hB : B = 0
  · subst hB
    simp at hA2
    exact ⟨hA2, rfl⟩
  exfalso
  obtain ⟨R, hR⟩ := (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd two_ne_zero).1 (Dvd.intro _ hA2.symm)
  have hRΔ : R ^ 2 = Δ := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hB)
    rw [← hA2, hR]; ring
  have hΔdeg : Δ.natDegree ≤ 2 := by
    rw [hΔdef]
    refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
    · exact (natDegree_C_mul_le _ _).trans (by simp)
    · exact (natDegree_C_mul_le _ _).trans (by simp)
    · exact (natDegree_C _).trans_le (Nat.zero_le _)
  have hRdeg : R.natDegree ≤ 1 := by
    have h1 := natDegree_pow R 2
    rw [hRΔ] at h1
    omega
  obtain ⟨r₁, r₀, hRe⟩ : ∃ r₁ r₀, R = C r₁ * X + C r₀ := ⟨_, _, eq_X_add_C_of_natDegree_le_one hRdeg⟩
  have hsq : (C r₁ * X + C r₀) ^ 2 = C (r₁ ^ 2) * X ^ 2 + C (2 * r₁ * r₀) * X + C (r₀ ^ 2) := by
    simp only [map_pow, map_mul, C_ofNat]; ring
  rw [hRe, hsq, hΔdef] at hRΔ
  have c0 := congrArg (coeff · 0) hRΔ
  have c1 := congrArg (coeff · 1) hRΔ
  have c2 := congrArg (coeff · 2) hRΔ
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at c0 c1 c2
  norm_num at c0 c1 c2
  apply hRes
  have h16 : (16 : ↥Qbar) * ((p.coeff 2 * q.coeff 0 - p.coeff 0 * q.coeff 2) ^ 2
      - (p.coeff 2 * q.coeff 1 - p.coeff 1 * q.coeff 2) * (p.coeff 1 * q.coeff 0 - p.coeff 0 * q.coeff 1))
      = 0 := by
    linear_combination (-(4 * (p.coeff 2 * q.coeff 0 + p.coeff 0 * q.coeff 2) - 2 * p.coeff 1 * q.coeff 1
      + 2 * r₁ * r₀)) * c1 + 4 * r₀ ^ 2 * c2 + 4 * (q.coeff 1 ^ 2 - 4 * q.coeff 2 * q.coeff 0) * c0
  exact (mul_eq_zero.1 h16).resolve_left (by norm_num)
