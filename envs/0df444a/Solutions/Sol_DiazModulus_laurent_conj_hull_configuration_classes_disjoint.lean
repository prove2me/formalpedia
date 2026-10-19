-- Prove2me | solution 1 for DiazModulus.laurent_conj_hull_configuration_classes_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T14:29:55.314005+00:00
-- url     : https://prove2.me/submissions/81c3b59d-63f0-4fea-adbe-4b8d3ee07bab

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The polynomial, involution and real pencil classes are pairwise disjoint

Let `u ∉ Q̄`, `s ∈ Q̄` with `s² = u ū`, and `W` any `Q̄`-subspace of `ℂ`. Then no two of the classes
(P) (`α u² + β u³ ∈ W`, `(α, β) ≠ 0`), (Q) (`W` is the involution normal form) and (R) (`W` is the
real pencil normal form) hold at once.

`s` is real, so `v = u/s` is transcendental with `v̄ = v⁻¹`, `u = s v` and `ū = s v⁻¹`; a relation
in `v` and `v⁻¹` with `Q̄` coefficients is cleared to a polynomial identity and compared
coefficientwise. (P)–(Q): writing `α u² + β u³` in the (Q) basis and multiplying by `v³` gives a
degree-6 identity whose coefficients at `1, v, v⁵, v⁶` force the `(Q)` coordinates and then `α, β`
to vanish. For (R), with `n = deg G ≥ 2`, put `H = Σ_{i ≤ n} Ḡ_i X^{n−i}`, so that
`H(v) = vⁿ · conj G(v)` and `H(0) = Ḡ_n ≠ 0`. Then `vⁿ⁺¹ g = vⁿ⁺¹ G(v) + κ H(v)` and
`vⁿ⁺¹ ḡ = v H(v) + κ̄ vⁿ⁺² G(v)`; evaluating the cleared identity at `0` kills the coordinate of
`g` (`xkill`), and after it, clearing by `vⁿ` kills the one of `ḡ` (`ykill`). (P)–(R): applied to
`α u² + β u³`, both coordinates vanish and `α = β = 0`. (Q)–(R): applied to `v̄² + e v²` and to its
conjugate, both vanish, and `v̄² + e v² ∈ span(1, v, v̄)` is false at `v⁰`. -/

namespace R18_ED

open DiazModulus Polynomial

theorem conj_mem_Qbar {a : ℂ} (ha : a ∈ Qbar) : conj a ∈ Qbar := by
  obtain ⟨p, hp0, hp⟩ := mem_Qbar_iff.1 ha
  refine mem_Qbar_iff.2 ⟨p, hp0, ?_⟩
  have : (conj a : ℂ) = ((Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ) a := rfl
  rw [this, Polynomial.aeval_algHom_apply, hp, map_zero]

/-- Conjugation on `Q̄`. -/
def cjQ (a : ↥Qbar) : ↥Qbar := ⟨conj (a : ℂ), conj_mem_Qbar a.2⟩

theorem cjQ_coe (a : ↥Qbar) : (cjQ a : ℂ) = conj (a : ℂ) := rfl

theorem cjQ_ne_zero {a : ↥Qbar} (ha : a ≠ 0) : cjQ a ≠ 0 := fun h =>
  ha (Subtype.ext ((map_eq_zero _).1 (congrArg Subtype.val h)))

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) : P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

/-- A polynomial relation of degree `6` over `Q̄` at `u ∉ Q̄` is trivial. -/
theorem seven_terms {u : ℂ} (hu : u ∉ Qbar) {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : ↥Qbar}
    (h : (a₀ : ℂ) + a₁ * u + a₂ * u ^ 2 + a₃ * u ^ 3 + a₄ * u ^ 4 + a₅ * u ^ 5 +
      a₆ * u ^ 6 = 0) :
    a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 ∧ a₄ = 0 ∧ a₅ = 0 ∧ a₆ = 0 := by
  have hP := aeval_eq_zero hu (P := C a₀ + C a₁ * X + C a₂ * X ^ 2 + C a₃ * X ^ 3 +
    C a₄ * X ^ 4 + C a₅ * X ^ 5 + C a₆ * X ^ 6)
    (by simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, am]; exact h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 0) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 1) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 2) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 3) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 4) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 5) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 6) hP

theorem coeffs {u z zc t w : ℂ} (hw : w ∈ Submodule.span Qbar ({1, u, t, z, zc} : Set ℂ)) :
    ∃ c₁ c₂ c₃ c₄ c₅ : ↥Qbar, w = (c₁ : ℂ) + c₂ * u + c₃ * t + c₄ * z + c₅ * zc := by
  obtain ⟨c₁, w₁, hw₁, rfl⟩ := Submodule.mem_span_insert.1 hw
  obtain ⟨c₂, w₂, hw₂, rfl⟩ := Submodule.mem_span_insert.1 hw₁
  obtain ⟨c₃, w₃, hw₃, rfl⟩ := Submodule.mem_span_insert.1 hw₂
  obtain ⟨c₄, w₄, hw₄, rfl⟩ := Submodule.mem_span_insert.1 hw₃
  obtain ⟨c₅, rfl⟩ := Submodule.mem_span_singleton.1 hw₄
  exact ⟨c₁, c₂, c₃, c₄, c₅, by simp only [Subfield.smul_def, smul_eq_mul]; ring⟩

theorem lin_of_eq {A B T : ℂ} (M : ℂ) (h : A = B) (hT : T = M * (A - B)) : T = 0 := by
  rw [hT, h, sub_self, mul_zero]

/-- `s` is real and non-zero. -/
theorem s_facts {u s : ℂ} (hu : u ∉ Qbar) (hss : s * s = u * conj u) : s ≠ 0 ∧ conj s = s := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ zero_mem _)
  have hn : 0 < Complex.normSq u := Complex.normSq_pos.2 hu0
  refine ⟨?_, ?_⟩
  · rintro rfl
    rw [Complex.mul_conj, zero_mul, eq_comm, Complex.ofReal_eq_zero] at hss
    linarith
  · have h1 : conj s * conj s = s * s := by
      rw [← map_mul, hss, map_mul, Complex.conj_conj, mul_comm]
    rcases mul_eq_zero.1 (show (conj s - s) * (conj s + s) = 0 by linear_combination h1) with h | h
    · exact sub_eq_zero.1 h
    · exfalso
      have h3 : s * conj s = -(u * conj u) := by linear_combination s * h - hss
      rw [Complex.mul_conj, Complex.mul_conj] at h3
      have h4 := congrArg Complex.re h3
      simp only [Complex.ofReal_re, Complex.neg_re] at h4
      linarith [Complex.normSq_nonneg s]

/-- `H = Σ_{i ≤ n} Ḡ_i X^{n−i}`. -/
noncomputable def rev (n : ℕ) (G : (↥Qbar)[X]) : (↥Qbar)[X] :=
  ∑ i ∈ Finset.range (n + 1), C (cjQ (G.coeff i)) * X ^ (n - i)

/-- With `G` of degree `m + 2 ≥ 2`, `H(v) = v^{m+2} · conj G(v)` and `H(0) ≠ 0`. -/
theorem rsetup {v : ℂ} (hv0 : v ≠ 0) (hcv : conj v = v⁻¹) (G : (↥Qbar)[X]) (hG : 2 ≤ G.natDegree) :
    ∃ m : ℕ, ∃ H : (↥Qbar)[X], aeval v H = v ^ (m + 2) * conj (aeval v G) ∧ H.eval 0 ≠ 0 := by
  obtain ⟨m, hm⟩ : ∃ m, G.natDegree = m + 2 := ⟨G.natDegree - 2, by omega⟩
  refine ⟨m, rev G.natDegree G, ?_, ?_⟩
  · rw [aeval_eq_sum_range (p := G), map_sum, Finset.mul_sum, ← hm]
    simp only [rev, map_sum, map_mul, aeval_C, aeval_X_pow, am]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ G.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [Subfield.smul_def, smul_eq_mul, map_mul, map_pow, hcv, pow_sub₀ v hv0 hi', inv_pow, cjQ_coe]
    ring
  · have hG0 : G ≠ 0 := by rintro rfl; simp at hG
    simp only [rev, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    rw [Finset.sum_eq_single G.natDegree]
    · rw [Nat.sub_self, pow_zero, mul_one]
      exact cjQ_ne_zero (leadingCoeff_ne_zero.2 hG0)
    · intro i hi hin
      rw [zero_pow (by have := Finset.mem_range.1 hi; omega), mul_zero]
    · exact fun h => absurd (Finset.self_mem_range_succ _) h

/-- Evaluating the identity cleared by `v^{m+3}` at `0` kills the coordinate of `g`. -/
theorem xkill {v u cu g cg cG w : ℂ} (hv : v ∉ Qbar) (hv0 : v ≠ 0) {m : ℕ}
    {G H L : (↥Qbar)[X]} {s κ κ' a b c x y : ↥Qbar} (hκ : κ ≠ 0) (hH0 : H.eval 0 ≠ 0)
    (hu : u = s * v) (hcu : cu = s * v⁻¹)
    (hg : g = aeval v G + κ * (v⁻¹ * cG)) (hcg : cg = cG + κ' * (v * aeval v G))
    (hH : aeval v H = v ^ (m + 2) * cG)
    (hL : aeval v L = v ^ (m + 3) * w) (hL0 : L.eval 0 = 0)
    (h : (a : ℂ) + b * u + c * cu + x * g + y * cg = w) : x = 0 := by
  have hP : L = C a * X ^ (m + 3) + C (b * s) * X ^ (m + 4) + C (c * s) * X ^ (m + 2) +
      C x * (X ^ (m + 3) * G + C κ * H) + C y * (X * H + C κ' * (X ^ (m + 4) * G)) := by
    apply sub_eq_zero.1
    apply aeval_eq_zero hv
    simp only [map_sub, map_add, map_mul, map_pow, aeval_C, aeval_X, am, hL, hH]
    subst hu hcu hg hcg
    rw [← h]
    field_simp
    ring
  have := congrArg (Polynomial.eval 0) hP
  simp [hL0] at this
  tauto

/-- With the coordinate of `g` zero, clearing by `v^{m+2}` and evaluating at `0` kills that of `ḡ`. -/
theorem ykill {v u cu g cg cG w : ℂ} (hv : v ∉ Qbar) (hv0 : v ≠ 0) {m : ℕ}
    {G H L : (↥Qbar)[X]} {s κ' a b c x y : ↥Qbar} (hH0 : H.eval 0 ≠ 0)
    (hu : u = s * v) (hcu : cu = s * v⁻¹) (hcg : cg = cG + κ' * (v * aeval v G))
    (hH : aeval v H = v ^ (m + 2) * cG)
    (hL : aeval v L = v ^ (m + 2) * w) (hL0 : L.eval 0 = 0) (hx : x = 0)
    (h : (a : ℂ) + b * u + c * cu + x * g + y * cg = w) : y = 0 := by
  have hP : L = C a * X ^ (m + 2) + C (b * s) * X ^ (m + 3) + C (c * s) * X ^ (m + 1) +
      C y * (H + C κ' * (X ^ (m + 3) * G)) := by
    apply sub_eq_zero.1
    apply aeval_eq_zero hv
    simp only [map_sub, map_add, map_mul, map_pow, aeval_C, aeval_X, am, hL, hH]
    subst hu hcu hcg hx
    simp only [ZeroMemClass.coe_zero, zero_mul, add_zero] at h
    rw [← h]
    field_simp
    ring
  have := congrArg (Polynomial.eval 0) hP
  simp [hL0] at this
  tauto

end R18_ED

open DiazModulus R18_ED Polynomial in
theorem solution
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hss : s * s = u * conj u) (W : Submodule (↥Qbar) ℂ) :
    ¬ ((∃ α β : ℂ, α ∈ Qbar ∧ β ∈ Qbar ∧ (α ≠ 0 ∨ β ≠ 0) ∧ α * u ^ 2 + β * u ^ 3 ∈ W) ∧
      (∃ e β ζ : ℂ, e ∈ Qbar ∧ β ∈ Qbar ∧ ζ ∈ Qbar ∧ e * conj e = 1 ∧ β * conj β = 1 ∧
        ζ = -(β * e ^ 2 * conj ζ) ∧
        W =
          Submodule.span Qbar ({1, u, conj u, conj (u / s) ^ 2 + e * (u / s) ^ 2, β * conj (u / s) ^ 3 + ζ * (u / s) ^ 2 + e * (u / s) ^ 3} : Set ℂ))) ∧
    ¬ ((∃ α β : ℂ, α ∈ Qbar ∧ β ∈ Qbar ∧ (α ≠ 0 ∨ β ≠ 0) ∧ α * u ^ 2 + β * u ^ 3 ∈ W) ∧
      (∃ κ : ℂ, κ ∈ Qbar ∧ κ * conj κ = 1 ∧ ∃ G : Polynomial ↥Qbar, G.coeff 0 = 0 ∧ 2 ≤ G.natDegree ∧
        W =
          Submodule.span Qbar ({1, u, conj u, Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G), conj (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G))} : Set ℂ))) ∧
    ¬ ((∃ e β ζ : ℂ, e ∈ Qbar ∧ β ∈ Qbar ∧ ζ ∈ Qbar ∧ e * conj e = 1 ∧ β * conj β = 1 ∧
        ζ = -(β * e ^ 2 * conj ζ) ∧
        W =
          Submodule.span Qbar ({1, u, conj u, conj (u / s) ^ 2 + e * (u / s) ^ 2, β * conj (u / s) ^ 3 + ζ * (u / s) ^ 2 + e * (u / s) ^ 3} : Set ℂ)) ∧
      (∃ κ : ℂ, κ ∈ Qbar ∧ κ * conj κ = 1 ∧ ∃ G : Polynomial ↥Qbar, G.coeff 0 = 0 ∧ 2 ≤ G.natDegree ∧
        W =
          Submodule.span Qbar ({1, u, conj u, Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G), conj (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G))} : Set ℂ))) := by
  obtain ⟨hs0, hsr⟩ := s_facts hu hss
  lift s to ↥Qbar using hs
  have hs0' : s ≠ 0 := fun h => hs0 (by rw [h]; rfl)
  set v := u / (s : ℂ) with hvdef
  have hv : v ∉ Qbar := fun h => hu (by
    have := mul_mem s.2 h
    rwa [hvdef, mul_div_cancel₀ u hs0] at this)
  have hv0 : v ≠ 0 := fun h => hv (h ▸ zero_mem _)
  have hu0 : u ≠ 0 := fun h => hu (h ▸ zero_mem _)
  have hcv : conj v = v⁻¹ := by
    rw [hvdef, map_div₀, hsr, inv_div, div_eq_div_iff hs0 hu0]
    linear_combination -hss
  have hu' : u = s * v := by rw [hvdef, mul_div_cancel₀ u hs0]
  have hcu' : conj u = s * v⁻¹ := by rw [← hcv, ← hsr, ← map_mul, ← hu']
  -- the conjugate of `g` and `g` itself, for `G` and `κ`
  have hgg : ∀ (κ : ↥Qbar) (G : (↥Qbar)[X]), aeval v G + κ * conj (v * aeval v G) =
      aeval v G + κ * (v⁻¹ * conj (aeval v G)) := fun κ G => by rw [map_mul, hcv]
  have hcg : ∀ (κ : ↥Qbar) (G : (↥Qbar)[X]), conj (aeval v G + κ * conj (v * aeval v G)) =
      conj (aeval v G) + cjQ κ * (v * aeval v G) := fun κ G => by
    simp only [map_add, map_mul, Complex.conj_conj, cjQ_coe]
  refine ⟨?_, ?_, ?_⟩
  · -- (P) and (Q)
    rintro ⟨⟨α, β, hα, hβ, hne, hm⟩, ⟨e, b, ζ, he, hb, hζ, -, hb1, -, hWQ⟩⟩
    rw [hWQ] at hm
    obtain ⟨c₁, c₂, c₃, c₄, c₅, h⟩ := coeffs hm
    lift α to ↥Qbar using hα
    lift β to ↥Qbar using hβ
    lift e to ↥Qbar using he
    lift b to ↥Qbar using hb
    lift ζ to ↥Qbar using hζ
    have hb0 : b ≠ 0 := by rintro rfl; simp at hb1
    obtain ⟨h0, h1, -, -, -, h5, h6⟩ := seven_terms hv (a₀ := -(c₅ * b)) (a₁ := -c₄)
      (a₂ := -(c₃ * s)) (a₃ := -c₁) (a₄ := -(c₂ * s)) (a₅ := α * s ^ 2 - c₄ * e - c₅ * ζ)
      (a₆ := β * s ^ 3 - c₅ * e) (by
        push_cast
        rw [hcu', hu', hcv] at h
        exact lin_of_eq (v ^ 3) h (by field_simp; ring))
    have hc5 : c₅ = 0 := (mul_eq_zero.1 (neg_eq_zero.1 h0)).resolve_right hb0
    have hc4 : c₄ = 0 := neg_eq_zero.1 h1
    simp only [hc4, hc5, zero_mul, sub_zero, mul_eq_zero, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, hs0', or_false] at h5 h6
    rcases hne with h | h
    · exact h (by rw [h5]; rfl)
    · exact h (by rw [h6]; rfl)
  · -- (P) and (R)
    rintro ⟨⟨α, β, hα, hβ, hne, hm⟩, ⟨κ, hκ, hκ1, G, -, hG, hWR⟩⟩
    rw [hWR] at hm
    obtain ⟨c₁, c₂, c₃, c₄, c₅, h⟩ := coeffs hm
    lift α to ↥Qbar using hα
    lift β to ↥Qbar using hβ
    lift κ to ↥Qbar using hκ
    have hκ0 : κ ≠ 0 := by rintro rfl; simp at hκ1
    obtain ⟨m, H, hH, hH0⟩ := rsetup hv0 hcv G hG
    have hx := xkill hv hv0 hκ0 hH0 hu' hcu' (hgg κ G) (hcg κ G) hH
      (L := C (α * s ^ 2) * X ^ (m + 5) + C (β * s ^ 3) * X ^ (m + 6))
      (by simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, am]; rw [hu']; ring)
      (by simp) h.symm
    have hy := ykill hv hv0 hH0 hu' hcu' (hcg κ G) hH
      (L := C (α * s ^ 2) * X ^ (m + 4) + C (β * s ^ 3) * X ^ (m + 5))
      (by simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, am]; rw [hu']; ring)
      (by simp) hx h.symm
    rw [hx, hy] at h
    simp only [ZeroMemClass.coe_zero, zero_mul, add_zero] at h
    rw [hcu', hu'] at h
    obtain ⟨-, -, -, h3, h4, -, -⟩ := seven_terms hv (a₀ := -(c₃ * s)) (a₁ := -c₁)
      (a₂ := -(c₂ * s)) (a₃ := α * s ^ 2) (a₄ := β * s ^ 3) (a₅ := 0) (a₆ := 0) (by
        push_cast
        exact lin_of_eq v h (by field_simp; ring))
    simp only [mul_eq_zero, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      hs0', or_false] at h3 h4
    rcases hne with h | h
    · exact h (by rw [h3]; rfl)
    · exact h (by rw [h4]; rfl)
  · -- (Q) and (R)
    rintro ⟨⟨e, b, ζ, he, hb, hζ, -, -, -, hWQ⟩, ⟨κ, hκ, hκ1, G, -, hG, hWR⟩⟩
    have hn0 : conj v ^ 2 + e * v ^ 2 ∈ W := by
      rw [hWQ]; exact Submodule.subset_span (by simp)
    rw [hWR] at hn0
    obtain ⟨c₁, c₂, c₃, c₄, c₅, h⟩ := coeffs hn0
    lift e to ↥Qbar using he
    lift κ to ↥Qbar using hκ
    have hκ0 : κ ≠ 0 := by rintro rfl; simp at hκ1
    obtain ⟨m, H, hH, hH0⟩ := rsetup hv0 hcv G hG
    have hx := xkill hv hv0 hκ0 hH0 hu' hcu' (hgg κ G) (hcg κ G) hH
      (L := X ^ (m + 1) + C e * X ^ (m + 5))
      (by simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, am]; rw [hcv]; field_simp; ring)
      (by simp) h.symm
    have hy := xkill hv hv0 hκ0 hH0 hu' hcu' (hgg κ G) (hcg κ G) hH
      (a := cjQ c₁) (b := cjQ c₃) (c := cjQ c₂) (x := cjQ c₅) (y := cjQ c₄)
      (w := v ^ 2 + conj (e : ℂ) * conj v ^ 2)
      (L := X ^ (m + 5) + C (cjQ e) * X ^ (m + 1))
      (by simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, am, cjQ_coe]; rw [hcv]; field_simp; ring)
      (by simp)
      (by
        have := congrArg conj h
        simp only [map_add, map_mul, map_pow, Complex.conj_conj, cjQ_coe] at this ⊢
        linear_combination this.symm)
    have hc5 : c₅ = 0 := by
      by_contra h5; exact cjQ_ne_zero h5 hy
    rw [hx, hc5] at h
    simp only [ZeroMemClass.coe_zero, zero_mul, add_zero] at h
    rw [hcu', hu', hcv] at h
    obtain ⟨h0, -⟩ := seven_terms hv (a₀ := 1) (a₁ := -(c₃ * s)) (a₂ := -c₁) (a₃ := -(c₂ * s))
      (a₄ := e) (a₅ := 0) (a₆ := 0) (by
        push_cast
        exact lin_of_eq (v ^ 2) h (by field_simp; ring))
    exact one_ne_zero h0
