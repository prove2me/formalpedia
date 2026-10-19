-- Prove2me | solution 1 for DiazModulus.laurent_conj_hull_class_finrank_eq_five
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T14:32:36.918163+00:00
-- url     : https://prove2.me/submissions/13b183b1-f05f-45cd-86b5-1013f7643f12

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A conjugation hull in the polynomial, involution or real pencil class is five-dimensional

Let `u ∉ Q̄`, `s ∈ Q̄` with `s² = u ū`, and `z = Σ_{|j| ≤ k} c_j (u/s)^j` (any complex `c_j`) whose hull
`W = span_Q̄ {1, u, ū, z, z̄}` is in class (P), (Q) or (R). Then `dim W = 5`.
Work in `v = u/s`: `s` is real, so `v̄ = v⁻¹`, and `v` is transcendental. (P): with
`m = α u² + β u³ ∈ W`, also `m̄ ∈ W` (the hull is conjugation-stable); `1, u, ū, m, m̄` are free
(a relation cleared by `v³` is a degree-6 polynomial in `v`, and its seven coefficients vanish), and
`W` has five generators. (Q): the normal-form generators are free in the same way (`β ≠ 0` from
`β β̄ = 1`). (R): with `n = deg G ≥ 2` put `H = Σ Ḡ_i X^{n−i}`, so `H(v) = vⁿ conj G(v)` and
`H(0) = Ḡ_n ≠ 0`; a relation cleared by `vⁿ⁺¹` and evaluated at `0` loses its `g` coordinate,
its conjugate loses the `ḡ` one, and `1, u, ū` are free. -/

namespace R18_E5

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
  have c := fun n => congrArg (coeff · n) hP
  simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero] at c
  exact ⟨by simpa using c 0, by simpa using c 1, by simpa using c 2, by simpa using c 3,
    by simpa using c 4, by simpa using c 5, by simpa using c 6⟩

theorem lin_of_eq {A B T : ℂ} (M : ℂ) (h : A = B) (hT : T = M * (A - B)) : T = 0 := by
  rw [hT, h, sub_self, mul_zero]

/-- `s` is real and non-zero. -/
theorem s_facts {u s : ℂ} (hu : u ∉ Qbar) (hss : s * s = u * conj u) : s ≠ 0 ∧ conj s = s := by
  have hn : 0 < Complex.normSq u := Complex.normSq_pos.2 fun h => hu (h ▸ zero_mem _)
  rw [Complex.mul_conj] at hss
  have h1 := congrArg Complex.im hss
  have h2 := congrArg Complex.re hss
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re] at h1 h2
  have him : s.im = 0 := by
    rcases mul_eq_zero.1 (show s.re * s.im = 0 by linarith) with h | h
    · rw [h] at h2; nlinarith [sq_nonneg s.im]
    · exact h
  exact ⟨fun h0 => by simp [h0] at h2; linarith, Complex.ext (by simp) (by simp [him])⟩

/-- `span {1, u, ū, z, z̄}` is conjugation-stable. -/
theorem hull_conj_stable (u z : ℂ) :
    ∀ w ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ),
      conj w ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact Submodule.subset_span (by simp)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [show conj (c • x) = cjQ c • conj x from map_mul conj (c : ℂ) x]
    exact Submodule.smul_mem _ _ hx

theorem finrank_le_five (a b c d e : ℂ) :
    Module.finrank (↥Qbar) (Submodule.span Qbar ({a, b, c, d, e} : Set ℂ)) ≤ 5 := by
  classical
  have h := finrank_span_finset_le_card (R := ↥Qbar) ({a, b, c, d, e} : Finset ℂ)
  simp only [Finset.coe_insert, Finset.coe_singleton] at h
  exact h.trans Finset.card_le_five

/-- Five free vectors `1, a₁, …, a₄` span a five-dimensional space. -/
theorem finrank_five {a₁ a₂ a₃ a₄ : ℂ}
    (h : ∀ c₀ c₁ c₂ c₃ c₄ : ↥Qbar, (c₀ : ℂ) + c₁ * a₁ + c₂ * a₂ + c₃ * a₃ + c₄ * a₄ = 0 →
      c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 ∧ c₄ = 0) :
    Module.finrank (↥Qbar) (Submodule.span Qbar ({1, a₁, a₂, a₃, a₄} : Set ℂ)) = 5 := by
  have hli : LinearIndependent (↥Qbar) ![1, a₁, a₂, a₃, a₄] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Subfield.smul_def,
      smul_eq_mul, mul_one] at hg
    obtain ⟨h0, h1, h2, h3, h4⟩ := h _ _ _ _ _ hg
    intro i; fin_cases i <;> assumption
  have := finrank_span_eq_card hli
  rw [show Set.range ![1, a₁, a₂, a₃, a₄] = ({1, a₁, a₂, a₃, a₄} : Set ℂ) by
    simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]] at this
  rw [this, Fintype.card_fin]

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

/-- Evaluating a relation cleared by `v^{m+3}` at `0` kills the coordinate of `g`. -/
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

/-- `1, u, ū, α u² + β u³` and its conjugate are free when `(α, β) ≠ 0`. -/
theorem dimP {v u : ℂ} (hv : v ∉ Qbar) (hcv : conj v = v⁻¹) {s α β : ↥Qbar} (hs0 : s ≠ 0)
    (hsr : conj (s : ℂ) = s) (hu : u = s * v) (hv0 : v ≠ 0) (hne : α ≠ 0 ∨ β ≠ 0) (c₀ c₁ c₂ c₃ c₄ : ↥Qbar)
    (h : (c₀ : ℂ) + c₁ * u + c₂ * conj u + c₃ * (α * u ^ 2 + β * u ^ 3) +
      c₄ * conj (α * u ^ 2 + β * u ^ 3) = 0) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 ∧ c₄ = 0 := by
  have hcu : conj u = s * v⁻¹ := by rw [hu, map_mul, hsr, hcv]
  simp only [map_add, map_mul, map_pow] at h
  rw [hcu, hu] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := seven_terms hv (a₀ := c₄ * cjQ β * s ^ 3)
    (a₁ := c₄ * cjQ α * s ^ 2) (a₂ := c₂ * s) (a₃ := c₀) (a₄ := c₁ * s) (a₅ := c₃ * α * s ^ 2)
    (a₆ := c₃ * β * s ^ 3) (by
      push_cast
      simp only [cjQ_coe]
      exact lin_of_eq (v ^ 3) h (by field_simp; ring))
  simp only [mul_eq_zero, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, hs0,
    or_false] at h0 h1 h2 h4 h5 h6
  have hc : c₃ = 0 ∧ c₄ = 0 := by
    rcases hne with hα | hβ
    · exact ⟨h5.resolve_right hα, h1.resolve_right (cjQ_ne_zero hα)⟩
    · exact ⟨h6.resolve_right hβ, h0.resolve_right (cjQ_ne_zero hβ)⟩
  exact ⟨h3, h4, h2, hc.1, hc.2⟩

/-- The five generators of the involution normal form are free when `β ≠ 0`. -/
theorem dimQ {v u : ℂ} (hv : v ∉ Qbar) (hcv : conj v = v⁻¹) {s e b ζ : ↥Qbar} (hs0 : s ≠ 0)
    (hsr : conj (s : ℂ) = s) (hu : u = s * v) (hv0 : v ≠ 0) (hb : b ≠ 0) (c₀ c₁ c₂ c₃ c₄ : ↥Qbar)
    (h : (c₀ : ℂ) + c₁ * u + c₂ * conj u + c₃ * (conj v ^ 2 + e * v ^ 2) +
      c₄ * (b * conj v ^ 3 + ζ * v ^ 2 + e * v ^ 3) = 0) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 ∧ c₄ = 0 := by
  have hcu : conj u = s * v⁻¹ := by rw [hu, map_mul, hsr, hcv]
  rw [hcu, hu, hcv] at h
  obtain ⟨h0, h1, h2, h3, h4, -, -⟩ := seven_terms hv (a₀ := c₄ * b) (a₁ := c₃) (a₂ := c₂ * s)
    (a₃ := c₀) (a₄ := c₁ * s) (a₅ := c₃ * e + c₄ * ζ) (a₆ := c₄ * e) (by
      push_cast
      exact lin_of_eq (v ^ 3) h (by field_simp; ring))
  simp only [mul_eq_zero, hs0, hb, or_false] at h0 h2 h4
  exact ⟨h3, h4, h2, h1, h0⟩

/-- The five generators of the real pencil normal form are free when `deg G ≥ 2`. -/
theorem dimR {v u : ℂ} (hv : v ∉ Qbar) (hcv : conj v = v⁻¹) {s κ : ↥Qbar} (hs0 : s ≠ 0)
    (hsr : conj (s : ℂ) = s) (hu : u = s * v) (hv0 : v ≠ 0) (hκ : κ ≠ 0) (G : (↥Qbar)[X])
    (hG : 2 ≤ G.natDegree) (c₀ c₁ c₂ c₃ c₄ : ↥Qbar)
    (h : (c₀ : ℂ) + c₁ * u + c₂ * conj u + c₃ * (aeval v G + κ * conj (v * aeval v G)) +
      c₄ * conj (aeval v G + κ * conj (v * aeval v G)) = 0) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 ∧ c₄ = 0 := by
  have hcu : conj u = s * v⁻¹ := by rw [hu, map_mul, hsr, hcv]
  obtain ⟨m, H, hH, hH0⟩ := rsetup hv0 hcv G hG
  have hgg : aeval v G + κ * conj (v * aeval v G) = aeval v G + κ * (v⁻¹ * conj (aeval v G)) := by
    rw [map_mul, hcv]
  have hcg : conj (aeval v G + κ * conj (v * aeval v G)) =
      conj (aeval v G) + cjQ κ * (v * aeval v G) := by
    simp only [map_add, map_mul, Complex.conj_conj, cjQ_coe]
  have h3 := xkill hv hv0 hκ hH0 hu hcu hgg hcg hH (L := 0) (by simp) (by simp) h
  have h4 := xkill hv hv0 hκ hH0 hu hcu hgg hcg hH (L := 0) (by simp) (by simp)
    (a := cjQ c₀) (b := cjQ c₂) (c := cjQ c₁) (x := cjQ c₄) (y := cjQ c₃) (w := 0) (by
      have := congrArg conj h
      simp only [map_add, map_mul, map_zero, Complex.conj_conj, cjQ_coe] at this ⊢
      linear_combination this)
  replace h4 : c₄ = 0 := by by_contra h4'; exact cjQ_ne_zero h4' h4
  rw [h3, h4] at h
  simp only [ZeroMemClass.coe_zero, zero_mul, add_zero] at h
  rw [hcu, hu] at h
  obtain ⟨h0, h1, h2, -⟩ := seven_terms hv (a₀ := c₂ * s) (a₁ := c₀) (a₂ := c₁ * s) (a₃ := 0)
    (a₄ := 0) (a₅ := 0) (a₆ := 0) (by
      push_cast
      exact lin_of_eq v h (by field_simp; ring))
  simp only [mul_eq_zero, hs0, or_false] at h0 h2
  exact ⟨h1, h2, h0, h3, h4⟩

end R18_E5

open DiazModulus R18_E5 in
theorem solution
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hss : s * s = u * conj u)
    (k : ℕ) (c : ℤ → ℂ)
    (hcls : (∃ α β : ℂ, α ∈ Qbar ∧ β ∈ Qbar ∧ (α ≠ 0 ∨ β ≠ 0) ∧ α * u ^ 2 + β * u ^ 3 ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ)) ∨
      (∃ e β ζ : ℂ, e ∈ Qbar ∧ β ∈ Qbar ∧ ζ ∈ Qbar ∧ e * conj e = 1 ∧ β * conj β = 1 ∧
        ζ = -(β * e ^ 2 * conj ζ) ∧
        Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ) =
          Submodule.span Qbar ({1, u, conj u, conj (u / s) ^ 2 + e * (u / s) ^ 2, β * conj (u / s) ^ 3 + ζ * (u / s) ^ 2 + e * (u / s) ^ 3} : Set ℂ)) ∨
      (∃ κ : ℂ, κ ∈ Qbar ∧ κ * conj κ = 1 ∧ ∃ G : Polynomial ↥Qbar, G.coeff 0 = 0 ∧ 2 ≤ G.natDegree ∧
        Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ) =
          Submodule.span Qbar ({1, u, conj u, Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G), conj (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G))} : Set ℂ))) :
    Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ)) = 5 := by
  obtain ⟨hs0, hsr⟩ := s_facts hu hss
  have hu0 : u ≠ 0 := fun h => hu (h ▸ zero_mem _)
  set z := ∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j with hz
  lift s to ↥Qbar using hs
  have hs0' : s ≠ 0 := fun h => hs0 (by rw [h]; rfl)
  have hv : u / s ∉ Qbar := fun h => hu (by
    have := mul_mem s.2 h
    rwa [mul_div_cancel₀ u hs0] at this)
  have hv0 : u / s ≠ 0 := div_ne_zero hu0 hs0
  have hcv : conj (u / s) = (u / s)⁻¹ := by
    rw [map_div₀, hsr, inv_div, div_eq_div_iff hs0 hu0]
    linear_combination -hss
  have hu' : u = s * (u / s) := by rw [mul_div_cancel₀ u hs0]
  rcases hcls with ⟨α, β, hα, hβ, hne, hm⟩ | ⟨e, b, ζ, he, hb, hζ, -, hb1, -, hWQ⟩ |
    ⟨κ, hκ, hκ1, G, -, hG, hWR⟩
  · lift α to ↥Qbar using hα
    lift β to ↥Qbar using hβ
    have hne' : α ≠ 0 ∨ β ≠ 0 := hne.imp (fun h h0 => h (by rw [h0]; rfl)) (fun h h0 => h (by rw [h0]; rfl))
    have hP5 := finrank_five (dimP hv hcv hs0' hsr hu' hv0 hne')
    have hPle : Submodule.span Qbar ({1, u, conj u, (α : ℂ) * u ^ 2 + β * u ^ 3,
        conj ((α : ℂ) * u ^ 2 + β * u ^ 3)} : Set ℂ) ≤
        Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) := by
      refine Submodule.span_le.2 ?_
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      exact ⟨Submodule.subset_span (by simp), Submodule.subset_span (by simp),
        Submodule.subset_span (by simp), hm, hull_conj_stable u z _ hm⟩
    have : FiniteDimensional (↥Qbar) (Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ)) :=
      FiniteDimensional.span_of_finite _ (Set.toFinite _)
    exact le_antisymm (finrank_le_five _ _ _ _ _) (hP5 ▸ Submodule.finrank_mono hPle)
  · lift e to ↥Qbar using he
    lift b to ↥Qbar using hb
    lift ζ to ↥Qbar using hζ
    have hb0 : b ≠ 0 := by rintro rfl; simp at hb1
    rw [hWQ]
    exact finrank_five (dimQ hv hcv hs0' hsr hu' hv0 hb0)
  · lift κ to ↥Qbar using hκ
    have hκ0 : κ ≠ 0 := by rintro rfl; simp at hκ1
    rw [hWR]
    exact finrank_five (dimR hv hcv hs0' hsr hu' hv0 hκ0 G hG)
