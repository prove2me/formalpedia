-- Prove2me | solution 1 for DiazModulus.cubic_window_hull_polynomial_class_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T14:40:50.232667+00:00
-- url     : https://prove2.me/submissions/a03c67eb-4ce1-4284-9cdf-93a2c8f3f72d

import Mathlib
import Definitions.Def_DiazModulus

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open Complex ComplexConjugate

/-! # The polynomial class of a cubic-window conjugation hull

Let `v ∉ Q̄` with `v v̄ = 1`, and `z ≡ m := a v̄³ + b v̄² + c v² + d v³` modulo `H₀ = span(1, v, v̄)`.
Then `z̄ ≡ m̄ = d̄ v̄³ + c̄ v̄² + b̄ v² + ā v³` (as `H₀` is conjugation-stable), so
`W = span(1, v, v̄, z, z̄) = span(1, v, v̄, m, m̄)`, and `dim W = 5` makes `1, v, v̄, m, m̄` free.
Since `v` is transcendental, `v⁻³, …, v³` are free over `Q̄` (multiply by `v³`). So an element
`x₀ + x₁v + x₂v̄ + xm + ym̄` of `W` equals `αv² + βv³` only if its `v̄³` and `v̄²` coefficients
`xa + yd̄` and `xb + yc̄` vanish. (→) `(α, β) ≠ 0` forces `(x, y) ≠ 0`, and Cramer's rule gives
`(ac̄ − bd̄)x = (ac̄ − bd̄)y = 0`, so `ac̄ − bd̄ = 0`. (←) If `ac̄ = bd̄`, take `(x, y) = (d̄, −a)`, or
`(c̄, −b)` when `a = d = 0` (then `(b, c) ≠ 0`, since `m ≠ 0`). Then `xm + ym̄ = αv² + βv³` with
`α = xc + yb̄`, `β = xd + yā`, and `(α, β) ≠ 0` because `m, m̄` are free.
-/

namespace R18_Eb1

open DiazModulus Polynomial

/-- Complex conjugation as a `ℚ`-algebra map. -/
noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

/-- Conjugation maps `Q̄` to itself. -/
theorem conj_mem {a : ℂ} (ha : a ∈ Qbar) : conj a ∈ Qbar := by
  obtain ⟨p, hp0, hp⟩ := mem_Qbar_iff.1 ha
  refine mem_Qbar_iff.2 ⟨p, hp0, ?_⟩
  rw [show (conj a : ℂ) = cjQ a from rfl, Polynomial.aeval_algHom_apply, hp, map_zero]


/-- Outside `Q̄`, no non-zero polynomial over `Q̄` vanishes. -/
theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) :
    P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

/-- `v⁻³, …, v³` are free over `Q̄` at a transcendental `v` with `v v̄ = 1`. -/
theorem coeff7 {v : ℂ} (hv : v ∉ Qbar) (hv1 : v * conj v = 1) {c₀ c₁ c₂ c₃ c₄ c₅ c₆ : ℂ}
    (h₀ : c₀ ∈ Qbar) (h₁ : c₁ ∈ Qbar) (h₂ : c₂ ∈ Qbar) (h₃ : c₃ ∈ Qbar) (h₄ : c₄ ∈ Qbar)
    (h₅ : c₅ ∈ Qbar) (h₆ : c₆ ∈ Qbar)
    (h : c₀ * conj v ^ 3 + c₁ * conj v ^ 2 + c₂ * conj v + c₃ + c₄ * v + c₅ * v ^ 2 +
      c₆ * v ^ 3 = 0) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 ∧ c₄ = 0 ∧ c₅ = 0 ∧ c₆ = 0 := by
  lift c₀ to Qbar using h₀; lift c₁ to Qbar using h₁; lift c₂ to Qbar using h₂
  lift c₃ to Qbar using h₃; lift c₄ to Qbar using h₄; lift c₅ to Qbar using h₅
  lift c₆ to Qbar using h₆
  have hP := aeval_eq_zero hv (P := C c₀ + C c₁ * X + C c₂ * X ^ 2 + C c₃ * X ^ 3 +
    C c₄ * X ^ 4 + C c₅ * X ^ 5 + C c₆ * X ^ 6)
    (by
      simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, am]
      linear_combination v ^ 3 * h - ((c₀ : ℂ) * ((v * conj v) ^ 2 + v * conj v + 1) +
        c₁ * v * (v * conj v + 1) + c₂ * v ^ 2) * hv1)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 0) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 1) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 2) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 3) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 4) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 5) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 6) hP

theorem span_mul_mem {S : Set ℂ} {c w : ℂ} (hc : c ∈ Qbar) (hw : w ∈ Submodule.span Qbar S) :
    c * w ∈ Submodule.span Qbar S := by
  have := Submodule.smul_mem _ (⟨c, hc⟩ : ↥Qbar) hw
  rwa [Subfield.smul_def, smul_eq_mul] at this

/-- A span whose generators have conjugates in it is conjugation-stable. -/
theorem span_conj_stable {S : Set ℂ} (hS : ∀ x ∈ S, conj x ∈ Submodule.span Qbar S) :
    ∀ w ∈ Submodule.span Qbar S, conj w ∈ Submodule.span Qbar S := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have hcx : conj (c • x) = (⟨conj (c : ℂ), conj_mem c.2⟩ : ↥Qbar) • conj x :=
      map_mul conj (c : ℂ) x
    rw [hcx]
    exact Submodule.smul_mem _ _ hx

theorem conj_H0 {v w : ℂ} (hw : w ∈ Submodule.span Qbar ({1, v, conj v} : Set ℂ)) :
    conj w ∈ Submodule.span Qbar ({1, v, conj v} : Set ℂ) := by
  refine span_conj_stable (fun x hx => ?_) w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · rw [map_one]; exact Submodule.subset_span (by simp)
  · exact Submodule.subset_span (by simp)
  · rw [conj_conj]; exact Submodule.subset_span (by simp)

theorem H0_le {v x y : ℂ} : Submodule.span Qbar ({1, v, conj v} : Set ℂ) ≤
    Submodule.span Qbar ({1, v, conj v, x, y} : Set ℂ) :=
  Submodule.span_mono (by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
    tauto)

/-- Two hulls over `span(1, v, v̄)`: the first lies in the second if its last generators do. -/
theorem span5_le {v x y x' y' : ℂ}
    (hx : x ∈ Submodule.span Qbar ({1, v, conj v, x', y'} : Set ℂ))
    (hy : y ∈ Submodule.span Qbar ({1, v, conj v, x', y'} : Set ℂ)) :
    Submodule.span Qbar ({1, v, conj v, x, y} : Set ℂ) ≤
      Submodule.span Qbar ({1, v, conj v, x', y'} : Set ℂ) := by
  rw [Submodule.span_le]
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with h | h | h | h | h <;> rw [h] <;>
    first | exact hx | exact hy | exact Submodule.subset_span (by simp)

/-- Replacing `z, z'` by `m, m'` modulo `span(1, v, v̄)` does not change the hull. -/
theorem span_swap {v z z' m m' : ℂ} (hz : z - m ∈ Submodule.span Qbar ({1, v, conj v} : Set ℂ))
    (hz' : z' - m' ∈ Submodule.span Qbar ({1, v, conj v} : Set ℂ)) :
    Submodule.span Qbar ({1, v, conj v, z, z'} : Set ℂ) =
      Submodule.span Qbar ({1, v, conj v, m, m'} : Set ℂ) := by
  have k : ∀ {a b x y : ℂ}, a - b ∈ Submodule.span Qbar ({1, v, conj v} : Set ℂ) →
      b ∈ Submodule.span Qbar ({1, v, conj v, x, y} : Set ℂ) →
      a ∈ Submodule.span Qbar ({1, v, conj v, x, y} : Set ℂ) := fun h hb => by
    simpa using Submodule.add_mem _ (H0_le h) hb
  have n : ∀ {a b : ℂ}, a - b ∈ Submodule.span Qbar ({1, v, conj v} : Set ℂ) →
      b - a ∈ Submodule.span Qbar ({1, v, conj v} : Set ℂ) := fun h => by
    rw [← neg_sub]; exact neg_mem h
  exact le_antisymm (span5_le (k hz (Submodule.subset_span (by simp)))
      (k hz' (Submodule.subset_span (by simp))))
    (span5_le (k (n hz) (Submodule.subset_span (by simp))) (k (n hz') (Submodule.subset_span (by simp))))

theorem li_of_finrank {v m m' : ℂ}
    (h5 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, v, conj v, m, m'} : Set ℂ)) = 5) :
    LinearIndependent (↥Qbar) ![1, v, conj v, m, m'] := by
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin,
    show Set.range ![1, v, conj v, m, m'] = ({1, v, conj v, m, m'} : Set ℂ) by
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]]
  exact h5.symm

theorem li2 {v m m' : ℂ} (hli : LinearIndependent (↥Qbar) ![1, v, conj v, m, m'])
    {x y : ℂ} (hx : x ∈ Qbar) (hy : y ∈ Qbar) (h : x * m + y * m' = 0) : x = 0 ∧ y = 0 := by
  have := Fintype.linearIndependent_iff.1 hli ![0, 0, 0, ⟨x, hx⟩, ⟨y, hy⟩] (by
    simp [Fin.sum_univ_five, Subfield.smul_def]
    linear_combination h)
  exact ⟨by simpa using congrArg Subtype.val (this 3), by simpa using congrArg Subtype.val (this 4)⟩

theorem coeffs {v t z zc w : ℂ} (hw : w ∈ Submodule.span Qbar ({1, v, t, z, zc} : Set ℂ)) :
    ∃ c₁ c₂ c₃ c₄ c₅ : ↥Qbar, w = (c₁ : ℂ) + c₂ * v + c₃ * t + c₄ * z + c₅ * zc := by
  obtain ⟨c₁, w₁, hw₁, rfl⟩ := Submodule.mem_span_insert.1 hw
  obtain ⟨c₂, w₂, hw₂, rfl⟩ := Submodule.mem_span_insert.1 hw₁
  obtain ⟨c₃, w₃, hw₃, rfl⟩ := Submodule.mem_span_insert.1 hw₂
  obtain ⟨c₄, w₄, hw₄, rfl⟩ := Submodule.mem_span_insert.1 hw₃
  obtain ⟨c₅, rfl⟩ := Submodule.mem_span_singleton.1 hw₄
  exact ⟨c₁, c₂, c₃, c₄, c₅, by simp only [Subfield.smul_def, smul_eq_mul]; ring⟩

theorem mem5 {v t z zc x₀ x₁ x₂ x₃ x₄ : ℂ} (h₀ : x₀ ∈ Qbar) (h₁ : x₁ ∈ Qbar) (h₂ : x₂ ∈ Qbar)
    (h₃ : x₃ ∈ Qbar) (h₄ : x₄ ∈ Qbar) :
    x₀ + x₁ * v + x₂ * t + x₃ * z + x₄ * zc ∈ Submodule.span Qbar ({1, v, t, z, zc} : Set ℂ) := by
  have g : ∀ {c : ℂ} (w : ℂ), c ∈ Qbar → w ∈ ({1, v, t, z, zc} : Set ℂ) →
      c * w ∈ Submodule.span Qbar ({1, v, t, z, zc} : Set ℂ) :=
    fun _ hc hw => span_mul_mem hc (Submodule.subset_span hw)
  have := Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (g 1 h₀ (by simp)) (g v h₁ (by simp))) (g t h₂ (by simp))) (g z h₃ (by simp)))
    (g zc h₄ (by simp))
  rwa [mul_one] at this

end R18_Eb1

open DiazModulus R18_Eb1 in
theorem solution
    (v : ℂ) (hv : v ∉ Qbar) (hv1 : v * conj v = 1)
    (z a b c d : ℂ) (ha : a ∈ Qbar) (hb : b ∈ Qbar) (hc : c ∈ Qbar) (hd : d ∈ Qbar)
    (hz : z - (a * conj v ^ 3 + b * conj v ^ 2 + c * v ^ 2 + d * v ^ 3) ∈ Submodule.span Qbar ({1, v, conj v} : Set ℂ))
    (h5 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, v, conj v, z, conj z} : Set ℂ)) = 5) :
    (∃ α β : ℂ, α ∈ Qbar ∧ β ∈ Qbar ∧ (α ≠ 0 ∨ β ≠ 0) ∧ α * v ^ 2 + β * v ^ 3 ∈ Submodule.span Qbar ({1, v, conj v, z, conj z} : Set ℂ)) ↔
      (a * conj c - b * conj d) = 0 := by
  set m := a * conj v ^ 3 + b * conj v ^ 2 + c * v ^ 2 + d * v ^ 3 with hm
  have hmc : conj m = conj d * conj v ^ 3 + conj c * conj v ^ 2 + conj b * v ^ 2 +
      conj a * v ^ 3 := by
    rw [hm]; simp only [map_add, map_mul, map_pow, conj_conj]; ring
  have hW := span_swap hz (by have := conj_H0 hz; rwa [map_sub] at this)
  rw [hW] at h5 ⊢
  have hli := li_of_finrank h5
  constructor
  · rintro ⟨α, β, hα, hβ, hne, hmem⟩
    obtain ⟨x₀, x₁, x₂, x, y, e⟩ := coeffs hmem
    rw [hmc, hm] at e
    obtain ⟨h0, h1, -, -, -, h5', h6⟩ := coeff7 hv hv1 (c₀ := x * a + y * conj d)
      (c₁ := x * b + y * conj c) (c₂ := x₂) (c₃ := x₀) (c₄ := x₁)
      (c₅ := x * c + y * conj b - α) (c₆ := x * d + y * conj a - β)
      (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb1.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb1.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb1.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb1.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb1.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb1.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb1.conj_mem | exact zero_mem _ | exact one_mem _))
      (by linear_combination -e)
    by_contra hp
    have hx : (x : ℂ) = 0 := by
      have : (a * conj c - b * conj d) * x = 0 := by linear_combination conj c * h0 - conj d * h1
      exact (mul_eq_zero.1 this).resolve_left hp
    have hy : (y : ℂ) = 0 := by
      have : (a * conj c - b * conj d) * y = 0 := by linear_combination a * h1 - b * h0
      exact (mul_eq_zero.1 this).resolve_left hp
    rw [hx, hy] at h5' h6
    rcases hne with h | h
    · exact h (by linear_combination -h5')
    · exact h (by linear_combination -h6)
  · intro hp
    have key : ∀ p q : ℂ, p ∈ Qbar → q ∈ Qbar → (p ≠ 0 ∨ q ≠ 0) → p * a + q * conj d = 0 →
        p * b + q * conj c = 0 → ∃ α β : ℂ, α ∈ Qbar ∧ β ∈ Qbar ∧ (α ≠ 0 ∨ β ≠ 0) ∧
          α * v ^ 2 + β * v ^ 3 ∈ Submodule.span Qbar ({1, v, conj v, m, conj m} : Set ℂ) := by
      intro p q hp hq hpq h1 h2
      refine ⟨p * c + q * conj b, p * d + q * conj a, by repeat' (first | assumption | exact SetLike.coe_mem _ | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb1.conj_mem | exact zero_mem _ | exact one_mem _), by repeat' (first | assumption | exact SetLike.coe_mem _ | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb1.conj_mem | exact zero_mem _ | exact one_mem _), ?_, ?_⟩
      · by_contra hcon
        push Not at hcon
        obtain ⟨hp0, hq0⟩ := li2 hli hp hq (by
          rw [hmc, hm]
          linear_combination conj v ^ 3 * h1 + conj v ^ 2 * h2 + v ^ 2 * hcon.1 + v ^ 3 * hcon.2)
        rcases hpq with h | h <;> contradiction
      · have := mem5 (v := v) (t := conj v) (z := m) (zc := conj m) (zero_mem _) (zero_mem _)
          (zero_mem _) hp hq
        convert this using 1
        rw [hmc, hm]
        linear_combination (-conj v ^ 3) * h1 + (-conj v ^ 2) * h2
    by_cases had : a = 0 ∧ d = 0
    · obtain ⟨rfl, rfl⟩ := had
      refine key (conj c) (-b) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb1.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb1.conj_mem | exact zero_mem _ | exact one_mem _)) ?_ (by simp) (by ring)
      by_contra hcon
      push Not at hcon
      have hb0 : b = 0 := neg_eq_zero.1 hcon.2
      have hc0 : c = 0 := by simpa using hcon.1
      have := li2 hli (one_mem _) (zero_mem _) (x := 1) (y := 0) (by rw [hm, hb0, hc0]; ring)
      exact one_ne_zero this.1
    · refine key (conj d) (-a) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb1.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb1.conj_mem | exact zero_mem _ | exact one_mem _)) ?_ (by ring)
        (by linear_combination -hp)
      by_contra hcon
      push Not at hcon
      exact had ⟨neg_eq_zero.1 hcon.2, by simpa using hcon.1⟩
