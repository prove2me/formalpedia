-- Prove2me | solution 1 for DiazModulus.cubic_window_hull_involution_class_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T14:40:47.464087+00:00
-- url     : https://prove2.me/submissions/a5ce37a7-f274-4aeb-9daa-10ab752a9bc8

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_laurent_involution_space_conj_stable_constraints

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open Complex ComplexConjugate

/-! # The involution class of a cubic-window conjugation hull

Let `v ∉ Q̄`, `v v̄ = 1`, `z ≡ m := a v̄³ + b v̄² + c v² + d v³` modulo `span(1, v, v̄)`, so that
`W = span(1, v, v̄, m, m̄)` with `1, v, v̄, m, m̄` free (`dim W = 5`), and `v⁻³, …, v³` are free
over `Q̄`. Write `p₁₂ = ac̄ − bd̄`, `p₁₃ = ab̄ − cd̄`, `p₁₄ = aā − dd̄`.
(→) `m` lies in `span(1, v, v̄, n₀, n₁)` with `n₀ = v̄² + ev²`, `n₁ = βv̄³ + ζv² + ev³`; the
`v̄³` and `v³` coefficients give `a = x β`, `d = x e`, so `p₁₄ = x x̄ (ββ̄ − eē) = 0`; and if
`a = d = 0` the `v̄³` coefficient of `n₁ ∈ W` gives `β = 0`, against `ββ̄ = 1`.
(←) `p₁₄ = 0` and `(a, d) ≠ 0` give `a, d ≠ 0`. The identity `ā p₁₃ = b̄ p₁₄ − d̄ p̄₁₂` and
`d̄m − a m̄ = −(p₁₂v̄² + p₁₃v² + p₁₄v³)` with freeness of `m, m̄` give `p₁₂ ≠ 0` and `p₁₃ ≠ 0`.
Put `e = p₁₃/p₁₂`, `β = ea/d`, `ζ = e(c − be)/d`: then `d̄m − a m̄ = −p₁₂ n₀` and
`d n₁ = e(m − b n₀)`, so `W = span(1, v, v̄, n₀, n₁)`. This span is conjugation-stable (it is `W`),
and `laurent_involution_space_conj_stable_constraints` (`β ≠ 0`) gives `|e| = |β| = 1` and
`ζ = −βe²ζ̄`.
-/

namespace R18_Eb2

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

theorem mul_conj_eq_zero {x : ℂ} (h : x * conj x = 0) : x = 0 := by
  rw [Complex.mul_conj, Complex.ofReal_eq_zero, Complex.normSq_eq_zero] at h
  exact h

/-- `span(1, v, v̄, m, m̄)` is conjugation-stable. -/
theorem W_conj {v m : ℂ} : ∀ w ∈ Submodule.span Qbar ({1, v, conj v, m, conj m} : Set ℂ),
    conj w ∈ Submodule.span Qbar ({1, v, conj v, m, conj m} : Set ℂ) := by
  refine span_conj_stable (fun x hx => ?_)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h | h | h | h <;> rw [h]
  · rw [map_one]; exact Submodule.subset_span (by simp)
  · exact Submodule.subset_span (by simp)
  · rw [conj_conj]; exact Submodule.subset_span (by simp)
  · exact Submodule.subset_span (by simp)
  · rw [conj_conj]; exact Submodule.subset_span (by simp)

end R18_Eb2

open DiazModulus R18_Eb2 in
theorem solution
    (v : ℂ) (hv : v ∉ Qbar) (hv1 : v * conj v = 1)
    (z a b c d : ℂ) (ha : a ∈ Qbar) (hb : b ∈ Qbar) (hc : c ∈ Qbar) (hd : d ∈ Qbar)
    (hz : z - (a * conj v ^ 3 + b * conj v ^ 2 + c * v ^ 2 + d * v ^ 3) ∈ Submodule.span Qbar ({1, v, conj v} : Set ℂ))
    (h5 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, v, conj v, z, conj z} : Set ℂ)) = 5) :
    (∃ e β ζ : ℂ, e ∈ Qbar ∧ β ∈ Qbar ∧ ζ ∈ Qbar ∧ e * conj e = 1 ∧ β * conj β = 1 ∧
        ζ = -(β * e ^ 2 * conj ζ) ∧
        Submodule.span Qbar ({1, v, conj v, z, conj z} : Set ℂ) =
          Submodule.span Qbar ({1, v, conj v, conj v ^ 2 + e * v ^ 2, β * conj v ^ 3 + ζ * v ^ 2 + e * v ^ 3} : Set ℂ)) ↔
      ((a * conj a - d * conj d) = 0 ∧ (a ≠ 0 ∨ d ≠ 0)) := by
  set m := a * conj v ^ 3 + b * conj v ^ 2 + c * v ^ 2 + d * v ^ 3 with hm
  have hmc : conj m = conj d * conj v ^ 3 + conj c * conj v ^ 2 + conj b * v ^ 2 +
      conj a * v ^ 3 := by
    rw [hm]; simp only [map_add, map_mul, map_pow, conj_conj]; ring
  have hW := span_swap hz (by have := conj_H0 hz; rwa [map_sub] at this)
  rw [hW] at h5 ⊢
  have hli := li_of_finrank h5
  constructor
  · rintro ⟨e, β, ζ, he, hβ, hζ, hee, hββ, -, hspan⟩
    have hmem : m ∈ Submodule.span Qbar ({1, v, conj v, conj v ^ 2 + e * v ^ 2,
        β * conj v ^ 3 + ζ * v ^ 2 + e * v ^ 3} : Set ℂ) := by
      rw [← hspan]; exact Submodule.subset_span (by simp)
    obtain ⟨x₀, x₁, x₂, x₃, x₄, e1⟩ := coeffs hmem
    rw [hm] at e1
    obtain ⟨h0, -, -, -, -, -, h6⟩ := coeff7 hv hv1 (c₀ := a - x₄ * β) (c₁ := b - x₃)
      (c₂ := -x₂) (c₃ := -x₀) (c₄ := -x₁) (c₅ := c - x₃ * e - x₄ * ζ) (c₆ := d - x₄ * e)
      (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb2.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb2.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb2.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb2.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb2.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb2.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb2.conj_mem | exact zero_mem _ | exact one_mem _))
      (by linear_combination e1)
    have h0c := congrArg conj h0
    have h6c := congrArg conj h6
    rw [map_sub, map_mul, map_zero] at h0c h6c
    refine ⟨by linear_combination conj a * h0 + x₄ * β * h0c - conj d * h6 - x₄ * e * h6c +
      x₄ * conj (x₄ : ℂ) * (hββ - hee), ?_⟩
    by_contra hcon
    push Not at hcon
    have hmem' : β * conj v ^ 3 + ζ * v ^ 2 + e * v ^ 3 ∈
        Submodule.span Qbar ({1, v, conj v, m, conj m} : Set ℂ) := by
      rw [hspan]; exact Submodule.subset_span (by simp)
    obtain ⟨y₀, y₁, y₂, y₃, y₄, e2⟩ := coeffs hmem'
    rw [hmc, hm] at e2
    obtain ⟨h0', -⟩ := coeff7 hv hv1 (c₀ := β - y₃ * a - y₄ * conj d)
      (c₁ := -(y₃ * b) - y₄ * conj c) (c₂ := -y₂) (c₃ := -y₀) (c₄ := -y₁)
      (c₅ := ζ - y₃ * c - y₄ * conj b) (c₆ := e - y₃ * d - y₄ * conj a)
      (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb2.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb2.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb2.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb2.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb2.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb2.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb2.conj_mem | exact zero_mem _ | exact one_mem _))
      (by linear_combination e2)
    rw [hcon.1, hcon.2] at h0'
    simp [show β = 0 by simpa using h0'] at hββ
  · rintro ⟨hN, had⟩
    have ha0 : a ≠ 0 := fun h0 => by
      have hd' : d = 0 := mul_conj_eq_zero (by rw [h0] at hN; linear_combination -hN)
      rcases had with h | h <;> contradiction
    have hd0 : d ≠ 0 := fun h0 => by
      have ha' : a = 0 := mul_conj_eq_zero (by rw [h0] at hN; linear_combination hN)
      rcases had with h | h <;> contradiction
    have hid : conj a * (a * conj b - c * conj d) = -(conj d * (conj a * c - conj b * d)) := by
      linear_combination conj b * hN
    have hp12c : conj (a * conj c - b * conj d) = conj a * c - conj b * d := by
      simp only [map_sub, map_mul, conj_conj]
    have hp12 : a * conj c - b * conj d ≠ 0 := by
      intro h0
      have h0c : conj a * c - conj b * d = 0 := by rw [← hp12c, h0, map_zero]
      have h13 : a * conj b - c * conj d = 0 := by
        have : conj a * (a * conj b - c * conj d) = 0 := by rw [hid, h0c]; ring
        exact (mul_eq_zero.1 this).resolve_left ((map_ne_zero _).2 ha0)
      have := li2 hli (x := -conj d) (y := a) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb2.conj_mem | exact zero_mem _ | exact one_mem _)) ha (by
        rw [hmc, hm]
        linear_combination conj v ^ 2 * h0 + v ^ 2 * h13 + v ^ 3 * hN)
      exact ha0 this.2
    have hp13 : a * conj b - c * conj d ≠ 0 := by
      intro h0
      rw [h0] at hid
      have : conj d * (conj a * c - conj b * d) = 0 := by linear_combination hid
      rcases mul_eq_zero.1 this with h | h
      · exact hd0 ((map_eq_zero _).1 h)
      · exact hp12 ((map_eq_zero conj).1 (by rw [hp12c, h]))
    obtain ⟨e, he, hpe⟩ : ∃ e ∈ Qbar, (a * conj c - b * conj d) * e = a * conj b - c * conj d :=
      ⟨_, div_mem (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb2.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb2.conj_mem | exact zero_mem _ | exact one_mem _)), mul_div_cancel₀ _ hp12⟩
    have he0 : e ≠ 0 := fun h0 => hp13 (by rw [← hpe, h0, mul_zero])
    obtain ⟨β, hβ, hβd⟩ : ∃ β ∈ Qbar, d * β = e * a :=
      ⟨_, div_mem (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb2.conj_mem | exact zero_mem _ | exact one_mem _)) hd, mul_div_cancel₀ _ hd0⟩
    obtain ⟨ζ, hζ, hζd⟩ : ∃ ζ ∈ Qbar, d * ζ = e * (c - b * e) :=
      ⟨_, div_mem (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb2.conj_mem | exact zero_mem _ | exact one_mem _)) hd, mul_div_cancel₀ _ hd0⟩
    have hβ0 : β ≠ 0 := fun h0 => mul_ne_zero he0 ha0 (by rw [← hβd, h0, mul_zero])
    set n0 := conj v ^ 2 + e * v ^ 2 with hn0
    set n1 := β * conj v ^ 3 + ζ * v ^ 2 + e * v ^ 3 with hn1
    have R1 : conj d * m - a * conj m = -(a * conj c - b * conj d) * n0 := by
      rw [hmc, hm, hn0]; linear_combination v ^ 2 * hpe - v ^ 3 * hN
    have R2 : d * n1 = e * (m - b * n0) := by
      rw [hm, hn0, hn1]; linear_combination conj v ^ 3 * hβd + v ^ 2 * hζd
    have hmS' : m ∈ Submodule.span Qbar ({1, v, conj v, n0, n1} : Set ℂ) := by
      convert mem5 (v := v) (t := conj v) (z := n0) (zc := n1) (zero_mem _) (zero_mem _)
        (zero_mem _) hb (x₄ := d * e⁻¹) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb2.conj_mem | exact zero_mem _ | exact one_mem _)) using 1
      linear_combination (-e⁻¹) * R2 - (m - b * n0) * mul_inv_cancel₀ he0
    have hmcS' : conj m ∈ Submodule.span Qbar ({1, v, conj v, n0, n1} : Set ℂ) := by
      convert Submodule.add_mem _ (span_mul_mem (c := a⁻¹ * conj d) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb2.conj_mem | exact zero_mem _ | exact one_mem _)) hmS')
        (span_mul_mem (c := a⁻¹ * (a * conj c - b * conj d)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb2.conj_mem | exact zero_mem _ | exact one_mem _))
          (Submodule.subset_span (by simp) :
            n0 ∈ Submodule.span Qbar ({1, v, conj v, n0, n1} : Set ℂ))) using 1
      linear_combination (-a⁻¹) * R1 - conj m * mul_inv_cancel₀ ha0
    have hn0S : n0 ∈ Submodule.span Qbar ({1, v, conj v, m, conj m} : Set ℂ) := by
      convert mem5 (v := v) (t := conj v) (z := m) (zc := conj m) (zero_mem _) (zero_mem _)
        (zero_mem _) (x₃ := -(a * conj c - b * conj d)⁻¹ * conj d)
        (x₄ := (a * conj c - b * conj d)⁻¹ * a) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb2.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb2.conj_mem | exact zero_mem _ | exact one_mem _)) using 1
      linear_combination (a * conj c - b * conj d)⁻¹ * R1 - n0 * mul_inv_cancel₀ hp12
    have hn1S : n1 ∈ Submodule.span Qbar ({1, v, conj v, m, conj m} : Set ℂ) := by
      convert Submodule.add_mem _ (span_mul_mem (c := d⁻¹ * e) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb2.conj_mem | exact zero_mem _ | exact one_mem _))
          (Submodule.subset_span (by simp) :
            m ∈ Submodule.span Qbar ({1, v, conj v, m, conj m} : Set ℂ)))
        (span_mul_mem (c := -(d⁻¹ * e * b)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb2.conj_mem | exact zero_mem _ | exact one_mem _)) hn0S) using 1
      linear_combination d⁻¹ * R2 - n1 * mul_inv_cancel₀ hd0
    have hS : Submodule.span Qbar ({1, v, conj v, m, conj m} : Set ℂ) =
        Submodule.span Qbar ({1, v, conj v, n0, n1} : Set ℂ) :=
      le_antisymm (span5_le hmS' hmcS') (span5_le hn0S hn1S)
    have hconj : ∀ w ∈ Submodule.span Qbar ({1, v, conj v, n0, n1} : Set ℂ),
        conj w ∈ Submodule.span Qbar ({1, v, conj v, n0, n1} : Set ℂ) := by
      rw [← hS]; exact W_conj
    obtain ⟨hee, hββ, hζe⟩ := DiazModulus.laurent_involution_space_conj_stable_constraints
      v hv hv1 e β ζ he hβ hζ hβ0 hconj
    exact ⟨e, β, ζ, he, hβ, hζ, hee, hββ, hζe, hS⟩
