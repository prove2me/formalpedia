-- Prove2me | solution 1 for DiazModulus.cubic_window_hull_real_pencil_class_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T14:40:53.017107+00:00
-- url     : https://prove2.me/submissions/be3487ca-be06-4ddb-9d67-92daeb4a4124

import Mathlib
import Definitions.Def_DiazModulus

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open Complex ComplexConjugate

/-! # The real pencil class of a cubic-window conjugation hull

Let `v ∉ Q̄`, `v v̄ = 1`, `z ≡ m := a v̄³ + b v̄² + c v² + d v³` modulo `span(1, v, v̄)`, so that
`W = span(1, v, v̄, m, m̄)`. Write `p₁₂ = ac̄ − bd̄` and `p₁₄ = aā − dd̄`. (The hypothesis
`dim W = 5` is not needed: `p₁₄ ≠ 0` already makes `m, m̄` free modulo `span(1, v, v̄)`.)
(→) Let `g = G(v) + κ conj(v G(v)) ∈ W`, `g = x₀ + x₁v + x₂v̄ + xm + ym̄`. Then
`G(v) − (x₀ + x₁v + f₂v² + f₃v³) = v̄ · conj(Q(v))` with `Q = x̄₂ + f̄₋₂X + f̄₋₃X² − κ̄G`, where
`f₋₃, f₋₂, f₂, f₃` are the coefficients of `xm + ym̄`. Multiplying by `v^(n+1)`, `n = deg Q`, the
left side has order `≥ n + 1` and the right side degree `≤ n`, so both vanish (transcendence).
Hence `G = x₀ + x₁X + f₂X² + f₃X³` and `κ̄G = x̄₂ + f̄₋₂X + f̄₋₃X²`: `f₃ = 0`, `f₋₃ = κ f̄₂`, and
`f₂ ≠ 0` since `deg G ≥ 2`. With `D = xx̄ − yȳ`, the Plücker identities give `D p₁₄ = f₂f̄₂ ≠ 0`
and `D p₁₂ = κ f̄₂²`, so `p₁₄ ≠ 0` and `p₁₂p̄₁₂ = p₁₄²`.
(←) `κ = p₁₄/p₁₂` has `κκ̄ = 1`. With `G = conj(āb − dc̄)κ X + conj(p₁₂) X²`,
`g = G₁v + (ām − dm̄)` and `ḡ = Ḡ₁v̄ + (am̄ − d̄m)`, and `det [[ā, −d], [−d̄, a]] = p₁₄ ≠ 0` gives
`W = span(1, v, v̄, g, ḡ)`.
-/

namespace R18_Eb3

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

/-- Conjugation on `Q̄`. -/
noncomputable def cj (x : ↥Qbar) : ↥Qbar := ⟨conj (x : ℂ), conj_mem x.2⟩

/-- Separation of positive and negative powers: `P(v) = v̄ · conj(Q(v))` forces `P = Q = 0`. -/
theorem sep {v : ℂ} (hv : v ∉ Qbar) (hv1 : v * conj v = 1) {P Q : (↥Qbar)[X]}
    (h : aeval v P = conj v * conj (aeval v Q)) : P = 0 ∧ Q = 0 := by
  set n := Q.natDegree
  set R : (↥Qbar)[X] := ∑ i ∈ Finset.range (n + 1), C (cj (Q.coeff i)) * X ^ (n - i) with hRdef
  have hR : aeval v R = v ^ n * conj (aeval v Q) := by
    rw [aeval_eq_sum_range (p := Q), hRdef]
    simp only [map_sum, map_mul, map_pow, aeval_C, aeval_X, am, Algebra.smul_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hvn : v ^ n = v ^ (n - i) * v ^ i := by rw [← pow_add, Nat.sub_add_cancel hi']
    have hpow : (v * conj v) ^ i = 1 := by rw [hv1, one_pow]
    show conj ((Q.coeff i : ↥Qbar) : ℂ) * v ^ (n - i) = _
    rw [hvn]
    linear_combination (-(conj ((Q.coeff i : ↥Qbar) : ℂ) * v ^ (n - i))) * hpow
  have hRd : R.natDegree ≤ n :=
    natDegree_sum_le_of_forall_le _ _ fun i _ => (natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le n i)
  have hXP : X ^ (n + 1) * P = R := by
    apply sub_eq_zero.1
    apply aeval_eq_zero hv
    rw [map_sub, map_mul, map_pow, aeval_X, hR, h]
    linear_combination (v ^ n * conj (aeval v Q)) * hv1
  have hP : P = 0 := by
    by_contra hP0
    have hd := natDegree_mul (pow_ne_zero (n + 1) (X_ne_zero : (X : (↥Qbar)[X]) ≠ 0)) hP0
    rw [hXP, natDegree_X_pow] at hd
    omega
  refine ⟨hP, aeval_eq_zero hv ?_⟩
  rw [hP, map_zero] at h
  have hcv : conj v ≠ 0 := fun h0 => by rw [h0, mul_zero] at hv1; exact zero_ne_one hv1
  exact (map_eq_zero _).1 ((mul_eq_zero.1 h.symm).resolve_left hcv)

end R18_Eb3

open DiazModulus R18_Eb3 Polynomial in
theorem solution
    (v : ℂ) (hv : v ∉ Qbar) (hv1 : v * conj v = 1)
    (z a b c d : ℂ) (ha : a ∈ Qbar) (hb : b ∈ Qbar) (hc : c ∈ Qbar) (hd : d ∈ Qbar)
    (hz : z - (a * conj v ^ 3 + b * conj v ^ 2 + c * v ^ 2 + d * v ^ 3) ∈ Submodule.span Qbar ({1, v, conj v} : Set ℂ)) :
    (∃ κ : ℂ, κ ∈ Qbar ∧ κ * conj κ = 1 ∧ ∃ G : Polynomial ↥Qbar, G.coeff 0 = 0 ∧ 2 ≤ G.natDegree ∧
        Submodule.span Qbar ({1, v, conj v, z, conj z} : Set ℂ) =
          Submodule.span Qbar ({1, v, conj v, Polynomial.aeval v G + κ * conj (v * Polynomial.aeval v G), conj (Polynomial.aeval v G + κ * conj (v * Polynomial.aeval v G))} : Set ℂ)) ↔
      ((a * conj c - b * conj d) * conj (a * conj c - b * conj d) = (a * conj a - d * conj d) ^ 2 ∧ (a * conj a - d * conj d) ≠ 0) := by
  set m := a * conj v ^ 3 + b * conj v ^ 2 + c * v ^ 2 + d * v ^ 3 with hm
  have hmc : conj m = conj d * conj v ^ 3 + conj c * conj v ^ 2 + conj b * v ^ 2 +
      conj a * v ^ 3 := by
    rw [hm]; simp only [map_add, map_mul, map_pow, conj_conj]; ring
  have hW := span_swap hz (by have := conj_H0 hz; rwa [map_sub] at this)
  rw [hW]
  constructor
  · rintro ⟨κ, hκ, hκκ, G, hG0, hG2, hspan⟩
    have hgW : aeval v G + κ * conj (v * aeval v G) ∈
        Submodule.span Qbar ({1, v, conj v, m, conj m} : Set ℂ) := by
      rw [hspan]; exact Submodule.subset_span (by simp)
    obtain ⟨x₀, x₁, x₂, x, y, e1⟩ := coeffs hgW
    rw [hmc, hm, map_mul] at e1
    obtain ⟨F₂, hF₂⟩ : ∃ q : ↥Qbar, (q : ℂ) = x * c + y * conj b := ⟨⟨_, by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb3.conj_mem | exact zero_mem _ | exact one_mem _)⟩, rfl⟩
    obtain ⟨F₃, hF₃⟩ : ∃ q : ↥Qbar, (q : ℂ) = x * d + y * conj a := ⟨⟨_, by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb3.conj_mem | exact zero_mem _ | exact one_mem _)⟩, rfl⟩
    obtain ⟨Y₀, hY₀⟩ : ∃ q : ↥Qbar, (q : ℂ) = conj (x₂ : ℂ) := ⟨⟨_, by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb3.conj_mem | exact zero_mem _ | exact one_mem _)⟩, rfl⟩
    obtain ⟨Y₁, hY₁⟩ : ∃ q : ↥Qbar, (q : ℂ) = conj ((x : ℂ) * b + y * conj c) :=
      ⟨⟨_, by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb3.conj_mem | exact zero_mem _ | exact one_mem _)⟩, rfl⟩
    obtain ⟨Y₂, hY₂⟩ : ∃ q : ↥Qbar, (q : ℂ) = conj ((x : ℂ) * a + y * conj d) :=
      ⟨⟨_, by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb3.conj_mem | exact zero_mem _ | exact one_mem _)⟩, rfl⟩
    obtain ⟨K, hK⟩ : ∃ q : ↥Qbar, (q : ℂ) = conj κ := ⟨⟨_, by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb3.conj_mem | exact zero_mem _ | exact one_mem _)⟩, rfl⟩
    obtain ⟨hP, hQ⟩ := sep hv hv1 (P := G - (C x₀ + C x₁ * X + C F₂ * X ^ 2 + C F₃ * X ^ 3))
      (Q := C Y₀ + C Y₁ * X + C Y₂ * X ^ 2 - C K * G) (by
        simp only [map_sub, map_add, map_mul, map_pow, aeval_C, aeval_X, am, hF₂, hF₃, hY₀, hY₁,
          hY₂, hK, conj_conj]
        linear_combination e1)
    have hGe : G = C x₀ + C x₁ * X + C F₂ * X ^ 2 + C F₃ * X ^ 3 := sub_eq_zero.1 hP
    rw [hGe] at hQ
    have q2 := congrArg (coeff · 2) hQ
    have q3 := congrArg (coeff · 3) hQ
    simp [coeff_X_pow] at q2 q3
    have hκ0 : κ ≠ 0 := fun h0 => by rw [h0, zero_mul] at hκκ; exact zero_ne_one hκκ
    have hK0 : K ≠ 0 := fun h0 => hκ0 ((map_eq_zero _).1 (by rw [← hK, h0]; rfl))
    have hF30 : F₃ = 0 := q3.resolve_left hK0
    have ht3 : (x : ℂ) * d + y * conj a = 0 := by rw [← hF₃, hF30]; rfl
    have hs3c : conj ((x : ℂ) * a + y * conj d) = conj κ * (x * c + y * conj b) := by
      rw [← hY₂, ← hK, ← hF₂]; exact congrArg Subtype.val (sub_eq_zero.1 q2)
    have hF20 : F₂ ≠ 0 := by
      intro h0
      simp only [h0, hF30, map_zero, zero_mul, add_zero] at hGe
      have : G.natDegree ≤ 1 := by rw [hGe, add_comm]; exact natDegree_linear_le
      omega
    have ht2 : (x : ℂ) * c + y * conj b ≠ 0 := by
      rw [← hF₂]; exact fun h0 => hF20 (Subtype.ext h0)
    have hs3c' : conj (x : ℂ) * conj a + conj (y : ℂ) * d = conj κ * (x * c + y * conj b) := by
      rw [← hs3c]; simp only [map_add, map_mul, conj_conj]
    have hs3 : (x : ℂ) * a + y * conj d = κ * (conj (x : ℂ) * conj c + conj (y : ℂ) * b) := by
      simpa only [map_add, map_mul, conj_conj] using congrArg conj hs3c'
    have ht3c : conj (x : ℂ) * conj d + conj (y : ℂ) * a = 0 := by
      simpa only [map_add, map_mul, conj_conj, map_zero] using congrArg conj ht3
    have hD14 : (x * conj (x : ℂ) - y * conj (y : ℂ)) * (a * conj a - d * conj d) =
        (x * c + y * conj b) * (conj (x : ℂ) * conj c + conj (y : ℂ) * b) := by
      linear_combination (conj (x : ℂ) * conj a + conj (y : ℂ) * d) * hs3 +
        κ * (conj (x : ℂ) * conj c + conj (y : ℂ) * b) * hs3c' -
        (conj (x : ℂ) * conj d + conj (y : ℂ) * a) * ht3 +
        (conj (x : ℂ) * conj c + conj (y : ℂ) * b) * (x * c + y * conj b) * hκκ
    have hD12 : (x * conj (x : ℂ) - y * conj (y : ℂ)) * (a * conj c - b * conj d) =
        κ * (conj (x : ℂ) * conj c + conj (y : ℂ) * b) ^ 2 := by
      linear_combination (conj (x : ℂ) * conj c + conj (y : ℂ) * b) * hs3 -
        (x * b + y * conj c) * ht3c
    have hD12c : (x * conj (x : ℂ) - y * conj (y : ℂ)) * (conj a * c - conj b * d) =
        conj κ * (x * c + y * conj b) ^ 2 := by
      have := congrArg conj hD12
      simp only [map_mul, map_sub, map_add, map_pow, conj_conj] at this
      linear_combination this
    have hD0 : (x * conj (x : ℂ) - y * conj (y : ℂ)) * (a * conj a - d * conj d) ≠ 0 := by
      rw [hD14]
      exact fun h0 => ht2 (mul_conj_eq_zero (by simpa only [map_add, map_mul, conj_conj] using h0))
    refine ⟨?_, right_ne_zero_of_mul hD0⟩
    have hD : (x * conj (x : ℂ) - y * conj (y : ℂ)) ≠ 0 := left_ne_zero_of_mul hD0
    have key : (x * conj (x : ℂ) - y * conj (y : ℂ)) ^ 2 * ((a * conj c - b * conj d) *
        (conj a * c - conj b * d) - (a * conj a - d * conj d) ^ 2) = 0 := by
      linear_combination ((x * conj (x : ℂ) - y * conj (y : ℂ)) * (conj a * c - conj b * d)) * hD12 +
        κ * (conj (x : ℂ) * conj c + conj (y : ℂ) * b) ^ 2 * hD12c -
        ((x * conj (x : ℂ) - y * conj (y : ℂ)) * (a * conj a - d * conj d) +
          (x * c + y * conj b) * (conj (x : ℂ) * conj c + conj (y : ℂ) * b)) * hD14 +
        (x * c + y * conj b) ^ 2 * (conj (x : ℂ) * conj c + conj (y : ℂ) * b) ^ 2 * hκκ
    rw [show conj (a * conj c - b * conj d) = conj a * c - conj b * d by
      simp only [map_sub, map_mul, conj_conj]]
    exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_left (pow_ne_zero 2 hD))
  · rintro ⟨h12, h14⟩
    have hp12c : conj (a * conj c - b * conj d) = conj a * c - conj b * d := by
      simp only [map_sub, map_mul, conj_conj]
    rw [hp12c] at h12
    have hp12 : a * conj c - b * conj d ≠ 0 := fun h0 => h14 ((pow_eq_zero_iff two_ne_zero).1
      (by rw [← h12, h0, zero_mul]))
    have hp12' : conj a * c - conj b * d ≠ 0 := by
      rw [← hp12c]; exact (_root_.map_ne_zero _).2 hp12
    obtain ⟨κ, hκ, hκd⟩ : ∃ κ ∈ Qbar, (a * conj c - b * conj d) * κ = a * conj a - d * conj d :=
      ⟨_, div_mem (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb3.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb3.conj_mem | exact zero_mem _ | exact one_mem _)), mul_div_cancel₀ _ hp12⟩
    have hκdc : (conj a * c - conj b * d) * conj κ = a * conj a - d * conj d := by
      have := congrArg conj hκd
      simp only [map_mul, map_sub, conj_conj] at this
      linear_combination this
    have hκκ : κ * conj κ = 1 := by
      have h : ((a * conj c - b * conj d) * (conj a * c - conj b * d)) * (κ * conj κ - 1) = 0 := by
        linear_combination ((conj a * c - conj b * d) * conj κ) * hκd +
          (a * conj a - d * conj d) * hκdc - h12
      exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left (mul_ne_zero hp12 hp12'))
    obtain ⟨G1, hG1⟩ : ∃ q : ↥Qbar, (q : ℂ) = (a * conj b - conj d * c) * κ :=
      ⟨⟨_, by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb3.conj_mem | exact zero_mem _ | exact one_mem _)⟩, rfl⟩
    obtain ⟨G2, hG2⟩ : ∃ q : ↥Qbar, (q : ℂ) = conj a * c - conj b * d := ⟨⟨_, by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb3.conj_mem | exact zero_mem _ | exact one_mem _)⟩, rfl⟩
    have hG20 : G2 ≠ 0 := fun h0 => hp12' (by rw [← hG2, h0]; rfl)
    refine ⟨κ, hκ, hκκ, C G1 * X + C G2 * X ^ 2, by simp,
      le_natDegree_of_ne_zero (by simpa using hG20), ?_⟩
    have hg : aeval v (C G1 * X + C G2 * X ^ 2) + κ * conj (v * aeval v (C G1 * X + C G2 * X ^ 2)) =
        (G1 : ℂ) * v + (conj a * m - d * conj m) := by
      simp only [map_add, map_mul, map_pow, map_sub, aeval_C, aeval_X, am, hG1, hG2, conj_conj]
      rw [hmc, hm]
      linear_combination ((conj a * b - d * conj c) * conj v ^ 2) * hκκ + conj v ^ 3 * hκd
    rw [hg]
    have hgc : conj ((G1 : ℂ) * v + (conj a * m - d * conj m)) =
        conj (G1 : ℂ) * conj v + (a * conj m - conj d * m) := by
      simp only [map_add, map_sub, map_mul, conj_conj]
    rw [hgc]
    have hp14i : (a * conj a - d * conj d) * (a * conj a - d * conj d)⁻¹ = 1 := mul_inv_cancel₀ h14
    have hmS : m ∈ Submodule.span Qbar ({1, v, conj v, (G1 : ℂ) * v + (conj a * m - d * conj m),
        conj (G1 : ℂ) * conj v + (a * conj m - conj d * m)} : Set ℂ) := by
      convert mem5 (x₀ := 0) (x₁ := -((a * conj a - d * conj d)⁻¹ * a * G1))
        (x₂ := -((a * conj a - d * conj d)⁻¹ * d * conj (G1 : ℂ)))
        (x₃ := (a * conj a - d * conj d)⁻¹ * a) (x₄ := (a * conj a - d * conj d)⁻¹ * d)
        (zero_mem _) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb3.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb3.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb3.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb3.conj_mem | exact zero_mem _ | exact one_mem _)) using 1
      linear_combination (-m) * hp14i
    have hmcS : conj m ∈ Submodule.span Qbar ({1, v, conj v, (G1 : ℂ) * v +
        (conj a * m - d * conj m), conj (G1 : ℂ) * conj v + (a * conj m - conj d * m)} : Set ℂ) := by
      convert mem5 (x₀ := 0) (x₁ := -((a * conj a - d * conj d)⁻¹ * conj d * G1))
        (x₂ := -((a * conj a - d * conj d)⁻¹ * conj a * conj (G1 : ℂ)))
        (x₃ := (a * conj a - d * conj d)⁻¹ * conj d) (x₄ := (a * conj a - d * conj d)⁻¹ * conj a)
        (zero_mem _) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb3.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb3.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb3.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb3.conj_mem | exact zero_mem _ | exact one_mem _)) using 1
      linear_combination (-conj m) * hp14i
    have hgS : (G1 : ℂ) * v + (conj a * m - d * conj m) ∈
        Submodule.span Qbar ({1, v, conj v, m, conj m} : Set ℂ) := by
      convert mem5 (x₀ := 0) (x₁ := G1) (x₂ := 0) (x₃ := conj a) (x₄ := -d) (zero_mem _)
        (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb3.conj_mem | exact zero_mem _ | exact one_mem _)) (zero_mem _) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb3.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb3.conj_mem | exact zero_mem _ | exact one_mem _)) using 1
      ring
    have hgcS : conj (G1 : ℂ) * conj v + (a * conj m - conj d * m) ∈
        Submodule.span Qbar ({1, v, conj v, m, conj m} : Set ℂ) := by
      convert mem5 (x₀ := 0) (x₁ := 0) (x₂ := conj (G1 : ℂ)) (x₃ := -conj d) (x₄ := a)
        (zero_mem _) (zero_mem _) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb3.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb3.conj_mem | exact zero_mem _ | exact one_mem _)) (by repeat' (first | assumption | exact SetLike.coe_mem _ | apply div_mem | apply inv_mem | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem | apply R18_Eb3.conj_mem | exact zero_mem _ | exact one_mem _)) using 1
      ring
    exact le_antisymm (span5_le hmS hmcS) (span5_le hgS hgcS)
