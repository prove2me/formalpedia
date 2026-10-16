-- Prove2me | solution 1 for DiazModulus.cyclic_pair_configuration_invisible_to_four_dimensional_extensions
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-15T11:59:40.064742+00:00
-- url     : https://prove2.me/submissions/53713363-33b4-4317-b3ec-a1e9984b360a

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_cyclic_pair_space_excludes_squares_and_reciprocals
import Theorems.Thm_DiazModulus_circle_point_extension_two_by_three_configuration_iff

open Complex ComplexConjugate

/-! # The cyclic pair configuration needs the whole space

Let `u ∉ Q̄`, `s ∈ Q̄` real with `s² = u ū`, `G₁ = s/(u − s) + 2s/(u + s)`,
`G₂ = s²/(u − s)² + s/(u − s) − 2s²/(u + s)² + 2s/(u + s)`, `W = span_Q̄ {1, u, ū, G₁, G₂}` and
`H₀ = Q̄ + Q̄u + Q̄ū`. For `z = u` and `z = ū` (both `≠ ±s`): `G₁(z)(z² − s²) = s(3z − s)` and
`G₂(z)(z² − s²)² = s z (3z² − 2sz + 3s²)`.

* Conjugation: `Ḡ₁ = 1 − G₁` and `Ḡ₂ = G₂` (clear denominators, reduce modulo `ū u − s²`); by
  induction on the span, `W̄ ⊆ W`.
* Configuration `x = (1, u²)`, `y = (ū, G₁, G₂)`: the products `ū`, `G₁`, `G₂`, `u²ū = s²u`,
  `u²G₁ = 3su − s² + s²G₁`, `u²G₂ = s²G₂ + 3su − 2s² + 2s²G₁` lie in `W` and give back its five
  generators; `x`, `y` are free by `cyclic_pair_space_excludes_squares_and_reciprocals`.
* Invisibility: by Theorem B (`circle_point_extension_two_by_three_configuration_iff`) a
  configuration in `H₀ + Q̄w`, `w ∈ W \ H₀`, puts `w` in `H₀ + Q̄t` with `t = u²`, `ū²` or `(u − e)⁻¹`;
  exchange puts `t` in `H₀ + Q̄w ≤ W`, which that node excludes.
-/

namespace R15_cyclicInvisible

open DiazModulus

/-- Complex conjugation as a `ℚ`-algebra map. -/
noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

/-- Conjugation maps `Q̄` to itself. -/
theorem conj_mem_Qbar {a : ℂ} (ha : a ∈ Qbar) : conj a ∈ Qbar := by
  obtain ⟨p, hp0, hp⟩ := mem_Qbar_iff.1 ha
  refine mem_Qbar_iff.2 ⟨p, hp0, ?_⟩
  rw [show (conj a : ℂ) = cjQ a from rfl, Polynomial.aeval_algHom_apply, hp, map_zero]

theorem span_mul_mem {S : Set ℂ} {c v : ℂ} (hc : c ∈ Qbar) (hv : v ∈ Submodule.span Qbar S) :
    c * v ∈ Submodule.span Qbar S := by
  have := Submodule.smul_mem _ (⟨c, hc⟩ : ↥Qbar) hv
  rwa [Subfield.smul_def, smul_eq_mul] at this

theorem span_mem_of_eq {S : Set ℂ} {v z : ℂ} (h : v = z) (hz : z ∈ Submodule.span Qbar S) :
    v ∈ Submodule.span Qbar S := by
  rwa [h]

/-- A span whose generators have conjugates in it is conjugation-stable. -/
theorem span_conj_stable {S : Set ℂ} (hS : ∀ x ∈ S, conj x ∈ Submodule.span Qbar S) :
    ∀ w ∈ Submodule.span Qbar S, conj w ∈ Submodule.span Qbar S := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have hcx : conj (c • x) = (⟨conj (c : ℂ), conj_mem_Qbar c.2⟩ : ↥Qbar) • conj x :=
      map_mul conj (c : ℂ) x
    rw [hcx]
    exact Submodule.smul_mem _ _ hx

theorem set_eq_insert (u w : ℂ) : ({1, u, conj u, w} : Set ℂ) = insert w {1, u, conj u} := by
  ext t
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- Exchange: `w ∉ H₀` and `w ∈ H₀ + Q̄t` give `t ∈ H₀ + Q̄w`. -/
theorem exchange {u t w : ℂ} (hw : w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ))
    (h : w ∈ Submodule.span Qbar ({1, u, conj u, t} : Set ℂ)) :
    t ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) := by
  rw [set_eq_insert] at h ⊢
  exact mem_span_insert_exchange h hw

/-- `H₀ + Q̄w ≤ W` for `w ∈ W`, when `W` is spanned by `1, u, ū` and two more numbers. -/
theorem span_four_le {u w f g : ℂ}
    (hw : w ∈ Submodule.span Qbar ({1, u, conj u, f, g} : Set ℂ)) :
    Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) ≤
      Submodule.span Qbar ({1, u, conj u, f, g} : Set ℂ) := by
  refine Submodule.span_le.2 fun x hx => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact Submodule.subset_span (by simp)
  · exact Submodule.subset_span (by simp)
  · exact Submodule.subset_span (by simp)
  · exact hw

/-- `G₁` at `x`, denominators cleared. -/
theorem G₁_id {x s : ℂ} (hm : x - s ≠ 0) (hp : x + s ≠ 0) :
    (s / (x - s) + 2 * s / (x + s)) * (x ^ 2 - s ^ 2) = s * (3 * x - s) := by
  field_simp
  ring

/-- `G₂` at `x`, denominators cleared. -/
theorem G₂_id {x s : ℂ} (hm : x - s ≠ 0) (hp : x + s ≠ 0) :
    (s * s / (x - s) ^ 2 + s / (x - s) - 2 * (s * s) / (x + s) ^ 2 + 2 * s / (x + s)) *
      (x ^ 2 - s ^ 2) ^ 2 = s * x * (3 * x ^ 2 - 2 * s * x + 3 * s ^ 2) := by
  field_simp
  ring

end R15_cyclicInvisible

open DiazModulus R15_cyclicInvisible in
theorem solution
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u) :
    (∀ w ∈ Submodule.span Qbar ({1, u, conj u, (s / (u - s) + 2 * s / (u + s)), (s * s / (u - s) ^ 2 + s / (u - s) - 2 * (s * s) / (u + s) ^ 2 + 2 * s / (u + s))} : Set ℂ), conj w ∈ Submodule.span Qbar ({1, u, conj u, (s / (u - s) + 2 * s / (u + s)), (s * s / (u - s) ^ 2 + s / (u - s) - 2 * (s * s) / (u + s) ^ 2 + 2 * s / (u + s))} : Set ℂ)) ∧
      (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
        (∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, (s / (u - s) + 2 * s / (u + s)), (s * s / (u - s) ^ 2 + s / (u - s) - 2 * (s * s) / (u + s) ^ 2 + 2 * s / (u + s))} : Set ℂ)) ∧
        Submodule.span Qbar (Set.range (fun p : Fin 2 × Fin 3 => x p.1 * y p.2)) = Submodule.span Qbar ({1, u, conj u, (s / (u - s) + 2 * s / (u + s)), (s * s / (u - s) ^ 2 + s / (u - s) - 2 * (s * s) / (u + s) ^ 2 + 2 * s / (u + s))} : Set ℂ)) ∧
      ∀ w ∈ Submodule.span Qbar ({1, u, conj u, (s / (u - s) + 2 * s / (u + s)), (s * s / (u - s) ^ 2 + s / (u - s) - 2 * (s * s) / (u + s) ^ 2 + 2 * s / (u + s))} : Set ℂ), w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) →
        ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Subfield.zero_mem _)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hu0 ((map_ne_zero _).2 hu0) (by rw [← hss]; ring)
  have hm : u - s ≠ 0 := sub_ne_zero.2 fun e => hu (by rw [e]; exact hs)
  have hp : u + s ≠ 0 := fun e => hu (by rw [eq_neg_of_add_eq_zero_left e]; exact neg_mem hs)
  have hcm : conj u - s ≠ 0 := fun e => hm (by
    have := congrArg conj (sub_eq_zero.1 e)
    rw [conj_conj, hsr] at this
    rw [this, sub_self])
  have hcp : conj u + s ≠ 0 := fun e => hp (by
    have := congrArg conj (eq_neg_of_add_eq_zero_left e)
    rw [conj_conj, map_neg, hsr] at this
    rw [this, neg_add_cancel])
  have hU : u ^ 2 - s ^ 2 ≠ 0 := by
    rw [show u ^ 2 - s ^ 2 = (u - s) * (u + s) by ring]; exact mul_ne_zero hm hp
  have hA : conj u ^ 2 - s ^ 2 ≠ 0 := by
    rw [show conj u ^ 2 - s ^ 2 = (conj u - s) * (conj u + s) by ring]; exact mul_ne_zero hcm hcp
  obtain ⟨hind, hsq, hcsq, hinv⟩ :=
    DiazModulus.cyclic_pair_space_excludes_squares_and_reciprocals u s hu hs hsr hss
  set G₁ := s / (u - s) + 2 * s / (u + s) with hG1def
  set G₂ := s * s / (u - s) ^ 2 + s / (u - s) - 2 * (s * s) / (u + s) ^ 2 + 2 * s / (u + s)
    with hG2def
  set W := Submodule.span Qbar ({1, u, conj u, G₁, G₂} : Set ℂ) with hW
  have m1 : (1 : ℂ) ∈ W := Submodule.subset_span (by simp)
  have mu : u ∈ W := Submodule.subset_span (by simp)
  have mcu : conj u ∈ W := Submodule.subset_span (by simp)
  have mG₁ : G₁ ∈ W := Submodule.subset_span (by simp)
  have mG₂ : G₂ ∈ W := Submodule.subset_span (by simp)
  have hG₁ : G₁ * (u ^ 2 - s ^ 2) = s * (3 * u - s) := G₁_id hm hp
  have hG₂ : G₂ * (u ^ 2 - s ^ 2) ^ 2 = s * u * (3 * u ^ 2 - 2 * s * u + 3 * s ^ 2) :=
    G₂_id hm hp
  -- conjugation stability
  have hH₁ : conj G₁ * (conj u ^ 2 - s ^ 2) = s * (3 * conj u - s) := by
    rw [hG1def]
    simp only [map_add, map_div₀, map_sub, map_mul, map_ofNat, hsr]
    exact G₁_id hcm hcp
  have hH₂ : conj G₂ * (conj u ^ 2 - s ^ 2) ^ 2 =
      s * conj u * (3 * conj u ^ 2 - 2 * s * conj u + 3 * s ^ 2) := by
    rw [hG2def]
    simp only [map_add, map_div₀, map_sub, map_mul, map_pow, map_ofNat, hsr]
    exact G₂_id hcm hcp
  have hcG₁ : conj G₁ = 1 - G₁ := by
    have key : (conj G₁ - (1 - G₁)) * ((conj u ^ 2 - s ^ 2) * (u ^ 2 - s ^ 2)) = 0 := by
      linear_combination (u ^ 2 - s ^ 2) * hH₁ + (conj u ^ 2 - s ^ 2) * hG₁ +
        (conj u * u - 3 * conj u * s - 3 * s * u + s ^ 2) * hss
    exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_right (mul_ne_zero hA hU))
  have hcG₂ : conj G₂ = G₂ := by
    have key : (conj G₂ - G₂) * ((conj u ^ 2 - s ^ 2) ^ 2 * (u ^ 2 - s ^ 2) ^ 2) = 0 := by
      linear_combination (u ^ 2 - s ^ 2) ^ 2 * hH₂ - (conj u ^ 2 - s ^ 2) ^ 2 * hG₂ -
        s * (u - conj u) * (3 * conj u ^ 2 * s ^ 2 - 2 * conj u ^ 2 * s * u +
          3 * conj u ^ 2 * u ^ 2 - 2 * conj u * s ^ 3 + 12 * conj u * s ^ 2 * u -
          2 * conj u * s * u ^ 2 + 3 * s ^ 4 - 2 * s ^ 3 * u + 3 * s ^ 2 * u ^ 2) * hss
    exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_right
      (mul_ne_zero (pow_ne_zero 2 hA) (pow_ne_zero 2 hU)))
  refine ⟨span_conj_stable ?_, ?_, ?_⟩
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · rw [map_one]; exact m1
    · exact mcu
    · rw [conj_conj]; exact mu
    · rw [hcG₁]; exact Submodule.sub_mem _ m1 mG₁
    · rw [hcG₂]; exact mG₂
  -- the configuration
  · have hind' := Fintype.linearIndependent_iff.1 hind
    have p10 : u ^ 2 * conj u = s * s * u := by linear_combination -u * hss
    have p11 : u ^ 2 * G₁ = 3 * s * u - s * s + s * s * G₁ := by linear_combination hG₁
    have p12 : u ^ 2 * G₂ = s * s * G₂ + 3 * s * u - 2 * (s * s) + 2 * (s * s) * G₁ := by
      have key : (u ^ 2 * G₂ - (s * s * G₂ + 3 * s * u - 2 * (s * s) + 2 * (s * s) * G₁)) *
          (u ^ 2 - s ^ 2) = 0 := by
        linear_combination hG₂ - 2 * s ^ 2 * hG₁
      exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_right hU)
    have h3 : (3 : ℂ) * s ∈ Qbar := mul_mem (ofNat_mem Qbar 3) hs
    have h2 : (2 : ℂ) * (s * s) ∈ Qbar := mul_mem (ofNat_mem Qbar 2) (mul_mem hs hs)
    have mem : ∀ i j, ![1, u ^ 2] i * ![conj u, G₁, G₂] j ∈ W := by
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using mcu
      · simpa using mG₁
      · simpa using mG₂
      · simpa [p10] using span_mul_mem (mul_mem hs hs) mu
      · exact span_mem_of_eq (show u ^ 2 * G₁ = 3 * s * u + (-(s * s)) * 1 + s * s * G₁ by
          rw [p11]; ring) (Submodule.add_mem _ (Submodule.add_mem _ (span_mul_mem h3 mu)
            (span_mul_mem (neg_mem (mul_mem hs hs)) m1)) (span_mul_mem (mul_mem hs hs) mG₁))
      · exact span_mem_of_eq (show u ^ 2 * G₂ = s * s * G₂ + 3 * s * u +
          (-(2 * (s * s))) * 1 + 2 * (s * s) * G₁ by rw [p12]; ring)
          (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
            (span_mul_mem (mul_mem hs hs) mG₂) (span_mul_mem h3 mu))
            (span_mul_mem (neg_mem h2) m1)) (span_mul_mem h2 mG₁))
    refine ⟨![1, u ^ 2], ![conj u, G₁, G₂], ?_, ?_, mem, ?_⟩
    · rw [Fintype.linearIndependent_iff]
      intro c hc
      simp only [Fin.sum_univ_two, Subfield.smul_def, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one, mul_one] at hc
      have hc1 : c 1 = 0 := by
        by_contra h1
        have h1' : (c 1 : ℂ) ≠ 0 := fun h => h1 (Subtype.ext h)
        apply hsq
        have : u ^ 2 = (-(c 0 : ℂ) / c 1) * 1 := by field_simp; linear_combination hc
        rw [this]
        exact span_mul_mem (div_mem (neg_mem (c 0).2) (c 1).2) m1
      have hc0 : c 0 = 0 := by
        rw [hc1] at hc
        exact Subtype.ext (by simpa using hc)
      intro i
      fin_cases i
      · exact hc0
      · exact hc1
    · rw [Fintype.linearIndependent_iff]
      intro c hc
      have := hind' ![0, 0, c 0, c 1, c 2] (by
        simp only [Fin.sum_univ_three, Subfield.smul_def, smul_eq_mul, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hc
        simp only [Fin.sum_univ_five, Subfield.smul_def, smul_eq_mul]
        simp
        linear_combination hc)
      have e2 := this 2
      have e3 := this 3
      have e4 := this 4
      simp at e2 e3 e4
      intro i
      fin_cases i
      · exact e2
      · exact e3
      · exact e4
    · refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
      · rintro _ ⟨⟨i, j⟩, rfl⟩
        exact mem i j
      · set P := Submodule.span Qbar (Set.range (fun p : Fin 2 × Fin 3 =>
          ![1, u ^ 2] p.1 * ![conj u, G₁, G₂] p.2)) with hP
        have pr : ∀ i j, ![1, u ^ 2] i * ![conj u, G₁, G₂] j ∈ P :=
          fun i j => Submodule.subset_span ⟨(i, j), rfl⟩
        have q00 := pr 0 0
        have q01 := pr 0 1
        have q02 := pr 0 2
        have q10 := pr 1 0
        have q11 := pr 1 1
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, one_mul] at q00 q01 q02 q10 q11
        have qu : u ∈ P := span_mem_of_eq
          (show u = (s * s)⁻¹ * (u ^ 2 * conj u) by rw [p10]; field_simp)
          (span_mul_mem (inv_mem (mul_mem hs hs)) q10)
        have q1 : (1 : ℂ) ∈ P := span_mem_of_eq
          (show (1 : ℂ) = (s * s)⁻¹ * (3 * s) * u + G₁ + (-(s * s)⁻¹) * (u ^ 2 * G₁) by
            rw [p11]; field_simp; ring)
          (Submodule.add_mem _ (Submodule.add_mem _
            (span_mul_mem (mul_mem (inv_mem (mul_mem hs hs)) h3) qu) q01)
            (span_mul_mem (neg_mem (inv_mem (mul_mem hs hs))) q11))
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        exacts [q1, qu, q00, q01, q02]
  -- invisibility
  · intro w hw hw0 hconfw
    have hρ : IsAlgebraic ℚ (u * conj u) := mem_Qbar_iff.1 (by rw [← hss]; exact mul_mem hs hs)
    have hle := span_four_le hw
    rcases (DiazModulus.circle_point_extension_two_by_three_configuration_iff u w hu hρ hw0).1
      hconfw with h | h | ⟨b, hb, hb0, h⟩
    · exact hsq (hle (exchange hw0 h))
    · exact hcsq (hle (exchange hw0 h))
    · exact hinv b hb hb0 (hle (exchange hw0 h))
