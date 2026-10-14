-- Prove2me | solution 1 for DiazModulus.laurent_cubic_configuration_invisible_to_four_dimensional_extensions
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T07:31:23.904045+00:00
-- url     : https://prove2.me/submissions/18b8e9fd-8343-4da9-845d-16b6c0c5db05

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_laurent_cubic_space_excludes_squares_and_reciprocals
import Theorems.Thm_DiazModulus_circle_point_extension_two_by_three_configuration_iff

open Complex ComplexConjugate

/-! # The Laurent cubic configuration needs the whole space

Let `u ∉ Q̄`, `s ∈ Q̄` real with `s² = u ū`, `F = u³/s³ + u²/s²`, `G = ū³/s³ + ū²/s²`,
`W₁ = span_Q̄ {1, u, ū, F, G}` and `H₀ = Q̄ + Q̄u + Q̄ū`. Then `u ≠ 0`, `s ≠ 0`, `F s³ = u³ + s u²`
and `u² G = s ū + s²` (from `ū u = s²`).

* Conjugation: `s̄ = s` gives `F̄ = G` and `Ḡ = F`; with `ū ↦ u` the generators go into `W₁`, and
  conjugation maps `q • w` to `q̄ • w̄` with `q̄ ∈ Q̄`, so by induction on the span `W̄₁ ⊆ W₁`.
* Configuration: `x = (1, u²)`, `y = (ū, u + s, G)`. The products are `ū`, `u + s`, `G`,
  `u² ū = s² u`, `u²(u + s) = s³ F` and `u² G = s ū + s²`, all in `W₁`, and they give back
  `1, u, ū, F, G`, so they span `W₁`. `x` is free because `u² ∉ W₁`, and `y` is free because a
  relation `a ū + b (u + s) + c G = 0` is one among the five free generators
  (`laurent_cubic_space_excludes_squares_and_reciprocals`).
* No `H₀ + Q̄w` with `w ∈ W₁ \ H₀` carries one: by Theorem B
  (`circle_point_extension_two_by_three_configuration_iff`, `u ū = s²` algebraic) a configuration
  there puts `w` in `H₀ + Q̄t` with `t = u²`, `ū²` or `(u − b)⁻¹`, `b ∈ Q̄ \ {0}`; exchange puts `t`
  in `H₀ + Q̄w ≤ W₁`, against `laurent_cubic_space_excludes_squares_and_reciprocals`.
-/

namespace R14_cubicInvisible

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

end R14_cubicInvisible

open DiazModulus R14_cubicInvisible in
theorem solution
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u) :
    (∀ w ∈ Submodule.span Qbar ({1, u, conj u, (u ^ 3 / (s * s * s) + u ^ 2 / (s * s)), (conj u ^ 3 / (s * s * s) + conj u ^ 2 / (s * s))} : Set ℂ), conj w ∈ Submodule.span Qbar ({1, u, conj u, (u ^ 3 / (s * s * s) + u ^ 2 / (s * s)), (conj u ^ 3 / (s * s * s) + conj u ^ 2 / (s * s))} : Set ℂ)) ∧
      (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
        (∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, (u ^ 3 / (s * s * s) + u ^ 2 / (s * s)), (conj u ^ 3 / (s * s * s) + conj u ^ 2 / (s * s))} : Set ℂ)) ∧
        Submodule.span Qbar (Set.range (fun p : Fin 2 × Fin 3 => x p.1 * y p.2)) = Submodule.span Qbar ({1, u, conj u, (u ^ 3 / (s * s * s) + u ^ 2 / (s * s)), (conj u ^ 3 / (s * s * s) + conj u ^ 2 / (s * s))} : Set ℂ)) ∧
      ∀ w ∈ Submodule.span Qbar ({1, u, conj u, (u ^ 3 / (s * s * s) + u ^ 2 / (s * s)), (conj u ^ 3 / (s * s * s) + conj u ^ 2 / (s * s))} : Set ℂ), w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) →
        ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Subfield.zero_mem _)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hu0 ((map_ne_zero _).2 hu0) (by rw [← hss]; ring)
  obtain ⟨hind, hsq, hcsq, hinv⟩ :=
    DiazModulus.laurent_cubic_space_excludes_squares_and_reciprocals u s hu hs hsr hss
  set F := u ^ 3 / (s * s * s) + u ^ 2 / (s * s) with hFdef
  set G := conj u ^ 3 / (s * s * s) + conj u ^ 2 / (s * s) with hGdef
  set W := Submodule.span Qbar ({1, u, conj u, F, G} : Set ℂ) with hW
  have m1 : (1 : ℂ) ∈ W := Submodule.subset_span (by simp)
  have mu : u ∈ W := Submodule.subset_span (by simp)
  have mcu : conj u ∈ W := Submodule.subset_span (by simp)
  have mF : F ∈ W := Submodule.subset_span (by simp)
  have mG : G ∈ W := Submodule.subset_span (by simp)
  have hF : F * (s * s * s) = u ^ 3 + s * u ^ 2 := by rw [hFdef]; field_simp
  have hcu' : conj u = s * s / u := by rw [eq_div_iff hu0]; linear_combination -hss
  have hG : u ^ 2 * G = s * conj u + s * s := by
    rw [hGdef, hcu']
    field_simp
  -- conjugation stability
  have hcF : conj F = G := by rw [hFdef, hGdef]; simp [map_add, map_div₀, map_pow, map_mul, hsr]
  have hcG : conj G = F := by
    rw [hFdef, hGdef]; simp [map_add, map_div₀, map_pow, map_mul, hsr]
  refine ⟨span_conj_stable ?_, ?_, ?_⟩
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · rw [map_one]; exact m1
    · exact mcu
    · rw [conj_conj]; exact mu
    · rw [hcF]; exact mG
    · rw [hcG]; exact mF
  -- the configuration
  · have hind' := Fintype.linearIndependent_iff.1 hind
    have p10 : u ^ 2 * conj u = (s * s) * u := by linear_combination -u * hss
    have p11 : u ^ 2 * (u + s) = (s * s * s) * F := by linear_combination -hF
    have mem : ∀ i j, ![1, u ^ 2] i * ![conj u, u + s, G] j ∈ W := by
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using mcu
      · simpa using Submodule.add_mem _ mu (span_mul_mem hs m1)
      · simpa using mG
      · simpa [p10] using span_mul_mem (mul_mem hs hs) mu
      · simpa [p11] using span_mul_mem (mul_mem (mul_mem hs hs) hs) mF
      · simpa [hG] using Submodule.add_mem _ (span_mul_mem hs mcu)
          (span_mul_mem (mul_mem hs hs) m1)
    refine ⟨![1, u ^ 2], ![conj u, u + s, G], ?_, ?_, mem, ?_⟩
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
      set σ : ↥Qbar := ⟨s, hs⟩
      have := hind' ![c 1 * σ, c 1, c 0, 0, c 2] (by
        simp only [Fin.sum_univ_three, Subfield.smul_def, smul_eq_mul, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hc
        simp only [Fin.sum_univ_five, Subfield.smul_def, smul_eq_mul]
        simp [σ]
        linear_combination hc)
      have e1 := this 1
      have e2 := this 2
      have e4 := this 4
      simp at e1 e2 e4
      intro i
      fin_cases i
      · exact e2
      · exact e1
      · exact e4
    · refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
      · rintro _ ⟨⟨i, j⟩, rfl⟩
        exact mem i j
      · set P := Submodule.span Qbar (Set.range (fun p : Fin 2 × Fin 3 =>
          ![1, u ^ 2] p.1 * ![conj u, u + s, G] p.2)) with hP
        have pr : ∀ i j, ![1, u ^ 2] i * ![conj u, u + s, G] j ∈ P :=
          fun i j => Submodule.subset_span ⟨(i, j), rfl⟩
        have q00 := pr 0 0
        have q01 := pr 0 1
        have q02 := pr 0 2
        have q11 := pr 1 1
        have q12 := pr 1 2
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, one_mul] at q00 q01 q02 q11 q12
        have q1 : (1 : ℂ) ∈ P := span_mem_of_eq
          (show (1 : ℂ) = (s * s)⁻¹ * (u ^ 2 * G) + (-(s * s)⁻¹ * s) * conj u by
            rw [hG]; field_simp; ring)
          (Submodule.add_mem _ (span_mul_mem (inv_mem (mul_mem hs hs)) q12)
            (span_mul_mem (mul_mem (neg_mem (inv_mem (mul_mem hs hs))) hs) q00))
        have qu : u ∈ P := span_mem_of_eq (show u = (u + s) + (-s) * 1 by ring)
          (Submodule.add_mem _ q01 (span_mul_mem (neg_mem hs) q1))
        have qF : F ∈ P := span_mem_of_eq
          (show F = (s * s * s)⁻¹ * (u ^ 2 * (u + s)) by rw [p11]; field_simp)
          (span_mul_mem (inv_mem (mul_mem (mul_mem hs hs) hs)) q11)
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        exacts [q1, qu, q00, qF, q02]
  -- invisibility
  · intro w hw hw0 hconfw
    have hρ : IsAlgebraic ℚ (u * conj u) := mem_Qbar_iff.1 (by rw [← hss]; exact mul_mem hs hs)
    have hle := span_four_le hw
    rcases (DiazModulus.circle_point_extension_two_by_three_configuration_iff u w hu hρ hw0).1
      hconfw with h | h | ⟨b, hb, hb0, h⟩
    · exact hsq (hle (exchange hw0 h))
    · exact hcsq (hle (exchange hw0 h))
    · exact hinv b hb hb0 (hle (exchange hw0 h))
