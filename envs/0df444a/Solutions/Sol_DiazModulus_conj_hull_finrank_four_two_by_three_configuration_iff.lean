-- Prove2me | solution 1 for DiazModulus.conj_hull_finrank_four_two_by_three_configuration_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T07:25:02.656139+00:00
-- url     : https://prove2.me/submissions/ee9686bf-ee8f-4da4-9725-7f6521e1553d

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_circle_point_extension_two_by_three_configuration_iff

open Complex ComplexConjugate

/-! # A four-dimensional conjugation hull carries a `2 × 3` configuration iff `z ∈ H + Q̄/(u − a)`, `a ā = u ū`

Let `u ∉ Q̄` with `ρ = u ū` algebraic, `H = Q̄ + Q̄u + Q̄ū`, `V = H + Q̄z` and `W = V + Q̄z̄` of dimension `4`.
Since `1, u, ū` are free (a relation times `u` is a polynomial of degree `≤ 2` vanishing at `u`), `z ∉ H`
(otherwise `z̄ ∈ H` and `W ≤ H` has dimension `≤ 3`), and `z̄ ∈ V` (otherwise `z̄, z, 1, u, ū` are free and
`W` has dimension `5`). So `W = V` and Theorem B (`circle_point_extension_two_by_three_configuration_iff`)
applies to `V`.
* **(⇐)** `a ā = ρ ≠ 0` gives `a ≠ 0`, and Theorem B's third alternative puts a configuration in `V = W`.
* **(⇒)** Theorem B gives `z ∈ H + Q̄w` with `w = u²`, `ū²` or `(u − a)⁻¹`, `a ≠ 0`. By exchange `w ∈ V`, and
  `W` is conjugation-stable, so `w̄ ∈ W = V ≤ H + Q̄w`. For `w = u²` this puts `ū² = ρ²u⁻²` in
  `H + Q̄u²`, for `w = ū²` it puts `u²` in `H + Q̄ū²`; clearing denominators, `u` is a root of a non-zero
  polynomial over `Q̄`. For `w = (u − a)⁻¹`, `w̄ = −ā/ρ − (ā²/ρ)(u − b)⁻¹` with `b = ρ/ā`, so
  `(u − b)⁻¹ ∈ H + Q̄(u − a)⁻¹`; multiplying out by `u(u − a)(u − b)` and evaluating at `b` gives
  `b(b − a) = 0`, so `b = a`, that is `a ā = ρ`.
-/

namespace R20_hull4
open DiazModulus Polynomial

/-- Outside `Q̄`, no non-zero polynomial over `Q̄` vanishes. -/
theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) :
    P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem ne_zero_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : u ≠ 0 :=
  fun h => hu (h ▸ Subfield.zero_mem _)

/-- `ρ = u ū` as a non-zero element of `Q̄`. -/
theorem exists_rho {u : ℂ} (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u)) :
    ∃ ρ : ↥Qbar, ρ ≠ 0 ∧ (ρ : ℂ) = u * conj u := by
  have hu0 := ne_zero_of_not_mem hu
  refine ⟨⟨u * conj u, mem_Qbar_iff.2 hρ⟩, fun h => ?_, rfl⟩
  exact mul_ne_zero hu0 ((_root_.map_ne_zero _).2 hu0) (congrArg Subtype.val h)

/-- Conjugation maps `Q̄` to itself. -/
theorem conj_mem_Qbar {a : ℂ} (ha : a ∈ Qbar) : conj a ∈ Qbar :=
  mem_Qbar_iff.2 ((mem_Qbar_iff.1 ha).algHom (starRingEnd ℂ).toRatAlgHom)

/-- A span whose generators have their conjugates in it is conjugation-stable. -/
theorem span_conj_stable {S : Set ℂ} (hS : ∀ x ∈ S, conj x ∈ Submodule.span Qbar S) :
    ∀ w ∈ Submodule.span Qbar S, conj w ∈ Submodule.span Qbar S := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [show conj (c • x) = (⟨conj (c : ℂ), conj_mem_Qbar c.2⟩ : ↥Qbar) • conj x from
      map_mul conj (c : ℂ) x]
    exact Submodule.smul_mem _ _ hx

theorem set_eq_insert (u w : ℂ) : ({1, u, conj u, w} : Set ℂ) = insert w {1, u, conj u} := by
  ext t
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem exchange {u z w : ℂ} (hw : w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ))
    (h : w ∈ Submodule.span Qbar ({1, u, conj u, z} : Set ℂ)) :
    z ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) := by
  rw [set_eq_insert] at h ⊢
  exact mem_span_insert_exchange h hw

theorem span_le_of_mem {u z w : ℂ} (h : w ∈ Submodule.span Qbar ({1, u, conj u, z} : Set ℂ)) :
    Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) ≤
      Submodule.span Qbar ({1, u, conj u, z} : Set ℂ) := by
  rw [set_eq_insert u w, Submodule.span_insert, set_eq_insert u z]
  exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 (by rwa [set_eq_insert] at h))
    (Submodule.span_mono (Set.subset_insert _ _))

theorem mem_span_four {u w t : ℂ} (h : t ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ)) :
    ∃ c₀ c₁ c₂ c₃ : ↥Qbar, t = (c₀ : ℂ) + c₁ * u + c₂ * conj u + c₃ * w := by
  rw [set_eq_insert, Submodule.mem_span_insert] at h
  obtain ⟨c₃, s, hs, rfl⟩ := h
  obtain ⟨c₀, c₁, c₂, rfl⟩ := Submodule.mem_span_triple.1 hs
  exact ⟨c₀, c₁, c₂, c₃, by simp only [Subfield.smul_def, smul_eq_mul, mul_one]; ring⟩

/-! ## Dimension facts -/

/-- `1, u, ū` are free over `Q̄`. -/
theorem li3 {u : ℂ} (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u)) :
    LinearIndependent (↥Qbar) ![1, u, conj u] := by
  obtain ⟨ρ, hρ0, hρ'⟩ := exists_rho hu hρ
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Subfield.smul_def, smul_eq_mul, mul_one] at hg
  have hP := aeval_eq_zero hu (P := C (g 1) * X ^ 2 + C (g 0) * X + C (g 2) * C ρ) (by
    simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, am, hρ']
    linear_combination u * hg)
  have h2 := congrArg (coeff · 2) hP
  have h1 := congrArg (coeff · 1) hP
  have h0 := congrArg (coeff · 0) hP
  simp at h2 h1
  simp [hρ0] at h0
  intro i; fin_cases i <;> assumption

theorem finrank_le_three (a b c : ℂ) :
    Module.finrank (↥Qbar) (Submodule.span Qbar ({a, b, c} : Set ℂ)) ≤ 3 := by
  classical
  have h := finrank_span_finset_le_card (R := ↥Qbar) ({a, b, c} : Finset ℂ)
  simp only [Finset.coe_insert, Finset.coe_singleton] at h
  exact h.trans Finset.card_le_three

/-- In a four-dimensional hull, `z ∉ H`. -/
theorem not_mem_H {u z : ℂ}
    (h4 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ)) = 4) :
    z ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) := by
  intro hz
  have hcz : conj z ∈ Submodule.span Qbar ({1, u, conj u} : Set ℂ) := by
    refine span_conj_stable (fun x hx => ?_) z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> exact Submodule.subset_span (by simp)
  have hle : Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) ≤
      Submodule.span Qbar ({1, u, conj u} : Set ℂ) := by
    refine Submodule.span_le.2 fun t ht => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · exact hz
    · exact hcz
  have : FiniteDimensional (↥Qbar) (Submodule.span Qbar ({1, u, conj u} : Set ℂ)) :=
    FiniteDimensional.span_of_finite _ (Set.toFinite _)
  have := Submodule.finrank_mono hle
  have := finrank_le_three 1 u (conj u)
  omega

/-- In a four-dimensional hull, `z̄ ∈ V = H + Q̄z`. -/
theorem conj_mem_V {u z : ℂ} (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u))
    (h4 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ)) = 4)
    (hzH : z ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ)) :
    conj z ∈ Submodule.span Qbar ({1, u, conj u, z} : Set ℂ) := by
  by_contra hc
  have hr3 : Set.range ![1, u, conj u] = ({1, u, conj u} : Set ℂ) := by
    simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  have hl4 : LinearIndependent (↥Qbar) ![z, 1, u, conj u] :=
    linearIndependent_finCons.2 ⟨li3 hu hρ, by rwa [hr3]⟩
  have hr4 : Set.range ![z, 1, u, conj u] = ({1, u, conj u, z} : Set ℂ) := by
    ext t
    simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hl5 : LinearIndependent (↥Qbar) ![conj z, z, 1, u, conj u] :=
    linearIndependent_finCons.2 ⟨hl4, by rwa [hr4]⟩
  have hr5 : Set.range ![conj z, z, 1, u, conj u] = ({1, u, conj u, z, conj z} : Set ℂ) := by
    ext t
    simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have := finrank_span_eq_card hl5
  rw [hr5, h4, Fintype.card_fin] at this
  omega

/-! ## The three exclusions -/

theorem conj_sq_not_mem {u : ℂ} (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u)) :
    conj u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, u ^ 2} : Set ℂ) := by
  intro hw
  obtain ⟨c₀, c₁, c₂, c₃, e⟩ := mem_span_four hw
  obtain ⟨ρ, hρ0, hρ'⟩ := exists_rho hu hρ
  have hP := aeval_eq_zero hu
    (P := C c₃ * X ^ 4 + C c₁ * X ^ 3 + C c₀ * X ^ 2 + C c₂ * C ρ * X - C ρ ^ 2) (by
    simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, am, hρ']
    linear_combination (-u ^ 2) * e)
  have h0 := congrArg (eval 0) hP
  simp [hρ0] at h0

theorem sq_not_mem {u : ℂ} (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u)) :
    u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, conj u ^ 2} : Set ℂ) := by
  intro hw
  obtain ⟨c₀, c₁, c₂, c₃, e⟩ := mem_span_four hw
  obtain ⟨ρ, -, hρ'⟩ := exists_rho hu hρ
  obtain ⟨σ, hσ⟩ : ∃ σ : ↥Qbar, (σ : ℂ) = (u * conj u) ^ 2 :=
    ⟨ρ ^ 2, by rw [SubmonoidClass.coe_pow, hρ']⟩
  have hP := aeval_eq_zero hu
    (P := X ^ 4 - C c₁ * X ^ 3 - C c₀ * X ^ 2 - C c₂ * C ρ * X - C c₃ * C σ) (by
    simp only [map_sub, map_mul, map_pow, aeval_X, aeval_C, am, hρ', hσ]
    linear_combination u ^ 2 * e)
  have h4 := congrArg (coeff · 4) hP
  simp at h4

/-- Partial fractions: `(u − b)⁻¹ ∈ H + Q̄(u − a)⁻¹` with `b ≠ 0` forces `b = a`. -/
theorem shift_eq {u : ℂ} (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u)) {α β : ↥Qbar}
    (hβ : β ≠ 0)
    (h : ((u - β)⁻¹ : ℂ) ∈ Submodule.span Qbar ({1, u, conj u, (u - α)⁻¹} : Set ℂ)) :
    β = α := by
  obtain ⟨c₀, c₁, c₂, c₃, e⟩ := mem_span_four h
  obtain ⟨ρ, -, hρ'⟩ := exists_rho hu hρ
  have hna : u - α ≠ 0 := fun h' => hu (sub_eq_zero.1 h' ▸ α.2)
  have hnb : u - β ≠ 0 := fun h' => hu (sub_eq_zero.1 h' ▸ β.2)
  have hP := aeval_eq_zero hu
    (P := X * (X - C α) - (C c₀ + C c₁ * X) * X * (X - C α) * (X - C β) -
      C c₂ * C ρ * (X - C α) * (X - C β) - C c₃ * X * (X - C β)) (by
    simp only [map_sub, map_add, map_mul, aeval_X, aeval_C, am, hρ']
    linear_combination (u * (u - α) * (u - β)) * e - (u * (u - α)) * mul_inv_cancel₀ hnb +
      (c₃ * u * (u - β)) * mul_inv_cancel₀ hna)
  have h' := congrArg (eval β) hP
  simp only [eval_sub, eval_add, eval_mul, eval_X, eval_C, sub_self, mul_zero,
    sub_zero, eval_zero] at h'
  rcases mul_eq_zero.1 h' with h'' | h''
  · exact absurd h'' hβ
  · exact sub_eq_zero.1 h''

/-- `conj (u − a)⁻¹ = −ā/ρ − (ā²/ρ)(u − ρ/ā)⁻¹`. -/
theorem conj_inv_shift {u a : ℂ} (hu : u ∉ Qbar) (ha : a ∈ Qbar) (ha0 : a ≠ 0) :
    (u - u * conj u / conj a)⁻¹ =
      -(conj a ^ 2 / (u * conj u)) * conj (u - a)⁻¹ - conj a / (u * conj u) := by
  have hu0 := ne_zero_of_not_mem hu
  have hcu0 : conj u ≠ 0 := (_root_.map_ne_zero _).2 hu0
  have hca0 : conj a ≠ 0 := (_root_.map_ne_zero _).2 ha0
  have hd : conj u - conj a ≠ 0 := by
    rw [← map_sub]
    exact (_root_.map_ne_zero _).2 fun h => hu (sub_eq_zero.1 h ▸ ha)
  have hd' : u * conj a - u * conj u ≠ 0 := by
    rw [← mul_sub]
    exact mul_ne_zero hu0 fun h => hd (by linear_combination -h)
  rw [map_inv₀, map_sub]
  refine inv_eq_of_mul_eq_one_right ?_
  field_simp
  ring

end R20_hull4

open DiazModulus R20_hull4 in
theorem solution (u z : ℂ) (hu : u ∉ Qbar)
    (hρ : IsAlgebraic ℚ (u * conj u))
    (h4 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ)) = 4) :
    (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
        ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ)) ↔
    ∃ a ∈ Qbar, a * conj a = u * conj u ∧
      z ∈ Submodule.span Qbar ({1, u, conj u, (u - a)⁻¹} : Set ℂ) := by
  have hzH := not_mem_H h4
  have hWV : Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) ≤
      Submodule.span Qbar ({1, u, conj u, z} : Set ℂ) := by
    refine Submodule.span_le.2 fun t ht => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · exact conj_mem_V hu hρ h4 hzH
  have hVW : Submodule.span Qbar ({1, u, conj u, z} : Set ℂ) ≤
      Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) :=
    Submodule.span_mono fun t ht => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht ⊢
      tauto
  have hWc := span_conj_stable (S := ({1, u, conj u, z, conj z} : Set ℂ)) fun x hx => by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact Submodule.subset_span (by simp)
  -- for `z ∈ H + Q̄w`: `w̄ ∈ H + Q̄w`
  have key : ∀ w, z ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) →
      conj w ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) := fun w hz =>
    span_le_of_mem hz (hWV (hWc _ (hVW (exchange hzH hz))))
  have hB := DiazModulus.circle_point_extension_two_by_three_configuration_iff u z hu hρ hzH
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    rcases hB.1 ⟨x, y, hx, hy, fun i j => hWV (hxy i j)⟩ with h | h | ⟨a, ha, ha0, h⟩
    · exact absurd (by simpa using key _ h) (conj_sq_not_mem hu hρ)
    · exact absurd (by simpa using key _ h) (sq_not_mem hu hρ)
    · refine ⟨a, ha, ?_, h⟩
      obtain ⟨ρ, hρ0, hρ'⟩ := exists_rho hu hρ
      have hca0 : conj a ≠ 0 := (_root_.map_ne_zero _).2 ha0
      obtain ⟨α', hα'⟩ : ∃ α' : ↥Qbar, (α' : ℂ) = conj a := ⟨⟨conj a, conj_mem_Qbar ha⟩, rfl⟩
      have hα0 : α' ≠ 0 := fun h0 => hca0 (by rw [← hα', h0]; rfl)
      have hmem : ((u - (ρ / α' : ↥Qbar))⁻¹ : ℂ) ∈
          Submodule.span Qbar ({1, u, conj u, (u - (⟨a, ha⟩ : ↥Qbar))⁻¹} : Set ℂ) := by
        have e : ((u - (ρ / α' : ↥Qbar))⁻¹ : ℂ) =
            (-(α' ^ 2 / ρ)) • conj (u - a)⁻¹ + (-(α' / ρ)) • (1 : ℂ) := by
          rw [Subfield.smul_def, Subfield.smul_def, smul_eq_mul, smul_eq_mul, mul_one]
          simp only [Subfield.coe_div, Subfield.coe_neg, SubmonoidClass.coe_pow, hρ', hα']
          rw [conj_inv_shift hu ha ha0]
          ring
        rw [e]
        exact add_mem (Submodule.smul_mem _ _ (key _ h))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      have hb := congrArg Subtype.val (shift_eq hu hρ (div_ne_zero hρ0 hα0) hmem)
      simp only [Subfield.coe_div, hρ', hα'] at hb
      rw [div_eq_iff hca0] at hb
      linear_combination -hb
  · rintro ⟨a, ha, haa, h⟩
    have ha0 : a ≠ 0 := by
      rintro rfl
      obtain ⟨ρ, hρ0, hρ'⟩ := exists_rho hu hρ
      exact hρ0 (Subtype.ext (by rw [hρ', ← haa, zero_mul]; rfl))
    obtain ⟨x, y, hx, hy, hxy⟩ := hB.2 (Or.inr (Or.inr ⟨a, ha, ha0, h⟩))
    exact ⟨x, y, hx, hy, fun i j => hVW (hxy i j)⟩
