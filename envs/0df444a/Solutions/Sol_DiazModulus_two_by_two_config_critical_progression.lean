-- Prove2me | solution 1 for DiazModulus.two_by_two_config_critical_progression
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-08T16:36:20.680853+00:00
-- url     : https://prove2.me/submissions/b90f5567-731a-4eea-8cb3-6e9e992d1a2e

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A `2 × 2` configuration of rank three is a critical progression

Let `x, y` be `K`-independent pairs whose four products `x i * y j` span a `K`-space of dimension 3.
Since a family of four vectors in a 3-dimensional span is not independent (`finrank_span_eq_card`),
there is a non-trivial relation `∑ g i j • x i y j = 0`; with `u = g₀₀ y₀ + g₀₁ y₁` and
`v = g₁₀ y₀ + g₁₁ y₁` it reads `x₀ u + x₁ v = 0`. Here `v ≠ 0`: otherwise `u = 0` too and the
independence of `y` kills all four coefficients. Put `h = x₁ / x₀`, `a = x₀`, `b = v`. Then
`h ∉ K` by the independence of `x`, `span{a, a h} = span{x₀, x₁}` trivially, and `b h = −u`.
Finally `span{v, −u} ≤ span{y₀, y₁}`, and `v, −u` are independent: from `s v − t u = 0` one gets
`v (s x₀ + t x₁) = 0`, so `s = t = 0` by the independence of `x`. Both spans have dimension 2,
so they are equal (`Submodule.eq_of_le_of_finrank_eq`).
-/

namespace R6_critical

theorem range_fin_two {α : Type*} (x : Fin 2 → α) : Set.range x = {x 0, x 1} := by
  rw [← Matrix.range_cons_cons_empty (x 0) (x 1) ![]]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem li_two {K : Subfield ℂ} {x : Fin 2 → ℂ} (hx : LinearIndependent K x) (s t : K)
    (h : (s : ℂ) * x 0 + (t : ℂ) * x 1 = 0) : s = 0 ∧ t = 0 := by
  have := Fintype.linearIndependent_iff.1 hx ![s, t] (by
    simpa [Fin.sum_univ_two, Subfield.smul_def] using h)
  exact ⟨by simpa using this 0, by simpa using this 1⟩

end R6_critical

open DiazModulus R6_critical in
theorem solution (K : Subfield ℂ) (x y : Fin 2 → ℂ)
    (hx : LinearIndependent K x) (hy : LinearIndependent K y)
    (h3 : Module.finrank K
      (Submodule.span K (Set.range fun ij : Fin 2 × Fin 2 => x ij.1 * y ij.2)) = 3) :
    ∃ h a b : ℂ, h ∉ K ∧ a ≠ 0 ∧ b ≠ 0 ∧
      Submodule.span K (Set.range x) = Submodule.span K {a, a * h} ∧
      Submodule.span K (Set.range y) = Submodule.span K {b, b * h} := by
  classical
  have hx0 : x 0 ≠ 0 := hx.ne_zero 0
  have hnot : ¬ LinearIndependent K (fun ij : Fin 2 × Fin 2 => x ij.1 * y ij.2) := by
    intro hf
    have := finrank_span_eq_card hf
    rw [h3] at this
    simp at this
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hnot
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u = (g (0, 0) : ℂ) * y 0 + (g (0, 1) : ℂ) * y 1 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℂ, v = (g (1, 0) : ℂ) * y 0 + (g (1, 1) : ℂ) * y 1 := ⟨_, rfl⟩
  have hrel : x 0 * u + x 1 * v = 0 := by
    rw [Fintype.sum_prod_type] at hg
    simp only [Fin.sum_univ_two, Subfield.smul_def, smul_eq_mul] at hg
    rw [hu, hv]
    linear_combination hg
  have hv0 : v ≠ 0 := by
    intro hv0
    have hu0 : u = 0 := by
      rw [hv0, mul_zero, add_zero] at hrel
      exact (mul_eq_zero.1 hrel).resolve_left hx0
    obtain ⟨h1, h2⟩ := li_two hy _ _ (hu ▸ hu0)
    obtain ⟨h3', h4⟩ := li_two hy _ _ (hv ▸ hv0)
    apply hi
    obtain ⟨a, b⟩ := i
    fin_cases a <;> fin_cases b <;> simp_all
  have hh : x 1 / x 0 ∉ K := by
    intro hmem
    have := li_two hx ⟨x 1 / x 0, hmem⟩ (-1) (by push_cast; field_simp; ring)
    exact one_ne_zero (neg_eq_zero.1 this.2)
  refine ⟨x 1 / x 0, x 0, v, hh, hx0, hv0, ?_, ?_⟩
  · rw [range_fin_two, mul_div_cancel₀ _ hx0]
  · have hvh : v * (x 1 / x 0) = -u := by
      field_simp
      linear_combination hrel
    rw [hvh]
    symm
    have : FiniteDimensional K (Submodule.span K (Set.range y)) :=
      FiniteDimensional.span_of_finite K (Set.finite_range y)
    have hmem : ∀ s t : K, (s : ℂ) * y 0 + (t : ℂ) * y 1 ∈ Submodule.span K (Set.range y) := by
      intro s t
      have h0 : (s : ℂ) * y 0 = s • y 0 := rfl
      have h1 : (t : ℂ) * y 1 = t • y 1 := rfl
      rw [h0, h1]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨hv ▸ hmem _ _, Submodule.neg_mem _ (hu ▸ hmem _ _)⟩
    · have hli : LinearIndependent K ![v, -u] := by
        rw [LinearIndependent.pair_iff]
        intro s t hst
        simp only [Subfield.smul_def, smul_eq_mul] at hst
        have : v * ((s : ℂ) * x 0 + (t : ℂ) * x 1) = 0 := by
          linear_combination x 0 * hst + (t : ℂ) * hrel
        exact li_two hx s t ((mul_eq_zero.1 this).resolve_left hv0)
      have e1 := finrank_span_eq_card hli
      have e2 := finrank_span_eq_card hy
      rw [Matrix.range_cons_cons_empty] at e1
      rw [e1, e2]
