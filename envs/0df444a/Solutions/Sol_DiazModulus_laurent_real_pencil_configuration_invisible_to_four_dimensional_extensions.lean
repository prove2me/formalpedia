-- Prove2me | solution 1 for DiazModulus.laurent_real_pencil_configuration_invisible_to_four_dimensional_extensions
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T07:31:29.388541+00:00
-- url     : https://prove2.me/submissions/6a687375-7ecb-4c89-b5e4-6262de9cbb61

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_laurent_real_pencil_space_excludes_squares_and_reciprocals
import Theorems.Thm_DiazModulus_conj_stable_real_pencil_space_carries_two_by_three_configuration
import Theorems.Thm_DiazModulus_circle_point_extension_two_by_three_configuration_iff

open Complex ComplexConjugate

/-! # The Laurent real-pencil configuration needs the whole space

Let `u ∉ Q̄`, `s ∈ Q̄` real with `s² = u ū`, `v = u/s`, `f = Σ_{|j| ≤ k} c_j v^j` with
`c_{-j} = c̄_j`, and `W = span_Q̄ {1, u, ū, f, f/(s + λu)}` with `λλ̄ = 1`. Put `H₀ = Q̄ + Q̄u + Q̄ū`.

* `f` is real: `ū = s²/u` and `s̄ = s` give `v̄ = v⁻¹`, so `f̄ = Σ c_{-j} v^{-j}`, which is `f`
  after the reindexing `j ↦ -j` of `[-k, k]`. With the five generators free (`hind`), the
  real-pencil node (`conj_stable_real_pencil_space_carries_two_by_three_configuration`) says that
  `W` is conjugation-stable and carries a `2 × 3` configuration.
* No `H₀ + Q̄w` with `w ∈ W`, `w ∉ H₀`, does. `H₀ + Q̄w ≤ W`. By Theorem B
  (`circle_point_extension_two_by_three_configuration_iff`, `u ū = s²` algebraic) a configuration
  there puts `w` in `H₀ + Q̄t` with `t = u²`, `t = ū²` or `t = (u − b)⁻¹`, `b ∈ Q̄ \ {0}`. As
  `w ∉ H₀`, exchange puts `t` in `H₀ + Q̄w ≤ W`, against
  `laurent_real_pencil_space_excludes_squares_and_reciprocals`.
-/

namespace R14_laurentInvisible

open DiazModulus

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

/-- A Laurent polynomial in `v` with `v̄ = v⁻¹` and `c_{-j} = c̄_j` is real. -/
theorem conj_laurent {v : ℂ} (hv : conj v = v⁻¹) (k : ℕ) (c : ℤ → ℂ)
    (hcs : ∀ j, c (-j) = conj (c j)) :
    conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j) = ∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j := by
  rw [map_sum]
  refine Finset.sum_nbij' (fun j => -j) (fun j => -j) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro j _
    simp
  · intro j _
    simp
  · intro j _
    rw [map_mul, map_zpow₀, hv, ← hcs, inv_zpow']

end R14_laurentInvisible

open DiazModulus R14_laurentInvisible in
theorem solution
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u)
    (lam : ℂ) (hlam : lam ∈ Qbar) (hlam1 : lam * conj lam = 1) (k : ℕ) (c : ℤ → ℂ)
    (hc : ∀ j, c j ∈ Qbar) (hcs : ∀ j, c (-j) = conj (c j)) (hck : c k ≠ 0)
    (hk : 3 ≤ k ∨ (k = 2 ∧ (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (-conj lam) ^ j) ≠ 0)) (hind : LinearIndependent (↥Qbar) ![1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j) / (s + lam * u)]) :
    (∀ w ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j) / (s + lam * u)} : Set ℂ), conj w ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j) / (s + lam * u)} : Set ℂ)) ∧
      (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
        ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j) / (s + lam * u)} : Set ℂ)) ∧
      ∀ w ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j) / (s + lam * u)} : Set ℂ), w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) →
        ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Subfield.zero_mem _)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hu0 ((map_ne_zero _).2 hu0) (by rw [← hss]; ring)
  have hcu : conj u = s * s / u := by rw [eq_div_iff hu0]; linear_combination -hss
  have hv : conj (u / s) = (u / s)⁻¹ := by
    rw [map_div₀, hsr, hcu]
    field_simp
  have hF := conj_laurent hv k c hcs
  obtain ⟨hsq, hcsq, hinv⟩ :=
    DiazModulus.laurent_real_pencil_space_excludes_squares_and_reciprocals u s hu hs hsr hss
      lam hlam hlam1 k c hc hcs hck hk hind
  obtain ⟨hconj, hconf⟩ :=
    DiazModulus.conj_stable_real_pencil_space_carries_two_by_three_configuration u s hu hs hsr hss
      lam hlam hlam1 _ hF hind
  refine ⟨hconj, hconf, ?_⟩
  intro w hw hw0 hconfw
  have hρ : IsAlgebraic ℚ (u * conj u) := mem_Qbar_iff.1 (by rw [← hss]; exact mul_mem hs hs)
  have hle := span_four_le hw
  rcases (DiazModulus.circle_point_extension_two_by_three_configuration_iff u w hu hρ hw0).1
    hconfw with h | h | ⟨b, hb, hb0, h⟩
  · exact hsq (hle (exchange hw0 h))
  · exact hcsq (hle (exchange hw0 h))
  · exact hinv b hb hb0 (hle (exchange hw0 h))
