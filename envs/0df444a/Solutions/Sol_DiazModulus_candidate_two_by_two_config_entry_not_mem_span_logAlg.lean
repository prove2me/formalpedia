-- Prove2me | solution 1 for DiazModulus.candidate_two_by_two_config_entry_not_mem_span_logAlg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-08T16:36:12.374518+00:00
-- url     : https://prove2.me/submissions/d0ef61c8-2eb2-40dd-a880-c790c6402ec7

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_circle_point_config_constant_matrix_det_ne_zero
import Theorems.Thm_DiazModulus_algebraic_mem_span_logAlg_eq_zero
import Theorems.Thm_DiazModulus_logAlg_conj_stable

open Complex ComplexConjugate

/-! # A generic `2 × 2` configuration at a candidate has an entry outside `span_{Q̄} ℒ` in every
row and every column

At a candidate `u`, `u ū = |u|²` is algebraic, so `circle_point_config_constant_matrix_det_ne_zero`
(with `K = Q̄`) gives an invertible matrix `c` over `Q̄` with `xᵢ yⱼ − cᵢⱼ ∈ Q̄u + Q̄ū` for all
`i, j`. An invertible `2 × 2` matrix has a non-zero entry in every row and every column. Both `u`
(by definition of a candidate) and `ū` (`logAlg_conj_stable`) lie in `ℒ`, so if `xᵢ yⱼ` were in
`span_{Q̄} ℒ` then so would be the algebraic number `cᵢⱼ = xᵢ yⱼ − (xᵢ yⱼ − cᵢⱼ)`, and
`algebraic_mem_span_logAlg_eq_zero` (a consequence of Baker's theorem) forces `cᵢⱼ = 0`.
Choosing `j` (resp. `i`) with `cᵢⱼ ≠ 0` gives the two claims.
-/

namespace R6_twoByTwoLog
open DiazModulus

theorem row_ne_zero (c : Matrix (Fin 2) (Fin 2) Qbar) (hc : c.det ≠ 0) :
    ∀ i, ∃ j, c i j ≠ 0 := by
  rw [Fin.forall_fin_two, Fin.exists_fin_two, Fin.exists_fin_two]
  rw [Matrix.det_fin_two] at hc
  constructor <;> by_contra h <;> push Not at h <;> apply hc <;> simp [h.1, h.2]

theorem col_ne_zero (c : Matrix (Fin 2) (Fin 2) Qbar) (hc : c.det ≠ 0) :
    ∀ j, ∃ i, c i j ≠ 0 := by
  rw [Fin.forall_fin_two, Fin.exists_fin_two, Fin.exists_fin_two]
  rw [Matrix.det_fin_two] at hc
  constructor <;> by_contra h <;> push Not at h <;> apply hc <;> simp [h.1, h.2]

theorem entry_eq_zero {u p : ℂ} (huL : u ∈ LogAlg) (a : Qbar)
    (hp : p - (a : ℂ) ∈ Submodule.span Qbar ({u, conj u} : Set ℂ))
    (hpL : p ∈ Submodule.span Qbar LogAlg) : a = 0 := by
  have hle : Submodule.span Qbar ({u, conj u} : Set ℂ) ≤ Submodule.span Qbar LogAlg :=
    Submodule.span_mono (Set.insert_subset_iff.2
      ⟨huL, Set.singleton_subset_iff.2 (logAlg_conj_stable u huL)⟩)
  have ha : (a : ℂ) ∈ Submodule.span Qbar LogAlg := by
    have := Submodule.sub_mem _ hpL (hle hp)
    rwa [sub_sub_cancel] at this
  exact Subtype.ext (algebraic_mem_span_logAlg_eq_zero (a : ℂ) a.2 ha)

end R6_twoByTwoLog

open DiazModulus R6_twoByTwoLog in
theorem solution {u : ℂ} (h : IsCandidate u)
    (m : ℕ) (w : Fin m → ℂ) (hgen : AlgebraicIndependent Qbar (Fin.cons u w : Fin (m + 1) → ℂ))
    (x y : Fin 2 → ℂ) (hx : LinearIndependent Qbar x) (hy : LinearIndependent Qbar y)
    (hxy : ∀ i j, x i * y j ∈ Submodule.span Qbar (({1, u, conj u} : Set ℂ) ∪ Set.range w)) :
    (∀ i, ∃ j, x i * y j ∉ Submodule.span Qbar LogAlg) ∧
      (∀ j, ∃ i, x i * y j ∉ Submodule.span Qbar LogAlg) := by
  have hρ : u * conj u ∈ Qbar := by
    rw [Complex.mul_conj']
    exact Qbar.pow_mem (mem_Qbar_iff.2 h.2.1) 2
  obtain ⟨c, hdet, hc⟩ :=
    circle_point_config_constant_matrix_det_ne_zero Qbar u hρ m w hgen x y hx hy hxy
  refine ⟨fun i => ?_, fun j => ?_⟩
  · obtain ⟨j, hj⟩ := row_ne_zero c hdet i
    exact ⟨j, fun hL => hj (entry_eq_zero h.2.2 (c i j) (hc i j) hL)⟩
  · obtain ⟨i, hi⟩ := col_ne_zero c hdet j
    exact ⟨i, fun hL => hi (entry_eq_zero h.2.2 (c i j) (hc i j) hL)⟩
