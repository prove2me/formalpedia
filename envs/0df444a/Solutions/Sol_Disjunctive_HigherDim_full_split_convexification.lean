-- Prove2me | solution 1 for Disjunctive.HigherDim.full_split_convexification
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T04:58:23.538113+00:00
-- url     : https://prove2.me/submissions/a3adabc4-5779-4aa8-bd25-95573a7cd444

import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic

set_option autoImplicit false

namespace Cexfb9c5727
open Disjunctive.HigherDim

/-- The line `x₁ = x₀ + 1/2` as `{x : A x ≥ b}`. -/
noncomputable def A : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 1; 1, -1]
noncomputable def b : Fin 2 → ℝ := ![1/2, -1/2]

theorem mem_poly_iff (x : Fin 2 → ℝ) :
    x ∈ Disjunctive.HigherDim.Poly A b ↔ x 1 = x 0 + 1/2 := by
  have e0 : (A.mulVec x) 0 = -x 0 + x 1 := by
    simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have e1 : (A.mulVec x) 1 = x 0 - x 1 := by
    simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  have b0 : b 0 = 1/2 := by simp [b]
  have b1 : b 1 = -1/2 := by simp [b]
  show (∀ i, b i ≤ (A.mulVec x) i) ↔ _
  rw [Fin.forall_fin_two, e0, e1, b0, b1]
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · intro h; constructor <;> linarith

theorem k0_empty :
    K0Set A b ({0, 1} : Finset (Fin 2)) = ∅ := by
  ext x
  simp only [K0Set, Set.mem_inter_iff, Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_and]
  intro hx h
  rw [mem_poly_iff] at hx
  have h0 : x 0 = 0 ∨ x 0 = 1 := h 0 (by simp)
  have h1 : x 1 = 0 ∨ x 1 = 1 := h 1 (by simp)
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rw [h0, h1] at hx <;> norm_num at hx

theorem lhs_mem : (![1/2, 1] : Fin 2 → ℝ) ∈ IteratedSplit (Disjunctive.HigherDim.Poly A b) [0, 1] := by
  show (![1/2, 1] : Fin 2 → ℝ) ∈ SplitConvexify (SplitConvexify (Disjunctive.HigherDim.Poly A b) 0) 1
  apply subset_convexHull
  refine ⟨?_, Or.inr (by simp)⟩
  have hx : (![0, 1/2] : Fin 2 → ℝ) ∈ Disjunctive.HigherDim.Poly A b ∩ ZeroOneSet 0 :=
    ⟨(mem_poly_iff _).2 (by simp), Or.inl (by simp)⟩
  have hy : (![1, 3/2] : Fin 2 → ℝ) ∈ Disjunctive.HigherDim.Poly A b ∩ ZeroOneSet 0 :=
    ⟨(mem_poly_iff _).2 (by norm_num), Or.inr (by simp)⟩
  apply segment_subset_convexHull hx hy
  refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
  funext i
  fin_cases i <;> simp <;> norm_num

end Cexfb9c5727

open Disjunctive.HigherDim in
theorem solution : ¬ (∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (l : List (Fin n)) (hnd : l.Nodup) (heq : l.toFinset = Nprime),
    IteratedSplit (Poly A b) l = convexHull ℝ (K0Set A b Nprime)) := by
  intro h
  have e := h Cexfb9c5727.A Cexfb9c5727.b ({0, 1} : Finset (Fin 2)) [0, 1] (by decide) (by decide)
  have hm := Cexfb9c5727.lhs_mem
  rw [e, Cexfb9c5727.k0_empty, convexHull_empty] at hm
  exact hm
