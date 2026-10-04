-- Prove2me | solution 1 for Disjunctive.HigherDim.lift_and_project_one_var
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T03:36:24.389574+00:00
-- url     : https://prove2.me/submissions/0c9c7a7c-beb1-46f8-a6ef-d8b4aecc7c1e

import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic

open Disjunctive.HigherDim in
/-- With no constraint rows (`m = 0`, `n = 1`), `Pj` is all of `ℝ¹` while the convex hull of
`{x₀ ∈ {0,1}}` stays inside `{x₀ ≤ 1}`; the point `x₀ = 2` separates them. -/
theorem pj_cex_548f8dcb :
    ¬ (Pj (Matrix.of fun (i : Fin 0) (_ : Fin 1) => i.elim0) (fun i : Fin 0 => i.elim0) 0 =
      convexHull ℝ (Poly (Matrix.of fun (i : Fin 0) (_ : Fin 1) => i.elim0)
        (fun i : Fin 0 => i.elim0) ∩ ZeroOneSet 0)) := by
  intro h
  have hx : (fun _ : Fin 1 => (2 : ℝ)) ∈
      Pj (Matrix.of fun (i : Fin 0) (_ : Fin 1) => i.elim0) (fun i : Fin 0 => i.elim0) 0 :=
    ⟨fun _ => 2, ⟨fun i => i.elim0, fun i => i.elim0, rfl⟩⟩
  rw [h] at hx
  have hconv : Convex ℝ {x : Fin 1 → ℝ | x 0 ≤ 1} :=
    convex_halfSpace_le (f := fun x : Fin 1 → ℝ => x 0)
      ⟨fun x y => rfl, fun c x => rfl⟩ 1
  have hsub : convexHull ℝ (Poly (Matrix.of fun (i : Fin 0) (_ : Fin 1) => i.elim0)
      (fun i : Fin 0 => i.elim0) ∩ ZeroOneSet 0) ⊆ {x : Fin 1 → ℝ | x 0 ≤ 1} := by
    refine convexHull_min ?_ hconv
    rintro x ⟨-, hx | hx⟩
    · show x 0 ≤ 1
      rw [hx]; norm_num
    · show x 0 ≤ 1
      rw [hx]
  have := hsub hx
  simp only [Set.mem_setOf_eq] at this
  norm_num at this

open Disjunctive.HigherDim in
theorem solution : ¬ (∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (j : Fin n),
    Pj A b j = convexHull ℝ (Poly A b ∩ ZeroOneSet j)) := by
  intro h
  exact pj_cex_548f8dcb (h _ _ _)
