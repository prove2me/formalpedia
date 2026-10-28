-- Prove2me | solution 1 for D1Bound5.finiteMDividedMatrix_root_height
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:25:54.459571+00:00
-- url     : https://prove2.me/submissions/cca61274-1b9a-475b-9337-62d73ace54c0

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteMMatrix_Definitions
import Theorems.Thm_D1Bound5_finiteMTermEval_norm_le
import Theorems.Thm_D1Bound5_finiteMTerms_admissible
import Theorems.Thm_D1Bound5_finiteMTerms_weight

section
namespace D1Bound5





private theorem finiteM_list_height (L : List FiniteMTerm)
    (a b s v : ℂ) (B S C : ℝ)
    (hB : 1 ≤ B) (hBS : B ≤ S) (hC : 1 ≤ C)
    (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (hs : ‖s‖ ≤ S)
    (hv : ‖v‖ ≤ 2*S*C) (hL : ∀ t ∈ L, finiteMTermAdmissible t) :
    ‖(L.map (fun t => finiteMTermEval t a b s v)).sum‖ ≤
      ((L.map finiteMTermWeight).sum : ℕ)*B^3*S^8*C^2 := by
  induction L with
  | nil => simp
  | cons t L ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    have ht := finiteMTermEval_norm_le t a b s v B S C
      hB hBS hC ha hb hs hv (hL t (by simp))
    have htail := ih (fun t ht => hL t (by simp [ht]))
    calc
      _ ≤ ‖finiteMTermEval t a b s v‖+
          ‖(L.map (fun t => finiteMTermEval t a b s v)).sum‖ := norm_add_le _ _
      _ ≤ _ := add_le_add ht htail
      _ = _ := by ring

/-- The complete actual divided M matrix satisfies a deliberately generous
height bound. This avoids the manuscript's sharper geometric row estimates,
while leaving ample room in its stated approximation constant. -/
theorem _root_.solution (a b s c : ℂ)
    (hB : 1 ≤ ‖b‖) (hab : ‖a‖ ≤ ‖b‖) (hbs : ‖b‖ ≤ ‖s‖)
    (hC : 1 ≤ ‖c‖) (i : Fin 4) :
    (∑ j : Fin 3, ‖finiteMDividedMatrix a b s c i j.succ‖) ≤
      169728*‖b‖^3*‖s‖^8*‖c‖^2 := by
  have hS : 1 ≤ ‖s‖ := hB.trans hbs
  have hSC : 1 ≤ ‖s‖*‖c‖ := by
    have hh := mul_le_mul hS hC (by norm_num : (0 : ℝ) ≤ 1) (norm_nonneg s)
    simpa only [one_mul] using hh
  have hvu (u : ℂ) (hu : ‖u‖ ≤ ‖s‖) : ‖u*c+1‖ ≤ 2*‖s‖*‖c‖ := by
    calc
      _ ≤ ‖u*c‖+‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖u‖*‖c‖+1 := by rw [norm_mul, norm_one]
      _ ≤ 2*‖s‖*‖c‖ := by
        have hmul := mul_le_mul_of_nonneg_right hu (norm_nonneg c)
        nlinarith only [hSC, hmul]
  have hv (j : Fin 3) : ‖![c,a*c+1,b*c+1,s*c+1] j.succ‖ ≤ 2*‖s‖*‖c‖ := by
    fin_cases j
    · exact hvu a (hab.trans hbs)
    · exact hvu b hbs
    · exact hvu s le_rfl
  have hentry (j : Fin 3) : ‖finiteMDividedMatrix a b s c i j.succ‖ ≤
      (((finiteMTerms i j.succ).map finiteMTermWeight).sum : ℕ)*
        ‖b‖^3*‖s‖^8*‖c‖^2 :=
    finiteM_list_height _ a b s _ _ _ _ hB hbs hC hab le_rfl le_rfl (hv j)
      (finiteMTerms_admissible i j)
  calc
    _ ≤ ∑ j : Fin 3, (((finiteMTerms i j.succ).map finiteMTermWeight).sum : ℕ)*
        ‖b‖^3*‖s‖^8*‖c‖^2 := Finset.sum_le_sum (fun j _ => hentry j)
    _ = ((∑ j : Fin 3, ((finiteMTerms i j.succ).map finiteMTermWeight).sum : ℕ) : ℝ)*
        ‖b‖^3*‖s‖^8*‖c‖^2 := by simp [Finset.sum_mul, Nat.cast_sum]
    _ ≤ _ := by
      gcongr
      exact_mod_cast finiteMTerms_weight i

end D1Bound5
end
