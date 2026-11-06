-- Prove2me | solution 1 for BianchiIX.alternating_fin5_add_flow
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T05:43:28.327609+00:00
-- url     : https://prove2.me/submissions/dbaea0a1-ac06-4eb9-91ff-0561ad613fb9

import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace BianchiIX
end BianchiIX

section
noncomputable section
open BianchiIX
variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
private theorem BianchiIX.alternating_update_add_multiple (f : E [⋀^ι]→ₗ[ℝ] ℝ) (v : ι → E)
    {i j : ι} (hij : i ≠ j) (c : ℝ) :
    f (Function.update v i (v i + c • v j)) = f v := by
  rw [f.map_update_add, Function.update_eq_self, f.map_update_smul,
    f.map_update_self v hij, smul_zero, add_zero]

end
end

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι] [DecidableEq ι]


/-- Each moving-time contribution repeats the flow vector in an alternating volume. -/
theorem solution (f : E [⋀^Fin 5]→ₗ[ℝ] ℝ)
    (X F A B C : E) (a b c : ℝ) :
    f ![X, F, A + a • F, B + b • F, C + c • F] = f ![X, F, A, B, C] := by
  have h₂ : f ![X, F, A + a • F, B, C] = f ![X, F, A, B, C] := by
    convert! alternating_update_add_multiple f ![X, F, A, B, C]
      (i := 2) (j := 1) (by decide) a using 1
    congr 1
    ext i
    fin_cases i <;> simp
  have h₃ : f ![X, F, A + a • F, B + b • F, C] = f ![X, F, A + a • F, B, C] := by
    convert! alternating_update_add_multiple f ![X, F, A + a • F, B, C]
      (i := 3) (j := 1) (by decide) b using 1
    congr 1
    ext i
    fin_cases i <;> simp
  have h₄ : f ![X, F, A + a • F, B + b • F, C + c • F] =
      f ![X, F, A + a • F, B + b • F, C] := by
    convert! alternating_update_add_multiple f ![X, F, A + a • F, B + b • F, C]
      (i := 4) (j := 1) (by decide) c using 1
    congr 1
    ext i
    fin_cases i <;> simp
  exact h₄.trans (h₃.trans h₂)
