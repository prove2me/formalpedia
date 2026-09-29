-- Prove2me | solution 2 for DiazModulus.hermite_lindemann_holds
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:16:33.550587+00:00
-- url     : https://prove2.me/submissions/1cee3eb3-5ab6-4281-9a6c-eb9645d04531

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_Schanuel_lindemann_weierstrass

open Complex ComplexConjugate

open DiazModulus in
theorem solution : HermiteLindemann := by
  intro a ha0 ha he
  refine Schanuel.lindemann_weierstrass 2 ![a, 0] ![1, -Complex.exp a] ?_ ?_ ?_ ⟨0, by simp⟩ ?_
  · intro i; fin_cases i
    exacts [ha, isAlgebraic_zero]
  · intro i j; fin_cases i, j <;> simp [ha0, ha0.symm]
  · intro i; fin_cases i
    exacts [isAlgebraic_one, he.neg]
  · simp [Fin.sum_univ_two]

#print axioms solution
