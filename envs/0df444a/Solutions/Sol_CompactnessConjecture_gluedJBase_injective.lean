-- Prove2me | solution 1 for CompactnessConjecture.gluedJBase_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/aafe744e-73d3-42ee-bdbf-8bb9060e1cf6

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (hdistinct :
      copies 0 (.inl (.inl (0 : Fin 3))) ≠
        copies 1 (.inl (.inl (0 : Fin 3)))) :
    Function.Injective (gluedJBase copies) := by
  have hcopy (index : Fin 2) {i j : Fin 3}
      (hij : i ≠ j) :
      copies index (.inl (.inl i)) ≠
        copies index (.inl (.inl j)) := by
    intro h
    apply hij
    simpa using (copies index).injective h
  have h02 :
      copies 0 (.inl (.inl (0 : Fin 3))) ≠
        copies 0 (.inl (.inl (1 : Fin 3))) :=
    hcopy 0 (by decide)
  have h03 :
      copies 0 (.inl (.inl (0 : Fin 3))) ≠
        copies 0 (.inl (.inl (2 : Fin 3))) :=
    hcopy 0 (by decide)
  have h23 :
      copies 0 (.inl (.inl (1 : Fin 3))) ≠
        copies 0 (.inl (.inl (2 : Fin 3))) :=
    hcopy 0 (by decide)
  have h12 :
      copies 1 (.inl (.inl (0 : Fin 3))) ≠
        copies 0 (.inl (.inl (1 : Fin 3))) := by
    intro h
    exact (hcopy 1 (by decide : (0 : Fin 3) ≠ 1))
      (h.trans hfirst.symm)
  have h13 :
      copies 1 (.inl (.inl (0 : Fin 3))) ≠
        copies 0 (.inl (.inl (2 : Fin 3))) := by
    intro h
    exact (hcopy 1 (by decide : (0 : Fin 3) ≠ 2))
      (h.trans hsecond.symm)
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [gluedJBase]
end CompactnessConjecture
