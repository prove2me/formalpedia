-- Prove2me | solution 1 for CompactnessConjecture.kernelNormalForm_kAdmissible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/f1f2d8d9-15b8-4665-ac5e-bd54b16d9588

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {V : Type*} (g : KVertex → V)
    (hcolor : ∀ u v, g u = g v → kColor u = kColor v)
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn g {v : KVertex | v.1 = copy}) :
    KAdmissible (kernelNormalForm g) := by
  refine ⟨?_, ?_⟩
  · intro u v huv
    exact hcolor u v ((kernelNormalForm_eq_iff g u v).mp huv)
  · intro copy u hu v hv huv
    exact hcopies copy hu hv
      ((kernelNormalForm_eq_iff g _ _).mp huv)
end CompactnessConjecture
