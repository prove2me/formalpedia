-- Prove2me | solution 1 for FiniteEnergyPlane.liouville_ofR4_ofR4
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T22:56:54.214114+00:00
-- url     : https://prove2.me/submissions/1fe2bb88-985e-4119-a381-7c11566fd96b

import Definitions.Def_FiniteEnergyPlane_Winding



namespace FiniteEnergyPlane

theorem liouville_ofR4_ofR4_aux (x v : HryniewiczCriterion.R4) :
    liouville (ofR4 x) (ofR4 v) = HryniewiczCriterion.liouvilleForm x v := by
  change (∑ k : Fin 4, (j0 (n := 1) (ofR4 x) : Fin 4 → ℝ) k * (ofR4 v : Fin 4 → ℝ) k) / 2 = _
  rw [Fin.sum_univ_four]
  simp [j0, ofR4, HryniewiczCriterion.liouvilleForm]
  ring

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution (x v : HryniewiczCriterion.R4) :
    liouville (ofR4 x) (ofR4 v) = HryniewiczCriterion.liouvilleForm x v :=
  liouville_ofR4_ofR4_aux x v
