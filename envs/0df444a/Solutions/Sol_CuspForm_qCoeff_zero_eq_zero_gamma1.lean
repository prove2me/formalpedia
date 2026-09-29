-- Prove2me | solution 1 for CuspForm.qCoeff_zero_eq_zero_gamma1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/5cdde7b2-87dd-5a98-9f43-040ac2cc9b3d

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CongruenceSubgroup_isCusp_infty_gamma1_mapGL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_qCoeff_zero_eq_zero_gamma1

open ModularFormClass UpperHalfPlane

theorem solution
    {M : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma1 M) k) :
    ModularFormClass.qCoeff f 0 = 0 := by
  haveI : Fact (IsCusp OnePoint.infty (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
      (CongruenceSubgroup.Gamma1 M))) := ⟨CongruenceSubgroup.isCusp_infty_gamma1_mapGL M⟩
  have hz : IsZeroAtImInfty (⇑f) := CuspFormClass.zero_at_infty f
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
    rw [CongruenceSubgroup.Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [ModularGroup.coe_T, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.head_fin_const]
  have hper : (1:ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
      (CongruenceSubgroup.Gamma1 M)).strictPeriods := by
    rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_map]
    refine ⟨ModularGroup.T, hT, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.upperRightHom, ModularGroup.coe_T,
        Matrix.SpecialLinearGroup.mapGL, Matrix.SpecialLinearGroup.toGL,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  show (PowerSeries.coeff 0) (UpperHalfPlane.qExpansion 1 ⇑f) = 0
  rw [UpperHalfPlane.qExpansion_coeff_zero one_pos
        (ModularFormClass.analyticAt_cuspFunction_zero f one_pos hper)
        (SlashInvariantFormClass.periodic_comp_ofComplex f hper)]
  exact hz.valueAtInfty_eq_zero

end S_CuspForm_qCoeff_zero_eq_zero_gamma1
end P2MW
export P2MW.S_CuspForm_qCoeff_zero_eq_zero_gamma1 (solution)
