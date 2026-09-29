-- Prove2me | solution 1 for CuspForm.newformBadPrimeCoeff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/5eb31604-c850-5c7d-a99b-4f7150fd01ac

import Mathlib
import Definitions.Def_CuspForm_Newforms
import Theorems.Thm_CuspForm_qCoeff_sq_eq_one_of_isNewform
import Theorems.Thm_CuspForm_qCoeff_eq_zero_of_isNewform_of_sq_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_newformBadPrimeCoeff
p2m_attr_erase "simp" "ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.coe_traceLin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply CuspForm.coe_heckeULowerLin_apply"

theorem solution (N : ℕ) : CuspForm.NewformBadPrimeCoeff N :=
  fun _f hf q hq hqN =>
    ⟨fun hsq => CuspForm.qCoeff_sq_eq_one_of_isNewform hf q hq hqN hsq,
     fun hsq => CuspForm.qCoeff_eq_zero_of_isNewform_of_sq_dvd hf q hq hsq⟩

end S_CuspForm_newformBadPrimeCoeff
end P2MW
export P2MW.S_CuspForm_newformBadPrimeCoeff (solution)
