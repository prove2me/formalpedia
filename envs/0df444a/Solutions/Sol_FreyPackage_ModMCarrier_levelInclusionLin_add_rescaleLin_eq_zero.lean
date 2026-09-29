-- Prove2me | solution 1 for FreyPackage.ModMCarrier.levelInclusionLin_add_rescaleLin_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/e697290e-63ea-5aae-9a0c-09126eb4ec24

import Mathlib
import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_FreyPackage_ModMCarrier_OldSublattice
import Theorems.Thm_CuspForm_eq_zero_of_coe_add_slash_heckeDiagMatrix_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FreyPackage_ModMCarrier_levelInclusionLin_add_rescaleLin_eq_zero
p2m_attr_erase "instance" "Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway"

open CongruenceSubgroup FreyPackage.ModMCarrier
open scoped ModularForm MatrixGroups

theorem solution
    {R M q' : ℕ} [NeZero M] (hq' : q'.Prime) (hq'R : ¬ q' ∣ R) (hRM : R ∣ M) (hqRM : q' * R ∣ M)
    (x y : CuspForm (CongruenceSubgroup.Gamma0 R) 2)
    (h : levelInclusionLin hRM 2 x + rescaleLin hqRM 2 y = 0) : x = 0 ∧ y = 0 := by
  haveI : NeZero R := ⟨by rintro rfl; exact NeZero.ne M (Nat.eq_zero_of_zero_dvd hRM)⟩
  have h' := congrArg (fun f : CuspForm (CongruenceSubgroup.Gamma0 M) 2 => (⇑f : UpperHalfPlane → ℂ)) h
  simp only [CuspForm.coe_add, CuspForm.coe_zero, coe_levelInclusionLin, coe_rescaleLin_apply] at h'
  exact CuspForm.eq_zero_of_coe_add_slash_heckeDiagMatrix_eq_zero hq' hq'R 2 x y h'

end S_FreyPackage_ModMCarrier_levelInclusionLin_add_rescaleLin_eq_zero
end P2MW
export P2MW.S_FreyPackage_ModMCarrier_levelInclusionLin_add_rescaleLin_eq_zero (solution)
