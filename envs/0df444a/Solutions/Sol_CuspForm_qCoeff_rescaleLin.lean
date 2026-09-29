-- Prove2me | solution 1 for CuspForm.qCoeff_rescaleLin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/5c0f1216-b4b5-597a-baac-48174ccd4aca

import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_qCoeff_rescaleLin

set_option autoImplicit false

open CongruenceSubgroup

namespace DeskWA_QCRL

private theorem d_ne_zero {d R M : ℕ} [NeZero M] (hdRM : d * R ∣ M) : d ≠ 0 := by
  rintro rfl
  exact NeZero.ne M (Nat.eq_zero_of_zero_dvd (by simpa using hdRM))

private theorem qCoeff_coe_smul {R : ℕ} (k : ℤ) (c : ℂ) (f : CuspForm (Gamma0 R) k) (m : ℕ) :
    ModularFormClass.qCoeff (⇑(c • f)) m = c * ModularFormClass.qCoeff (⇑f) m := by
  have hΓ := CongruenceSubgroup.one_mem_strictPeriods_Gamma0 R
  have han := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ
  unfold ModularFormClass.qCoeff
  rw [CuspForm.IsGLPos.coe_smul, UpperHalfPlane.qExpansion_smul han c]
  simp [smul_eq_mul]

private theorem main {d R M : ℕ} [NeZero M] (hdRM : d * R ∣ M) (k : ℤ)
    (f : CuspForm (Gamma0 R) k) (n : ℕ) :
    ModularFormClass.qCoeff (FreyPackage.ModMCarrier.rescaleLin hdRM k f) n
      = if d ∣ n then (d : ℂ) ^ (k - 1) * ModularFormClass.qCoeff f (n / d) else 0 := by
  have hd : d ≠ 0 := d_ne_zero hdRM
  have hΓ := CongruenceSubgroup.one_mem_strictPeriods_Gamma0 R
  have hfun : (⇑(FreyPackage.ModMCarrier.rescaleLin hdRM k f) : UpperHalfPlane → ℂ)
      = fun τ => (⇑(((d : ℂ) ^ (k - 1)) • f)) (ModularForm.heckeDiagMatrix d • τ) := by
    funext τ
    rw [FreyPackage.ModMCarrier.coe_rescaleLin_apply, ModularForm.slash_heckeDiagMatrix_apply k hd,
      CuspForm.IsGLPos.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [hfun, ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul (((d : ℂ) ^ (k - 1)) • f) hΓ hd n]
  split_ifs with h
  · rw [qCoeff_coe_smul]
  · rfl

end DeskWA_QCRL

theorem solution
    {d R M : ℕ} [NeZero M] (hdRM : d * R ∣ M) (k : ℤ)
    (f : CuspForm (Gamma0 R) k) (n : ℕ) :
    ModularFormClass.qCoeff (FreyPackage.ModMCarrier.rescaleLin hdRM k f) n
      = if d ∣ n then (d : ℂ) ^ (k - 1) * ModularFormClass.qCoeff f (n / d) else 0 :=
  DeskWA_QCRL.main hdRM k f n

end S_CuspForm_qCoeff_rescaleLin
end P2MW
export P2MW.S_CuspForm_qCoeff_rescaleLin (solution)
