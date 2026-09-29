-- Prove2me | solution 1 for CuspForm.atkinLehnerLin_eq_neg_qCoeff_smul_of_isNewform
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/e1f1369f-b0fd-5af8-a8fa-f0bb8dd4f5a6

import Mathlib
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Definitions.Def_CuspForm_LevelLoweringTrace
import Theorems.Thm_CuspForm_traceLin_atkinLehnerLin_eq_zero_of_isNewform
import Theorems.Thm_ModularForm_alSlash_add_heckeU_alSlash_alSlash
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_heckeT
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_atkinLehnerLin_eq_neg_qCoeff_smul_of_isNewform
p2m_attr_erase "simp" "ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply"

theorem solution {N q : ℕ} [NeZero N]
    (W : ModularForm.AtkinLehnerDatum N q) (hq : q.Prime)
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNewform) :
    CuspForm.atkinLehnerLin W 2 f = (-ModularFormClass.qCoeff f q) • f := by
  have hqN : q ∣ N := ⟨W.R, W.hM⟩
  haveI : NeZero W.R := ⟨(ModularForm.AtkinLehnerDatum.R_pos W).ne'⟩
  have hfeig := (CuspForm.isNormalizedEigenform_iff_heckeT f).mp hf.1
  have eU : ModularForm.heckeU 2 q ⇑f = ModularFormClass.qCoeff f q • ⇑f := (hfeig.2 q hq).2 hqN
  have hginv : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)),
      SlashAction.map (2 : ℤ) γ ⇑f = ⇑f := fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ

  have h0 := congrArg DFunLike.coe (CuspForm.traceLin_atkinLehnerLin_eq_zero_of_isNewform W hq hf)
  rw [CuspForm.coe_traceLin_apply, CuspForm.coe_atkinLehnerLin_apply] at h0
  have h := ModularForm.alSlash_add_heckeU_alSlash_alSlash W 2 hginv
  have h2 : ((q : ℂ) ^ ((2 : ℤ) - 2)) = 1 := by norm_num
  rw [h2, one_smul] at h
  rw [h] at h0
  have h0' : ModularForm.alSlash W 2 ⇑f + ModularForm.heckeU 2 q ⇑f = 0 := h0
  apply DFunLike.coe_injective
  show ⇑(CuspForm.atkinLehnerLin W 2 f) = ⇑((-ModularFormClass.qCoeff f q) • f)
  rw [CuspForm.coe_atkinLehnerLin_apply, CuspForm.IsGLPos.coe_smul, _root_.neg_smul, ← eU]
  exact eq_neg_of_add_eq_zero_left h0'

end S_CuspForm_atkinLehnerLin_eq_neg_qCoeff_smul_of_isNewform
end P2MW
export P2MW.S_CuspForm_atkinLehnerLin_eq_neg_qCoeff_smul_of_isNewform (solution)
