-- Prove2me | solution 1 for CuspForm.traceLin_heckeULin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/398eca12-13d1-5769-a423-3e4566f198b6

import Mathlib
import Definitions.Def_CuspForm_LevelLoweringTrace
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Theorems.Thm_CuspForm_atkinLehnerLin_heckeULin
import Theorems.Thm_CuspForm_heckeULin_comm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_traceLin_heckeULin

set_option autoImplicit false

open ModularForm

theorem solution {M q : ℕ} [NeZero M] (A : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ℓ ∣ M) (hℓR : ℓ ∣ A.R) (hne : ℓ ≠ q) (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    haveI : NeZero A.R := ⟨A.R_pos.ne'⟩
    CuspForm.traceLin A hq (CuspForm.heckeULin 2 hℓM f) = CuspForm.heckeULin 2 hℓR (CuspForm.traceLin A hq f) := by
  haveI : NeZero A.R := ⟨A.R_pos.ne'⟩
  have hqM : q ∣ M := ⟨A.R, A.hM⟩
  refine DFunLike.coe_injective ?_
  show ⇑(CuspForm.traceLin A hq (CuspForm.heckeULin 2 hℓM f)) = ⇑(CuspForm.heckeULin 2 hℓR (CuspForm.traceLin A hq f))
  rw [CuspForm.coe_traceLin_apply, CuspForm.coe_heckeULin_apply, CuspForm.coe_heckeULin_apply,
    CuspForm.coe_traceLin_apply, heckeU_add]
  congr 1

  have hw : alSlash A 2 (heckeU 2 ℓ ⇑f) = heckeU 2 ℓ (alSlash A 2 ⇑f) := by
    have h := congrArg (fun g : CuspForm (CongruenceSubgroup.Gamma0 M) 2 => (⇑g : UpperHalfPlane → ℂ))
      (CuspForm.atkinLehnerLin_heckeULin A hq hℓ hℓM hne f)
    simpa only [CuspForm.coe_atkinLehnerLin_apply, CuspForm.coe_heckeULin_apply] using h
  rw [hw]

  have hc := CuspForm.heckeULin_comm (N := M) 2 hℓM hqM
  have h := congrArg (fun g : CuspForm (CongruenceSubgroup.Gamma0 M) 2 => (⇑g : UpperHalfPlane → ℂ))
    (LinearMap.ext_iff.mp hc.eq (CuspForm.atkinLehnerLin A 2 f))
  simpa only [Module.End.mul_apply, CuspForm.coe_heckeULin_apply, CuspForm.coe_atkinLehnerLin_apply] using h.symm

end S_CuspForm_traceLin_heckeULin
end P2MW
export P2MW.S_CuspForm_traceLin_heckeULin (solution)
