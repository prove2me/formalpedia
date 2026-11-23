-- Prove2me | solution 1 for DensInertW.val_aniso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:19.588219+00:00
-- url     : https://prove2.me/submissions/be08f436-be1c-4bea-aeb8-824e468c1818

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankValPerp
import Theorems.Thm_DensInertW_val_smul_right
import Theorems.Thm_DensInertW_val_add_right
import Theorems.Thm_DensInertW_val_symm
import Theorems.Thm_DensInertW_exists_trace_ne_zero
import Theorems.Thm_DensInertW_frob_frob


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
noncomputable section
open DensInertW
variable {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L] {n : ℕ}
  {M : Matrix (Fin n) (Fin n) L}
namespace DensInertW
theorem _root_.solution [Fintype L] (h2 : finrank K L = 2) (hM : IsHerm (Fintype.card K) M)
    {W : Submodule L (Fin n → L)} (hW : NonDeg (Fintype.card K) M W) (hne : W ≠ ⊥) :
    ∃ e ∈ W, hf (Fintype.card K) M e e ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨v, hv, hwv⟩ : ∃ v ∈ W, hf (Fintype.card K) M w v ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (hW w hw h)
  obtain ⟨c, hc⟩ := exists_trace_ne_zero h2 _ (pow_ne_zero (Fintype.card K) hwv)
  apply hc
  have h := hcon (w + c • v) (W.add_mem hw (W.smul_mem c hv))
  simp only [val_add_left, val_add_right, val_smul_left, val_smul_right] at h
  rw [hcon w hw, hcon v hv, val_symm h2 hM w v] at h
  rw [mul_pow, frob_frob h2]
  linear_combination h
end DensInertW
