-- Prove2me | solution 1 for DensInertW.finrank_valPerp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:31.718863+00:00
-- url     : https://prove2.me/submissions/706eb311-888a-41a9-be6b-49035255b7bf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankValPerp
import Theorems.Thm_DensInertW_valL_apply

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
variable {L : Type} [Field L] {n : ℕ} {q : ℕ} {M : Matrix (Fin n) (Fin n) L}
namespace DensInertW
theorem _root_.solution {W : Submodule L (Fin n → L)} {e : Fin n → L} (he : e ∈ W)
    (hb : hf q M e e ≠ 0) : finrank L (valPerp q M W e) + 1 = finrank L W := by
  have hsurj : LinearMap.range ((valL q M e).domRestrict W) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro t
    refine ⟨⟨(t / hf q M e e) • e, W.smul_mem _ he⟩, ?_⟩
    simp only [LinearMap.domRestrict_apply, valL_apply, val_smul_left]
    exact div_mul_cancel₀ t hb
  have h := LinearMap.finrank_range_add_finrank_ker ((valL q M e).domRestrict W)
  rw [hsurj, finrank_top, finrank_self] at h
  rw [valPerp, Submodule.finrank_map_subtype_eq]
  omega
end DensInertW
