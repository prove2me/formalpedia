-- Prove2me | solution 1 for DensInertW.Sub.sub_mem_perp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:16.570077+00:00
-- url     : https://prove2.me/submissions/00ffe711-1180-47c1-b38c-424ae7879129

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne
import Theorems.Thm_DensInertW_Sub_hf_sub_left
import Theorems.Thm_DensInertW_Sub_hfL_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
open DensInertW DensInertW.Sub
variable {L : Type} [Field L]
variable {n : ℕ} {q : ℕ} {M : Matrix (Fin n) (Fin n) L}
namespace DensInertW.Sub
theorem _root_.solution (W : Submodule L (Fin n → L)) (e : Fin n → L) (he : e ∈ W)
    (hee : hf q M e e ≠ 0) (w : Fin n → L) (hw : w ∈ W) :
    w - (hf q M w e / hf q M e e) • e ∈ W ⊓ LinearMap.ker (hfL q M e) := by
  refine Submodule.mem_inf.2 ⟨W.sub_mem hw (W.smul_mem _ he), ?_⟩
  rw [LinearMap.mem_ker, hfL_apply, hf_sub_left, hf_smul_left, div_mul_cancel₀ _ hee, sub_self]
end DensInertW.Sub
