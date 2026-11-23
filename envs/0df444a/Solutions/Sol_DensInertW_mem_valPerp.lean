-- Prove2me | solution 1 for DensInertW.mem_valPerp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:52:08.171879+00:00
-- url     : https://prove2.me/submissions/a35ed133-3630-4695-99ba-6ee5bbd46aad

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
theorem _root_.solution {W : Submodule L (Fin n → L)} {e v : Fin n → L} :
    v ∈ valPerp q M W e ↔ v ∈ W ∧ hf q M v e = 0 := by
  simp only [valPerp, Submodule.mem_map, LinearMap.mem_ker, LinearMap.domRestrict_apply,
    valL_apply, Submodule.subtype_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hv, h⟩
    exact ⟨⟨v, hv⟩, h, rfl⟩
end DensInertW
