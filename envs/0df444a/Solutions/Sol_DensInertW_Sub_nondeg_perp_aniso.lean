-- Prove2me | solution 1 for DensInertW.Sub.nondeg_perp_aniso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:05.296304+00:00
-- url     : https://prove2.me/submissions/63a06bd0-3dc3-4d6b-800a-9b18c3775788

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne
import Theorems.Thm_DensInertW_Sub_hf_add_right
import Theorems.Thm_DensInertW_Sub_hf_smul_right
import Theorems.Thm_DensInertW_Sub_sub_mem_perp

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
theorem _root_.solution (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q)
    (W : Submodule L (Fin n → L)) (hW : NonDeg q M W) (e : Fin n → L) (he : e ∈ W)
    (hee : hf q M e e ≠ 0) : NonDeg q M (W ⊓ LinearMap.ker (hfL q M e)) := by
  intro w hw hperp
  have hw' := Submodule.mem_inf.1 hw
  have hwe : hf q M w e = 0 := LinearMap.mem_ker.1 hw'.2
  apply hW w hw'.1
  intro v hv
  have h1 := hperp _ (sub_mem_perp W e he hee v hv)
  have hsplit : v = (v - (hf q M v e / hf q M e e) • e) + (hf q M v e / hf q M e e) • e :=
    (sub_add_cancel _ _).symm
  rw [hsplit, hf_add_right hadd, h1, hf_smul_right, hwe]
  ring
end DensInertW.Sub
