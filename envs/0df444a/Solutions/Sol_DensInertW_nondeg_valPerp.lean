-- Prove2me | solution 1 for DensInertW.nondeg_valPerp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:05.612884+00:00
-- url     : https://prove2.me/submissions/63a4e12e-aa76-4968-8a14-ab20e81301de

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankValPerp
import Theorems.Thm_DensInertW_val_sub_left
import Theorems.Thm_DensInertW_val_smul_right
import Theorems.Thm_DensInertW_mem_valPerp
import Theorems.Thm_DensInertW_val_add_right

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
    {W : Submodule L (Fin n → L)} (hW : NonDeg (Fintype.card K) M W) {e : Fin n → L}
    (he : e ∈ W) (hb : hf (Fintype.card K) M e e ≠ 0) :
    NonDeg (Fintype.card K) M (valPerp (Fintype.card K) M W e) := by
  intro w hw hall
  rw [mem_valPerp] at hw
  apply hW w hw.1
  intro v hv
  have hv' : v - (hf (Fintype.card K) M v e / hf (Fintype.card K) M e e) • e ∈
      valPerp (Fintype.card K) M W e := by
    rw [mem_valPerp]
    refine ⟨W.sub_mem hv (W.smul_mem _ he), ?_⟩
    rw [val_sub_left, val_smul_left, div_mul_cancel₀ _ hb, sub_self]
  have h1 := hall _ hv'
  have hv2 : v = (hf (Fintype.card K) M v e / hf (Fintype.card K) M e e) • e +
      (v - (hf (Fintype.card K) M v e / hf (Fintype.card K) M e e) • e) := by abel
  rw [hv2, val_add_right, val_smul_right, hw.2, h1]
  ring
end DensInertW
