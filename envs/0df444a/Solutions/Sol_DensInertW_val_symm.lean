-- Prove2me | solution 1 for DensInertW.val_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:42.710355+00:00
-- url     : https://prove2.me/submissions/06b5a38e-9b19-4d76-aa6f-8897a7318325

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankValPerp
import Theorems.Thm_DensInertW_frob_frob
import Theorems.Thm_DensInertW_frob_sum


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
    (x y : Fin n → L) : hf (Fintype.card K) M y x = (hf (Fintype.card K) M x y) ^ Fintype.card K := by
  unfold hf
  rw [frob_sum]
  simp_rw [frob_sum, mul_pow, frob_frob h2]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [← hM]
  ring
end DensInertW
