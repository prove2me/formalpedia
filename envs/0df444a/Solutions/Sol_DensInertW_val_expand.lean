-- Prove2me | solution 1 for DensInertW.val_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:58:29.647539+00:00
-- url     : https://prove2.me/submissions/dc049c40-1577-41c7-8488-8241a19132f2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankValPerp
import Theorems.Thm_DensInertW_val_smul_right
import Theorems.Thm_DensInertW_val_add_right
import Theorems.Thm_DensInertW_val_symm
import Theorems.Thm_DensInertW_one_lt_q


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
    (e w : Fin n → L) (hwe : hf (Fintype.card K) M w e = 0) (l : L) :
    hf (Fintype.card K) M (l • e + w) (l • e + w) =
      l ^ (Fintype.card K + 1) * hf (Fintype.card K) M e e + hf (Fintype.card K) M w w := by
  have hq := one_lt_q (K := K)
  have hew : hf (Fintype.card K) M e w = 0 := by
    rw [val_symm h2 hM w e, hwe, zero_pow (by omega)]
  simp only [val_add_left, val_add_right, val_smul_left, val_smul_right, hwe, hew]
  ring
end DensInertW
