-- Prove2me | solution 1 for DensInertW.val_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:38.315839+00:00
-- url     : https://prove2.me/submissions/4d5393c3-2ebf-44c2-99c9-048dda17b253

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankValPerp
import Theorems.Thm_DensInertW_card_norm_fibre
import Theorems.Thm_DensInertW_card_norm_zero


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
theorem _root_.solution [Fintype L] [DecidableEq L] (h2 : finrank K L = 2) (b t : L) (hb : b ≠ 0)
    (hbq : b ^ Fintype.card K = b) (ht : t ^ Fintype.card K = t) :
    #{l : L | l ^ (Fintype.card K + 1) * b = t} = if t = 0 then 1 else Fintype.card K + 1 := by
  have e : (univ.filter fun l : L => l ^ (Fintype.card K + 1) * b = t) =
      univ.filter fun l : L => l ^ (Fintype.card K + 1) = t / b :=
    filter_congr (fun l _ => (eq_div_iff hb).symm)
  rw [e]
  split_ifs with h0
  · rw [h0, zero_div]
    exact card_norm_zero _
  · exact card_norm_fibre h2 _ (div_ne_zero h0 hb) (by rw [div_pow, ht, hbq])
end DensInertW
