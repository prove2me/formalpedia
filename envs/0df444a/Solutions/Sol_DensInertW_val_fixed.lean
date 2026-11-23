-- Prove2me | solution 1 for DensInertW.val_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:58:41.863741+00:00
-- url     : https://prove2.me/submissions/17da8dba-82fe-4363-86a5-853997f41ff1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankValPerp
import Theorems.Thm_DensInertW_val_symm

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
    (x : Fin n → L) : (hf (Fintype.card K) M x x) ^ Fintype.card K = hf (Fintype.card K) M x x :=
  (val_symm h2 hM x x).symm
end DensInertW
