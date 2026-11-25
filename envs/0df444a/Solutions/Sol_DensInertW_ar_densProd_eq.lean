-- Prove2me | solution 1 for DensInertW.ar_densProd_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:20:56.775853+00:00
-- url     : https://prove2.me/submissions/37c65c39-b12d-4f56-88a1-48bd08ed4b0a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_DensExactInertOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_DensityProductAddTwoSuccSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open DensInertW
namespace DensInertW
theorem _root_.solution (q n m c : ℕ) :
    Formalism.L2.SG.DensExact.densProd q (-1) n m c = ∏ i ∈ Icc (n + 1 - (m + c)) n, arF q i := rfl
end DensInertW
