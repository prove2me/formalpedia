-- Prove2me | solution 1 for DensInertW.ar_zero_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:39:46.651212+00:00
-- url     : https://prove2.me/submissions/d2081706-eb86-4db8-9ce1-68a6467e2a8f

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
theorem _root_.solution (q n m c : ℕ) (h : n + 1 ≤ m + c) :
    Formalism.L2.SG.DensExact.densProd q (-1) n m c = 0 := by
  unfold Formalism.L2.SG.DensExact.densProd
  exact Finset.prod_eq_zero (i := 0) (Finset.mem_Icc.mpr ⟨by omega, Nat.zero_le _⟩) (by simp)
end DensInertW
