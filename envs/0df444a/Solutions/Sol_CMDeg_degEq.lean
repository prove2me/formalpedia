-- Prove2me | solution 1 for CMDeg.degEq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:39.589538+00:00
-- url     : https://prove2.me/submissions/fe4e1f53-ca27-404a-bab6-b76ffa7b692c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_MassRatio
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDegreeEquality_FinrankEqTwo
import Theorems.Thm_CMDeg_finrank_eq_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
namespace CMDeg
theorem _root_.solution : Formalism.L2.SG.MassRatio.DegEq := by
  intro F E _ _ _ _ _ _ hFE
  have : IsTotallyComplex E := hFE.1.1
  have h2 := CMDeg.finrank_eq_two hFE
  have hQ : finrank ℚ F * finrank F E = finrank ℚ E := Module.finrank_mul_finrank ℚ F E
  have hC := IsTotallyComplex.finrank (K := E)
  have hP := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
  rw [IsTotallyComplex.nrRealPlaces_eq_zero, zero_add] at hP
  unfold Formalism.L2.SG.MassRatio.fF Formalism.HermitianLatticesTheory.fDeg
  rw [hP]
  rw [h2] at hQ
  omega
end CMDeg
