-- Prove2me | solution 1 for Deduction.poleData_inv_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:11:35.157123+00:00
-- url     : https://prove2.me/submissions/d440fc36-661c-4e52-8957-629f37ed1ded

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LogDerivLocal
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LFunctionConj
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_CharFamilyLFunctionNeZeroOfOneLeRe
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_mellinGchiOfNeOne
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_mellinGchiModOne
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_measurableGchi
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_GchiGrowth
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_GchiConj
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_poleData
import Theorems.Thm_Deduction_LFunction_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
namespace Deduction
theorem _root_.solution {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (ρ : ℂ) :
    DirichletCharacter.LFunction χ⁻¹ ρ = 0 ↔
      DirichletCharacter.LFunction χ ((starRingEnd ℂ) ρ) = 0 := by
  have := LFunction_conj χ ((starRingEnd ℂ) ρ)
  rw [Complex.conj_conj] at this
  rw [this, map_eq_zero]
end Deduction
