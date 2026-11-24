-- Prove2me | solution 1 for Formalism.HermitianLattices.StabilizerLevels.PfB.stabG_of_proG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:21:20.643523+00:00
-- url     : https://prove2.me/submissions/264abcee-dfa5-4589-9b6f-7ccecd2d7ce6

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_CongruenceTorsion
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CongruenceSubgroupTorsionFree
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.StabilizerLevels
open Formalism.HermitianLattices.StabilizerLevels.PfB
open NumberField IsDedekindDomain
open scoped TensorProduct
namespace Formalism.HermitianLattices.StabilizerLevels.PfB
theorem _root_.solution (h : StabLevelProG) : StabLevelG := by
  intro F E _ _ _ _ _ k σ J h1 h2 h3 h4 U hU w g hg hgw hk hx
  refine h F E k σ J h1 h2 h3 h4 U hU w g hg hgw hk ?_
  intro x hxU
  refine ⟨0, fun i j => ?_⟩
  simpa using hx x hxU i j
end Formalism.HermitianLattices.StabilizerLevels.PfB
