-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.integral_ring_second_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:15:22.00252+00:00
-- url     : https://prove2.me/submissions/5ab29a86-0e44-448c-a89a-acef1709d2ce

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_exponent_le_over_ring_holds
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_application_window

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
namespace Formalism.CohomologicalDescent.DepthNonnegative
theorem _root_.solution : WeightSpacePrimePowerBoundOverDomain := by
  intro hD R _ _ l N k j t q h lam xm xp ecl hl hu hh ht hS hecl I w hw x hx
  obtain ⟨hrows, hanti, hblock, hspread, hcloud, hlows, habove, hle, htop⟩ := hS
  have hA := application_window hD l k j t q h lam xm xp hl ht
  rw [hrows] at hA
  have hE := hA hanti hblock hspread hh hcloud hlows habove hle htop ecl hecl I w hw
  exact exponent_le_over_ring_holds R l N (res N lam) w _ hu hE x hx
end Formalism.CohomologicalDescent.DepthNonnegative
