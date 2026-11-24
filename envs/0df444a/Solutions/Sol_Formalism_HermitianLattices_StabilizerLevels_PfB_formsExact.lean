-- Prove2me | solution 1 for Formalism.HermitianLattices.StabilizerLevels.PfB.formsExact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:37:35.823743+00:00
-- url     : https://prove2.me/submissions/a1c97626-39b3-4923-9120-2da777616f9e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_CongruenceTorsion
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CongruenceSubgroupTorsionFree
import Theorems.Thm_Formalism_HermitianLattices_StabilizerLevels_PfB_liftForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.StabilizerLevels
open Formalism.HermitianLattices.StabilizerLevels.PfB
open NumberField IsDedekindDomain
open scoped TensorProduct
namespace Formalism.HermitianLattices.StabilizerLevels.PfB
theorem _root_.solution : FormsExact := by
  intro G _ Γ U hst W₁ W₂ W₃ _ _ _ _ _ _ a b ha hb hex
  refine ⟨fun f hf h0 => ?_, fun hsur f'' hf'' => ?_⟩
  · exact liftForm Γ U hst a ha f hf (fun g => (hex _).1 (h0 g))
  · exact liftForm Γ U hst b hb f'' hf'' (fun g => hsur _)
end Formalism.HermitianLattices.StabilizerLevels.PfB
