-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.omOK_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:39:37.247832+00:00
-- url     : https://prove2.me/submissions/7553c36c-e94d-4395-b79e-fcd42cc441e8

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementGK
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KernelFromKOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_WModel
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_WChain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (K : Type) [NormedField K] (p : ℕ) :
    OmOK p 1 (fun _ _ => (1 : K)) (fun _ _ => (1 : K)) := by
  refine ⟨fun _ _ => by simp, fun _ _ => by simp, ?_⟩
  intro a b hab
  have hlt : ∀ c : ZMod (2 * 1), c.val < 2 := fun c => ZMod.val_lt c
  have hval : a.val = b.val := by
    have := hlt a
    have := hlt b
    omega
  have : a = b := ZMod.val_injective _ hval
  simp [this]
end Formalism.InvariantFactorPaths.G7
