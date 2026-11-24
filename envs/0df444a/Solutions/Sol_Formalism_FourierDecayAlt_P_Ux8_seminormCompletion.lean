-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux8.seminormCompletion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:42:22.609989+00:00
-- url     : https://prove2.me/submissions/26593a01-3ff8-4d41-974c-b9dbd4a40f28

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux8
namespace Formalism.FourierDecayAlt.P.Ux8
theorem _root_.solution : SeminormCompletion := by
  intro V _ _ p Cp hp
  let L : V →ₗ[ℂ] SW p :=
    { toFun := fun v => (v : SW p)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hL : ∀ v, ‖L v‖ = p v := fun _ => rfl
  let Lc : V →L[ℂ] SW p := L.mkContinuous Cp (fun v => by rw [hL]; exact hp v)
  refine ⟨UniformSpace.Completion (SW p), inferInstance, inferInstance, inferInstance,
    UniformSpace.Completion.toComplL.comp Lc, ?_, ?_⟩
  · intro v
    show ‖((Lc v : SW p) : UniformSpace.Completion (SW p))‖ = p v
    rw [UniformSpace.Completion.norm_coe]
    exact hL v
  · have hs : Function.Surjective (Lc : V → SW p) := fun v => ⟨v, rfl⟩
    rw [ContinuousLinearMap.coe_comp', UniformSpace.Completion.coe_toComplL]
    exact UniformSpace.Completion.denseRange_coe.comp hs.denseRange
      (UniformSpace.Completion.continuous_coe _)
end Formalism.FourierDecayAlt.P.Ux8
