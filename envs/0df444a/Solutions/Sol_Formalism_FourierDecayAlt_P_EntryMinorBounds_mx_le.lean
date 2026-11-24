-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EntryMinorBounds.mx_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:36:39.090391+00:00
-- url     : https://prove2.me/submissions/f08d0f6e-f8d8-421c-8de4-6cc8bd98228d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryMinorBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.EntryMinorBounds
namespace Formalism.FourierDecayAlt.P.EntryMinorBounds
theorem _root_.solution {α β : Type*} [Fintype α] [Fintype β] (M : Matrix α β ℂ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i j, ‖M i j‖ ≤ c) : C2.mx M ≤ c := by
  unfold C2.mx
  apply (pi_norm_le_iff_of_nonneg hc).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hc).mpr
  intro j
  exact h i j
end Formalism.FourierDecayAlt.P.EntryMinorBounds
