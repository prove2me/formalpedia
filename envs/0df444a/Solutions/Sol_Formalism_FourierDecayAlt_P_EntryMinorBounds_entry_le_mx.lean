-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EntryMinorBounds.entry_le_mx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:36:33.457062+00:00
-- url     : https://prove2.me/submissions/ac5e0028-04f1-4abe-91ef-de998ca8f7d6

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
theorem _root_.solution {α β : Type*} [Fintype α] [Fintype β] (M : Matrix α β ℂ) (i : α) (j : β) :
    ‖M i j‖ ≤ C2.mx M := by
  unfold C2.mx
  exact (norm_le_pi_norm (fun j => M i j) j).trans (norm_le_pi_norm (Matrix.of.symm M) i)
end Formalism.FourierDecayAlt.P.EntryMinorBounds
