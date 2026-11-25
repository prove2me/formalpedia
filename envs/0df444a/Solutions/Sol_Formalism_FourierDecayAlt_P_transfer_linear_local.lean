-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.transfer_linear_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:33:50.169811+00:00
-- url     : https://prove2.me/submissions/aa4e12b0-b041-4dbc-af45-7b089301383d

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_ll_tL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Q.TLinLoc := by
  intro E _ _ k r z z' i D Y p q f f₂ s hD hf hf₂ g hg
  have h := Qx2.ll_tL (E := E) (k := k) (r := r) (i := i) (D := D) hD z z' Y p q
  exact ⟨h.lin f f₂ s hf hf₂ g hg, fun he => h.loc f f₂ he g hg⟩
end Formalism.FourierDecayAlt.P
