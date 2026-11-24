-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.curve_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:21:21.743607+00:00
-- url     : https://prove2.me/submissions/2e430837-fa0f-41d1-ae8c-df4b99dff40f

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_exp_fix
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_exp_mem
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul


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
open Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx2
theorem _root_.solution {i : Fin (r + 1)} {g X : Mx k r} (hg : g ∈ Glev k r i) (hX : inLieLev k r i X) (t : ℝ) :
    g * NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i := by
  refine ⟨WeylGroupFacts.uh_mul hg.1 (B5.exp_mem hX.1 t), fun a ha => ⟨?_, ?_⟩⟩
  · rw [← Matrix.mulVec_mulVec, exp_fix (hX.2 a ha).1, (hg.2 a ha).1]
  · rw [← Matrix.mulVec_mulVec, exp_fix (hX.2 a ha).2, (hg.2 a ha).2]
end Formalism.FourierDecayAlt.P.Qx2
