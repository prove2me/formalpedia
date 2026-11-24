-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.polyAt_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:01:32.551162+00:00
-- url     : https://prove2.me/submissions/20e009f1-ac2c-454b-86dd-359da3079115

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_polyAt_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add

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
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.Qx2
theorem _root_.solution {ι : Type*} {N : ℕ} (s : Finset ι) (φ : ι → ℂ → E) (H : ∀ j ∈ s, PolyAt N (φ j)) :
    PolyAt N (fun Y => ∑ j ∈ s, φ j Y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact polyAt_zero N
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact PolyAt.add (H a (Finset.mem_insert_self a s)) (ih fun j hj => H j (Finset.mem_insert_of_mem hj))
end Formalism.FourierDecayAlt.P.Qx2
