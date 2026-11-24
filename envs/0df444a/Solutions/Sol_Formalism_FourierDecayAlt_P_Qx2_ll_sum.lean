-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.ll_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:46:40.092479+00:00
-- url     : https://prove2.me/submissions/ca54b5df-1283-4071-84dd-9d1b72f09b4c

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_ll_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add

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
theorem _root_.solution {ι : Type*} (s : Finset ι) (T : ι → (Mx k r → E) → Mx k r → E)
    (hT : ∀ j ∈ s, LL k r i D (T j)) : LL k r i D (fun f x => ∑ j ∈ s, T j f x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ll_zero
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact LL.add (hT a (Finset.mem_insert_self a s)) (ih fun j hj => hT j (Finset.mem_insert_of_mem hj))
end Formalism.FourierDecayAlt.P.Qx2
