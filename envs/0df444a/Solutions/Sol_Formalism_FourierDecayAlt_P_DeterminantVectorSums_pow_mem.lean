-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DeterminantVectorSums.pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:55:10.204806+00:00
-- url     : https://prove2.me/submissions/497528e1-dca2-458e-979a-3d6d80d9cfd1

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StarSumLemmas
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DeterminantVectorSums
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {W : Type} [AddCommGroup W] [Module ℂ W]
namespace Formalism.FourierDecayAlt.P.DeterminantVectorSums
theorem _root_.solution (G : Submodule ℂ W) (K : Module.End ℂ W) (hK : ∀ x ∈ G, K x ∈ G) (s : ℕ) : ∀ x ∈ G, (K ^ s) x ∈ G := by
  induction s with
  | zero => intro x hx; simpa using hx
  | succ s ih =>
    intro x hx
    rw [pow_succ', Module.End.mul_apply]
    exact hK _ (ih x hx)
end Formalism.FourierDecayAlt.P.DeterminantVectorSums
