-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.sum_posL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:45:18.044773+00:00
-- url     : https://prove2.me/submissions/9c7108d8-e641-4e25-af78-bff01cfb1846

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_posL_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_exists_posL

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
variable {k r : ℕ} {i : Fin (r + 1)}
namespace Formalism.FourierDecayAlt.P.Qx2
theorem _root_.solution (F : Fin (2 * r + k + 1) → ℂ) (h : ∀ p, ¬ inV k r i p → F p = 0) :
    ∑ j, F (posL k r i j) = ∑ p, F p := by
  have key : ∑ p ∈ Finset.univ.image (posL k r i), F p = ∑ j, F (posL k r i j) :=
    Finset.sum_image (by intro x _ y _ e; exact posL_inj i e)
  rw [← key]
  refine Finset.sum_subset (Finset.subset_univ _) fun p _ hp => h p fun hv => hp ?_
  obtain ⟨j, hj⟩ := exists_posL hv
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
end Formalism.FourierDecayAlt.P.Qx2
