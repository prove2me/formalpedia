-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.hpart_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:58:23.732101+00:00
-- url     : https://prove2.me/submissions/9b1ce7e1-d0de-44c6-b5a2-584043c7de8e

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpk_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpart1_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpart2_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_inV_posL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_not_inV_eI
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_not_inV_esI
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_unit_col
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx2_unit_col__f12299f6bc02

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
theorem _root_.solution (i : Fin (r + 1)) (a b : Fin (mdim k r i)) :
    inLieLev k r i (hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) ∧
      inLieLev k r i (hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) := by
  have hb := inV_posL i b
  have ha' := inV_posL i a
  have hs : ∀ (c : ℂ) (A : Mx k r) (v : Fin (2 * r + k + 1) → ℂ), (c • A) *ᵥ v = c • (A *ᵥ v) :=
    fun c A v => by
      ext q
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  have e1 : ∀ p, ¬ inV k r i p →
      hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1) *ᵥ bvec p = 0 := by
    intro p hp
    rw [hpart1, hpk_inv, hs, Matrix.sub_mulVec, unit_col hb hp, unit_col' ha' hp,
      sub_zero, smul_zero]
  have e2 : ∀ p, ¬ inV k r i p →
      hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1) *ᵥ bvec p = 0 := by
    intro p hp
    rw [hpart2, hpk_inv, hs, Matrix.add_mulVec, unit_col hb hp, unit_col' ha' hp,
      add_zero, smul_zero]
  exact ⟨⟨hpart1_lie _, fun c hc => ⟨e1 _ (not_inV_eI hc), e1 _ (not_inV_esI hc)⟩⟩,
    ⟨hpart2_lie _, fun c hc => ⟨e2 _ (not_inV_eI hc), e2 _ (not_inV_esI hc)⟩⟩⟩
end Formalism.FourierDecayAlt.P.Qx2
