-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.hpart_lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:46:35.906628+00:00
-- url     : https://prove2.me/submissions/2c6ea56c-f8f7-4c4f-be04-7932d0b1b9cf

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_hpk_e
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_hpk_es
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_hpk_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_hpk_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_single_bvec
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_posL_ne_e
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_hpart_skew
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_sq


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx3
theorem _root_.solution (i : Fin (r + 1)) (a b : Fin (mdim k r i)) :
    inLieLev k r i (hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) ∧
    inLieLev k r i (hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) := by
  have hs := hpart_skew (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1) WeylGroupFacts.hpk_sq hpk_herm
  have hZh : (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ =
      Matrix.single (posL k r i b) (posL k r i a) 1 := by
    rw [Matrix.conjTranspose_single, star_one]
  have hkill : ∀ c : Fin r, c.val < i.val →
      (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ)) *ᵥ bvec (eI k r c) = 0 ∧
      (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ)) *ᵥ bvec (esI k r c) = 0 ∧
      (Hpk k r * (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ * Hpk k r) *ᵥ bvec (eI k r c) = 0 ∧
      (Hpk k r * (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ * Hpk k r) *ᵥ bvec (esI k r c) = 0 := by
    intro c hc
    refine ⟨single_bvec (posL_ne_e i b c hc).1, single_bvec (posL_ne_e i b c hc).2, ?_, ?_⟩
    · rw [← Matrix.mulVec_mulVec, hpk_e, ← Matrix.mulVec_mulVec, hZh, single_bvec (posL_ne_e i a c hc).2,
        Matrix.mulVec_zero]
    · rw [← Matrix.mulVec_mulVec, hpk_es, ← Matrix.mulVec_mulVec, hZh, single_bvec (posL_ne_e i a c hc).1,
        Matrix.mulVec_zero]
  refine ⟨⟨hs.1, fun c hc => ?_⟩, ⟨hs.2, fun c hc => ?_⟩⟩
  · obtain ⟨k1, k2, k3, k4⟩ := hkill c hc
    unfold hpart1
    rw [hpk_inv]
    simp only [Matrix.smul_mulVec, Matrix.sub_mulVec, k1, k2, k3, k4, sub_zero, smul_zero, and_self]
  · obtain ⟨k1, k2, k3, k4⟩ := hkill c hc
    unfold hpart2
    rw [hpk_inv]
    simp only [Matrix.smul_mulVec, Matrix.add_mulVec, k1, k2, k3, k4, add_zero, smul_zero, and_self]
end Formalism.FourierDecayAlt.P.Qx3
