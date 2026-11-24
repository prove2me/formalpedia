-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.sandw_hat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:43:35.795114+00:00
-- url     : https://prove2.me/submissions/cf047381-fd28-4f55-b215-07ecfb8f25d2

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_good_oMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_hatM_oMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_good_TL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_good_TLs

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (H : HatData (Fn k r E))
variable {H}
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (hop : ∀ l q, H.Good (crd (opL l q))) (Y : ℂ) : ∀ (j : ℕ) (M : OM (Fn k r E)),
    (∀ a b, H.Good (M a b)) →
    (∀ a b, H.Good (sandw k r Y j M a b)) ∧ hatM H (sandw k r Y j M) = Lp H Y j * hatM H M * Rp H Y j
  | 0, M, hM => ⟨hM, by simp [sandw, Lp, Rp]⟩
  | j + 1, M, hM => by
    by_cases hj : j < r
    · have e : sandw k r Y (j + 1) M = sandw k r Y j (oMul (TLs k ⟨j, hj⟩ Y) (oMul M (TL k ⟨j, hj⟩ Y))) := by
        show sandw k r Y j _ = _
        rw [dif_pos hj]
      have g1 := good_oMul hM (good_TL hop ⟨j, hj⟩ Y)
      have g2 := good_oMul (good_TLs hop ⟨j, hj⟩ Y) g1
      obtain ⟨h1, h2⟩ := solution hop Y j _ g2
      rw [e]
      refine ⟨h1, ?_⟩
      rw [h2, hatM_oMul (good_TLs hop ⟨j, hj⟩ Y) g1, hatM_oMul hM (good_TL hop ⟨j, hj⟩ Y)]
      simp only [Lp, Rp, dif_pos hj, Matrix.mul_assoc]
    · have e : sandw k r Y (j + 1) M = sandw k r Y j M := by
        show sandw k r Y j _ = _
        rw [dif_neg hj]
      obtain ⟨h1, h2⟩ := solution hop Y j M hM
      rw [e]
      refine ⟨h1, ?_⟩
      rw [h2]
      simp only [Lp, Rp, dif_neg hj, Matrix.mul_one, Matrix.one_mul]
end Formalism.FourierDecayAlt.P.Qx6
