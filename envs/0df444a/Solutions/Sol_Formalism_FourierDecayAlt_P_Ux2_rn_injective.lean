-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.rn_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:29:26.279347+00:00
-- url     : https://prove2.me/submissions/d786b0ee-4ce9-44b3-8ab2-63a67cfbd7f9

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_wMat_sq_assoc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_block3_injective
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_skewOf_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_skewOf_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux2
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux2
theorem _root_.solution : Function.Injective (Rn k j ρ) := by
  intro x y h
  unfold Rn at h
  obtain ⟨-, -, h13, -, -, h23, -, -, -⟩ := block3_injective h
  have h1 : x.1 = y.1 := by funext i a; exact congrFun (congrFun h23 i) a
  have hw := congrArg (G.wMat j * ·) h13
  simp only [wMat_sq_assoc] at hw
  rw [h1] at hw
  have hs : skewOf x.2 = skewOf y.2 := add_left_cancel hw
  have h2 : x.2 = y.2 := by
    refine Prod.ext ?_ ?_
    · funext p
      have := congrFun (congrFun hs p.1.1) p.1.2
      rw [skewOf_lt _ p.2, skewOf_lt _ p.2] at this
      exact this
    · funext a
      have := congrArg Complex.im (congrFun (congrFun hs a) a)
      rw [skewOf_diag, skewOf_diag] at this
      simpa using this
  exact Prod.ext h1 h2
end Formalism.FourierDecayAlt.P.Ux2
