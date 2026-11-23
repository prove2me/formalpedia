-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.t_DiagScale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:46.04311+00:00
-- url     : https://prove2.me/submissions/f4cdd7d4-e4a5-41ee-878c-1cecfcac4255

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
open scoped ComplexOrder ComplexConjugate Matrix
namespace Formalism.FourierDecayAlt.P.Jx7
theorem _root_.solution : DiagScale := by
  intro α F k a hk
  have h1 : TB.PSDOn F (fun x y => (a x : ℂ) * (a y : ℂ)) := by
    unfold TB.PSDOn
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext x y; simp [Matrix.conjTranspose_apply, mul_comm]
    · intro x
      have : star x ⬝ᵥ (Matrix.of fun i j : F => (a i : ℂ) * (a j : ℂ)) *ᵥ x =
          star (∑ i : F, (a i : ℂ) * x i) * ∑ i : F, (a i : ℂ) * x i := by
        rw [star_sum, Finset.sum_mul_sum]
        simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        simp; ring
      rw [this]; exact star_mul_self_nonneg _
  exact psd_mul h1 hk
end Formalism.FourierDecayAlt.P.Jx7
