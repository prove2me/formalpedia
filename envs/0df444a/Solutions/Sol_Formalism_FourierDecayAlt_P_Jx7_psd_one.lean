-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.psd_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:58:24.103738+00:00
-- url     : https://prove2.me/submissions/bdc55ff5-a947-4d3a-b020-b3911f142c33

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA

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
variable {α : Type} {F : Finset α}
namespace Formalism.FourierDecayAlt.P.Jx7
theorem _root_.solution : TB.PSDOn F (fun _ _ : α => (1 : ℂ)) := by
  unfold TB.PSDOn
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext x y; simp [Matrix.conjTranspose_apply]
  · intro x
    have : star x ⬝ᵥ (Matrix.of fun _ _ : F => (1 : ℂ)) *ᵥ x = star (∑ i, x i) * ∑ i, x i := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, star_sum, one_mul,
        Finset.sum_mul]
    rw [this]; exact star_mul_self_nonneg _
end Formalism.FourierDecayAlt.P.Jx7
