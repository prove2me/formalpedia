-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BaseGramNonnegativity.sum_re_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:25.483005+00:00
-- url     : https://prove2.me/submissions/c95dece6-295f-47eb-bec3-10caece5ce70

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BaseGramNonnegativity
open Formalism.FourierDecayAlt.crystallineComparison Formalism.FourierDecayAlt.TB
namespace Formalism.FourierDecayAlt.P.BaseGramNonnegativity
theorem _root_.solution {α : Type} (Y : Finset α) (κ G : α → α → ℂ) (hκ : PSDOn Y κ) (hG : PSDOn Y G) :
    0 ≤ (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * G h h').re := by
  have H := (Matrix.PosSemidef.hadamard hκ hG).re_dotProduct_nonneg (fun _ => (1 : ℂ))
  simp only [dotProduct, Matrix.mulVec, Matrix.hadamard_apply, Matrix.of_apply, Pi.star_apply,
    star_one, one_mul, mul_one, RCLike.re_to_complex] at H
  convert H using 2
  rw [← Finset.sum_coe_sort Y]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [← Finset.sum_coe_sort Y]
end Formalism.FourierDecayAlt.P.BaseGramNonnegativity
