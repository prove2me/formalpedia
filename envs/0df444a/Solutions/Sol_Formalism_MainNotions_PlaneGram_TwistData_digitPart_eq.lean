-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.digitPart_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:27:42.299796+00:00
-- url     : https://prove2.me/submissions/ef034323-8cff-4002-8039-6c5472c642a4

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_lsup_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable (D : TwistData K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) :
    D.digitPart p ρ F = D.digitPartL p ρ F := by
  rw [digitPartL, lsup_apply, digitPart]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs
  · rw [smul_monomial, smul_eq_mul, mul_one]
  · rw [smul_zero]
end Formalism.MainNotions.PlaneGram.TwistData
