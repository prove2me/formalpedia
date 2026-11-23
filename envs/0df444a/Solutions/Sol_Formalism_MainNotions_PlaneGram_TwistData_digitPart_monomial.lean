-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.digitPart_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:12.464795+00:00
-- url     : https://prove2.me/submissions/79aa9855-8d16-4930-ab04-6a9317ddc436

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_lsup_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_digitPart_eq
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial


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
theorem _root_.solution (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) (α : D.EA) (c : K) :
    D.digitPart p ρ (monomial α c) = if D.InClass p ρ α then monomial (D.liftE p α) c else 0 := by
  rw [digitPart_eq, digitPartL, lsup_monomial]
  split_ifs
  · rw [smul_monomial, smul_eq_mul, mul_one]
  · rw [smul_zero]
end Formalism.MainNotions.PlaneGram.TwistData
