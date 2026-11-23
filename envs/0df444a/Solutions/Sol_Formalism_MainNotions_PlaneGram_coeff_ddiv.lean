-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.coeff_ddiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:14.743972+00:00
-- url     : https://prove2.me/submissions/c9db9008-5708-4945-a454-4b4e5c13cc36

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_ddiv_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_ddiv_add
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_add
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
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {σ : Type} (M β : σ →₀ ℕ) (F : MvPolynomial σ K) :
    (ddiv M F).coeff β = F.coeff (β + M) * (β + M).prod fun x k => (k.choose (M x) : K) := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial α c =>
    rw [ddiv_monomial, coeff_monomial]
    by_cases h : M ≤ α
    · rw [if_pos h, coeff_monomial]
      by_cases h2 : α - M = β
      · have : α = β + M := by rw [← h2, tsub_add_cancel_of_le h]
        rw [if_pos h2, if_pos this, this]
      · have : ¬ α = β + M := by
          intro h3; apply h2; rw [h3, add_tsub_cancel_right]
        rw [if_neg h2, if_neg this, zero_mul]
    · have : ¬ α = β + M := by
        intro h3; apply h; rw [h3]; exact le_add_self
      rw [if_neg h, if_neg this, coeff_zero, zero_mul]
  | add p q hp hq => rw [ddiv_add, coeff_add, coeff_add, hp, hq, add_mul]
end Formalism.MainNotions.PlaneGram
