-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.NU.pow_sum_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:34:14.266803+00:00
-- url     : https://prove2.me/submissions/f8792a1f-7974-4932-b0c9-313296aca650

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NormUnitary
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NU_prod_X_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.NU
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
namespace Formalism.NormUnitaryCountingLemmas.NU
theorem _root_.solution (d : ℕ) :
    (∑ i, (X i : MvPolynomial σ ℕ)) ^ d = ∑ t : Fin d → σ, monomial (cnt t) 1 := by
  have : (∑ i, (X i : MvPolynomial σ ℕ)) ^ d = ∏ _m : Fin d, ∑ i, (X i : MvPolynomial σ ℕ) := by
    simp [Finset.prod_const]
  rw [this, Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp_rw [prod_X_eq]
end Formalism.NormUnitaryCountingLemmas.NU
