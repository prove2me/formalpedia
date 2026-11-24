-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.NU.coeff_P
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:11:24.564793+00:00
-- url     : https://prove2.me/submissions/621b0cdf-c4dc-44f1-98da-05ad3e915739

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NormUnitary

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
theorem _root_.solution {d : ℕ} (S : (Fin d → σ) → ℂ) (e : σ →₀ ℕ) :
    coeff e (P S) = ∑ t, if cnt t = e then S t else 0 := by
  simp only [P, coeff_sum, coeff_monomial]
end Formalism.NormUnitaryCountingLemmas.NU
