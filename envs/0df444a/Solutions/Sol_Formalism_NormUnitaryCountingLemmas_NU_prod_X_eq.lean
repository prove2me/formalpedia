-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.NU.prod_X_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:11:07.607981+00:00
-- url     : https://prove2.me/submissions/481d1c92-4173-4f77-9fa8-f7528dd1eec6

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
theorem _root_.solution {R : Type*} [CommSemiring R] {d : ℕ} (t : Fin d → σ) :
    (∏ m, (X (t m) : MvPolynomial σ R)) = monomial (cnt t) 1 := by
  rw [cnt, monomial_sum_one]; rfl
end Formalism.NormUnitaryCountingLemmas.NU
