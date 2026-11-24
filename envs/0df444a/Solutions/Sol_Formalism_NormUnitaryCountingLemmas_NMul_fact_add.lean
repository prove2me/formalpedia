-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.NMul.fact_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:11:20.046818+00:00
-- url     : https://prove2.me/submissions/d4823428-638a-47a2-89fd-384b3f1abb85

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NormMul

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
open Formalism Formalism.NormUnitaryCountingLemmas
open Formalism.NormUnitaryCountingLemmas.NMul
namespace Formalism.NormUnitaryCountingLemmas.NMul
theorem _root_.solution (x y : ℕ) :
    ((x + y).factorial : ℝ) = ((x + y).choose x : ℝ) * x.factorial * y.factorial := by
  rw [Nat.choose_symm_add]
  exact_mod_cast (Nat.add_choose_mul_factorial_mul_factorial x y).symm
end Formalism.NormUnitaryCountingLemmas.NMul
