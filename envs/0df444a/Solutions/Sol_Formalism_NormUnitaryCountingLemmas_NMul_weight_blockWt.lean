-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.NMul.weight_blockWt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:11:22.686796+00:00
-- url     : https://prove2.me/submissions/29f017e5-5fbf-45a8-b1b7-00a6d5352f2b

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
theorem _root_.solution {N n : ℕ} (a : Fin N × Fin n →₀ ℕ) (j : Fin N) :
    Finsupp.weight (blockWt N n) a j = blockDeg a j := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [blockWt, blockDeg, Finset.sum_apply, Fintype.sum_prod_type, Pi.smul_apply,
    Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp
end Formalism.NormUnitaryCountingLemmas.NMul
