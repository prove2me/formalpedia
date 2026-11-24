-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.NMul.bweight_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:34:12.548796+00:00
-- url     : https://prove2.me/submissions/e465c4fd-1050-4963-9b1e-fd38e3878848

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NormMul
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NMul_blockDeg_add
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NMul_fact_add

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
theorem _root_.solution {N n : ℕ} (a b : Fin N × Fin n →₀ ℕ) :
    bweight (a + b) * ∏ j, ((blockDeg (a + b) j).choose (blockDeg a j) : ℝ) =
      bweight a * bweight b * ∏ j, ∏ k, (((a + b) (j, k)).choose (a (j, k)) : ℝ) := by
  unfold bweight
  rw [← prod_mul_distrib, ← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  rw [blockDeg_add]
  simp only [Finsupp.coe_add, Pi.add_apply]
  push_cast
  rw [fact_add (blockDeg a j) (blockDeg b j),
    prod_congr rfl (fun k _ => fact_add (a (j, k)) (b (j, k))), prod_mul_distrib,
    prod_mul_distrib]
  have h1 : (0 : ℝ) < ((blockDeg a j + blockDeg b j).choose (blockDeg a j) : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_right _ _)
  have h2 : (0 : ℝ) < (blockDeg a j).factorial := by positivity
  have h3 : (0 : ℝ) < (blockDeg b j).factorial := by positivity
  field_simp
end Formalism.NormUnitaryCountingLemmas.NMul
