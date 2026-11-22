-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.LFockb_fockF_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:57:30.234987+00:00
-- url     : https://prove2.me/submissions/ca9a9984-2435-4d4c-8bda-8783252ee96c

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
open Formalism.REAL (fockF)
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {σ : Type*} (f : MvPolynomial σ ℂ) :
    fockF f f = ((∑ m ∈ f.support, Complex.normSq (f.coeff m) *
      ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
  unfold Formalism.REAL.fockF
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self, mul_comm (starRingEnd ℂ _)]
  push_cast
  rfl
end Formalism.GradedWeylDivisibility
