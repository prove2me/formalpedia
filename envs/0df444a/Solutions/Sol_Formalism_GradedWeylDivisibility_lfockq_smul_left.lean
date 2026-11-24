-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lfockq_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:54.827275+00:00
-- url     : https://prove2.me/submissions/31f5bcab-12ce-4f69-8a39-0adcf7f340f8

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_eq_sum

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
variable {σ : Type*}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (c : ℚ) (f g : MvPolynomial σ ℚ) :
    fockQ (c • f) g = c * fockQ f g := by
  rw [lfockq_eq_sum (c • f) g f.support MvPolynomial.support_smul,
    lfockq_eq_sum f g f.support subset_rfl, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun m _ => by rw [MvPolynomial.coeff_smul, smul_eq_mul]; ring)
end Formalism.GradedWeylDivisibility
