-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.sizeData_joint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:19:39.237785+00:00
-- url     : https://prove2.me/submissions/eae4aa98-ebf0-45f1-bee8-3419db65bce7

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_tau_term_le_correction_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
open Formalism.RankGapBounds.ChebyshevFactorialBounds
namespace Formalism.CohomologicalDescent.DepthNonnegative
theorem _root_.solution : JointEstimate := by
  intro ι _ _ D hP h l hl hE hlJ h2 h3 h4
  have h5 := h l hl hE hlJ h2 h3 h4
  have h6 : (D.J l : ℝ) ≤ ((∑ τ, cTau D.T2 (fun τ => D.ex τ l) (fun τ =>
        ⌊cPrime l D.k (D.j τ) D.t (D.q τ) D.h (D.ecl τ l) (D.xlo τ) (D.xhi τ) (D.maxB τ)
          (D.depth τ l : ℝ)⌋₊) τ : ℕ) : ℝ) := by exact_mod_cast h5
  refine h6.trans ?_
  rw [Nat.cast_sum]
  exact Finset.sum_le_sum fun τ _ => tau_term_le_correction_bound D hP l hl τ
end Formalism.CohomologicalDescent.DepthNonnegative
