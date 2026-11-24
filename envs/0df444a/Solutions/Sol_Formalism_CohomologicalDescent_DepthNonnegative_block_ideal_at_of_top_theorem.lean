-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.block_ideal_at_of_top_theorem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:40:36.730628+00:00
-- url     : https://prove2.me/submissions/ca6daf56-88e4-4217-8abf-aee57cce1874

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
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
open Formalism.RankGapBounds.ChebyshevFactorialBounds
namespace Formalism.CohomologicalDescent.DepthNonnegative
theorem _root_.solution (hTop : TheoremWTop) : BlockIdealAt := by
  intro hD ι _ _ D l O _ _ _ A _ _ G _ Γ K jK lam _ _ T _ _ _ _ S ϖ n₀ e Λ L _ _ _ _ _ hwt hP hT hmaxB hJ
  have hl : l.Prime := hT.1
  have h1 := (hTop hD O A G Γ K jK ι l D.Nr D.k D.t D.h lam D.T2 D.j D.q D.xlo D.xhi
    (fun τ => D.ecl τ l) (fun τ => D.ex τ l) (fun τ => D.depth τ l) T S ϖ n₀ e Λ L hwt hT).2
  have h2 : (D.J l : ℝ) ≤ ((∑ τ, cTau D.T2 (fun τ => D.ex τ l)
      (cFloor l D.Nr D.k D.t D.h lam D.j D.q D.xlo D.xhi (fun τ => D.ecl τ l)
        (fun τ => D.depth τ l)) τ : ℕ) : ℝ) := by
    exact_mod_cast hJ.trans h1
  refine h2.trans ?_
  rw [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro τ _
  refine le_trans (le_of_eq ?_) (tau_term_le_correction_bound D hP l hl τ)
  congr 1
  unfold cTau
  by_cases hτ : τ ∈ D.T2
  · rw [if_pos hτ, if_pos hτ]
    unfold cFloor
    simp only [hmaxB τ hτ]
  · rw [if_neg hτ, if_neg hτ]
end Formalism.CohomologicalDescent.DepthNonnegative
