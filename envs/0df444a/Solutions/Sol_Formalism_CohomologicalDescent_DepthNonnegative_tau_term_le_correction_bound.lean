-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.tau_term_le_correction_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:32:32.977596+00:00
-- url     : https://prove2.me/submissions/8bf2fc96-1d12-4f8d-9098-ebb473312222

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_c_prime_le_weight_correction_holds
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_coefficientBoundTau_nonneg
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
theorem _root_.solution {ι : Type} [DecidableEq ι] (D : Data ι) (hP : D.Params) (l : ℕ) (hl : l.Prime) (τ : ι) :
    ((cTau D.T2 (fun τ => D.ex τ l) (fun τ =>
        ⌊cPrime l D.k (D.j τ) D.t (D.q τ) D.h (D.ecl τ l) (D.xlo τ) (D.xhi τ) (D.maxB τ)
          (D.depth τ l : ℝ)⌋₊) τ : ℕ) : ℝ) ≤
      (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (Cor.coefficientBoundTau D τ l) else (D.ex τ l : ℝ)) := by
  unfold cTau
  split_ifs with hτ
  · rw [Nat.cast_min]
    apply min_le_min le_rfl
    by_cases h0 : 0 ≤ cPrime l D.k (D.j τ) D.t (D.q τ) D.h (D.ecl τ l) (D.xlo τ) (D.xhi τ) (D.maxB τ)
        (D.depth τ l : ℝ)
    · exact (Nat.floor_le h0).trans (c_prime_le_weight_correction_holds ι D τ l hl hτ hP)
    · show ((⌊cPrime l D.k (D.j τ) D.t (D.q τ) D.h (D.ecl τ l) (D.xlo τ) (D.xhi τ) (D.maxB τ)
          (D.depth τ l : ℝ)⌋₊ : ℕ) : ℝ) ≤ _
      rw [Nat.floor_of_nonpos (not_le.1 h0).le]
      simpa using coefficientBoundTau_nonneg D τ l hl
  · exact le_rfl
end Formalism.CohomologicalDescent.DepthNonnegative
