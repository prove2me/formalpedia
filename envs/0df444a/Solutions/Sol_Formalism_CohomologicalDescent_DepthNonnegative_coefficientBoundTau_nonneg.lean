-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.coefficientBoundTau_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:14:42.505425+00:00
-- url     : https://prove2.me/submissions/5bd8d833-d597-4777-8eb2-2e6e71858cbf

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Theorems.Thm_Formalism_CohomologicalDescent_jw_Icl_nonneg
import Theorems.Thm_Formalism_CohomologicalDescent_jw_gate_nonneg


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
theorem _root_.solution {ι : Type} (D : Data ι) (τ : ι) (l : ℕ) (hl : l.Prime) : 0 ≤ Cor.coefficientBoundTau D τ l := by
  have hl0R : (0 : ℝ) < l := by exact_mod_cast hl.pos
  have hl1R : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
    linarith
  have h1 : (0 : ℝ) ≤ ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * (((D.h : ℝ) + (D.Nr : ℝ)) / ((l : ℝ) - 1) + 6) := by
    have : (0 : ℝ) ≤ ((D.h : ℝ) + (D.Nr : ℝ)) / ((l : ℝ) - 1) := div_nonneg (by positivity) hl1R.le
    positivity
  have h2 : (0 : ℝ) ≤ (D.ecl τ l : ℝ) := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ (D.k : ℝ) * ((D.S : ℝ) / (l : ℝ) + D.Icl τ l) :=
    mul_nonneg (Nat.cast_nonneg _) (add_nonneg (div_nonneg (Nat.cast_nonneg _) hl0R.le) (jw_Icl_nonneg D τ l))
  have h4 := jw_gate_nonneg D τ l
  have h5 : (0 : ℝ) ≤ ((D.depth τ l : ℝ) / (l : ℝ)) * max 0 (1 + Real.log ((D.h : ℝ) / (l : ℝ))) :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg _) hl0R.le) (le_max_left _ _)
  unfold Cor.coefficientBoundTau
  linarith
end Formalism.CohomologicalDescent.DepthNonnegative
