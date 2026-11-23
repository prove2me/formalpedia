-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xnN_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:29.865958+00:00
-- url     : https://prove2.me/submissions/110849a5-14f2-4a1b-b524-cde33b1bd349

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
variable {r n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {σ : Type*} (f : MvPolynomial σ ℂ) : 0 ≤ xnN f := by
  have key : ∀ (c : ℂ) (N : ℕ), 0 ≤ (c * star c * (N : ℂ)).re := by
    intro c N
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    first
    | (simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
        Complex.natCast_re, Complex.natCast_im, Complex.mul_im]
       nlinarith [sq_nonneg c.re, sq_nonneg c.im])
    | (rw [Complex.star_def, Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
        Complex.ofReal_re]
       exact mul_nonneg (Complex.normSq_nonneg _) hN)
  unfold xnN fockF
  rw [Complex.re_sum]
  exact Finset.sum_nonneg fun m _ => key _ _
end Formalism.BranchingDeterminantCap
