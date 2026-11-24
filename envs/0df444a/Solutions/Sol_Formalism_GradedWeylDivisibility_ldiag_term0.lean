-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldiag_term0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:07.230496+00:00
-- url     : https://prove2.me/submissions/9eb7126d-179a-4073-8bca-0f5562f6262f

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DomPow
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockDiagBound

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
open Formalism Formalism.GradedWeylDivisibility
open Formalism.REAL (fockF)
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (z : ℂ) (N : ℕ) :
    z * star z * (N : ℂ) = ((Complex.normSq z * N : ℝ) : ℂ) := by
  have hs : ∀ x : ℂ, star x = (starRingEnd ℂ) x := fun _ => rfl
  apply Complex.ext
  all_goals
    simp only [hs, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.natCast_re, Complex.natCast_im, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply]
    ring
end Formalism.GradedWeylDivisibility
