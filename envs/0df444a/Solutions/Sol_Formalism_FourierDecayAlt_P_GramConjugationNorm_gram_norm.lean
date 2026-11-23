-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GramConjugationNorm.gram_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:32.680113+00:00
-- url     : https://prove2.me/submissions/00fd7f50-28e2-4b94-ad08-ecce3e00d4b3

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramConjugationNorm
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramConjugationNorm_gram_re_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramConjugationNorm_gram_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GramConjugationNorm
open Finset Filter Topology Formalism.FourierDecayAlt.TA
open scoped InnerProductSpace ComplexConjugate
variable {E : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace Formalism.FourierDecayAlt.P.GramConjugationNorm
theorem _root_.solution (k : Pt E → Pt E → ℂ) (V : Pt E → H) (P : Finset (Pt E))
    (hk : PSDOn P k) : ‖gram k V P‖ = (gram k V P).re := by
  have h1 : (gram k V P).im = 0 := Complex.conj_eq_iff_im.1 (gram_conj k V P hk)
  have h2 : gram k V P = (((gram k V P).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h1])
  rw [h2, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs,
    abs_of_nonneg (gram_re_nonneg k V P hk)]
end Formalism.FourierDecayAlt.P.GramConjugationNorm
