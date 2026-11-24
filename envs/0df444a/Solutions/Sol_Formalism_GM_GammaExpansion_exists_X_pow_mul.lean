-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.exists_X_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:51.909309+00:00
-- url     : https://prove2.me/submissions/6dc71d1d-d189-464f-abc7-1dba4dd10aed

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open MvPolynomial Finset
variable {R σ : Type} [CommSemiring R]
namespace Formalism.GM.GammaExpansion
theorem _root_.solution (v : σ) (e : ℕ) (f : MvPolynomial σ R) (hf : ∀ m ∈ f.support, e ≤ m v) :
    ∃ h : MvPolynomial σ R, f = X v ^ e * h ∧ ∀ m ∈ h.support, Finsupp.single v e + m ∈ f.support := by
  classical
  refine ⟨f.divMonomial (Finsupp.single v e), ?_, fun m hm => ?_⟩
  · have hmod : f.modMonomial (Finsupp.single v e) = 0 := by
      ext m
      rw [coeff_zero]
      by_cases h : Finsupp.single v e ≤ m
      · exact coeff_modMonomial_of_le f h
      · rw [coeff_modMonomial_of_not_le f h]
        by_contra hc
        exact h (Finsupp.single_le_iff.2 (hf m (mem_support_iff.2 hc)))
    conv_lhs => rw [← divMonomial_add_modMonomial f (Finsupp.single v e), hmod, add_zero]
    rw [X_pow_eq_monomial]
  · rw [mem_support_iff, coeff_divMonomial] at hm
    exact mem_support_iff.2 hm
end Formalism.GM.GammaExpansion
