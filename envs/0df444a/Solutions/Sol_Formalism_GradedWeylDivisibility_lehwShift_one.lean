-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lehwShift_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:21.92655+00:00
-- url     : https://prove2.me/submissions/8bffe194-31be-409c-98cb-889c5dd8d166

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
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
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} (w : Fin r × Fin n → ℤ) (δ : ℤ) :
    LehwShift w (1 : Polynomial (MvPolynomial (Fin r × Fin n) R)) 0 δ := by
  intro k
  by_cases hk : k = 0
  · subst hk
    rw [Polynomial.coeff_one_zero]
    intro d hd
    rw [MvPolynomial.coeff_one] at hd
    split_ifs at hd with h
    · subst h
      simp
    · exact (hd rfl).elim
  · rw [Polynomial.coeff_one, if_neg (by omega)]
    intro d hd
    exact (hd (MvPolynomial.coeff_zero d)).elim
end Formalism.GradedWeylDivisibility
