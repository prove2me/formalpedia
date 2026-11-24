-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.exists_div
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:19.255957+00:00
-- url     : https://prove2.me/submissions/8f4221b7-6b9b-444a-89bd-0c4e8bdd919c

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_ShiftLastLetterThresholds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_intPol_iff_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (v : σ) (h : MvPolynomial σ ℚ_[p]) :
    ∃ a, h = initPart v 0 h + X v * a ∧ (h ∈ IntPol p σ → a ∈ IntPol p σ) := by
  classical
  refine ⟨MvPolynomial.divMonomial h (Finsupp.single v 1), ?_, ?_⟩
  · have hmod : MvPolynomial.modMonomial h (Finsupp.single v 1) = initPart v 0 h := by
      ext m
      rw [coeff_initPart]
      by_cases hm : m v = 0
      · rw [if_pos hm, MvPolynomial.coeff_modMonomial_of_not_le]
        rw [Finsupp.single_le_iff]
        omega
      · rw [if_neg hm, MvPolynomial.coeff_modMonomial_of_le]
        rw [Finsupp.single_le_iff]
        omega
    have hdm := MvPolynomial.divMonomial_add_modMonomial h (Finsupp.single v 1)
    rw [← hmod]
    calc h = monomial (Finsupp.single v 1) 1 * (MvPolynomial.divMonomial h (Finsupp.single v 1)) +
          MvPolynomial.modMonomial h (Finsupp.single v 1) := hdm.symm
      _ = MvPolynomial.modMonomial h (Finsupp.single v 1) + X v * (MvPolynomial.divMonomial h (Finsupp.single v 1)) := by
        rw [add_comm]
        rfl
  · intro hh
    rw [intPol_iff_norm] at hh ⊢
    intro m
    rw [MvPolynomial.coeff_divMonomial]
    exact hh _
end Formalism.InvariantFactorPaths.L4
