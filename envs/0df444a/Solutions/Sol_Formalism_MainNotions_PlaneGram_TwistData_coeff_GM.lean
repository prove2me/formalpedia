-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.coeff_GM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:33:22.685363+00:00
-- url     : https://prove2.me/submissions/d5465258-7845-48b7-b5c9-fa31a92226cf

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyLabel
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_prod_choose_add
import Theorems.Thm_Formalism_MainNotions_PlaneGram_coeff_ddiv
import Theorems.Thm_Formalism_MainNotions_PlaneGram_coeff_dg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) (ζ : D.EM) :
    (D.GM F (D.tpE ζ)).coeff (D.collapseExponent p ζ) =
      (D.ga (D.collapseExponent p ζ))⁻¹ * ((D.ga (D.phE p ζ) * F.coeff (D.phE p ζ)) *
        ((∏ x, (D.collapseExponent p ζ x + D.tpE ζ x).choose (D.tpE ζ x) : ℕ) : K)) := by
  have hga : ∀ β, (D.gaAct F).coeff β = D.ga β * F.coeff β := by
    intro β
    unfold gaAct
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [show F.coeff β = 0 by simpa using h, mul_zero]
  unfold GM
  rw [coeff_dg, coeff_ddiv, prod_choose_add, hga]
  rfl
end Formalism.MainNotions.PlaneGram.TwistData
