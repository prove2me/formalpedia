-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.coeff_digitPart_eIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:30:38.686424+00:00
-- url     : https://prove2.me/submissions/6b680d82-843e-4fe1-99b0-8ea40d89a165

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyLabel
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_class_iff
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial


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
theorem _root_.solution (p : ℕ) {ζ : D.EM} (hζ : D.LabLowE p ζ) (G : MvPolynomial (D.OL × Fin D.r) K) :
    (D.digitPart p (D.labF ζ) G).coeff (eIn D.outP ζ) = G.coeff (D.collapseExponent p ζ) := by
  classical
  unfold digitPart
  rw [MvPolynomial.coeff_sum]
  have h : ∀ α ∈ G.support, (if D.InClass p (D.labF ζ) α then monomial (D.liftE p α) (G.coeff α) else 0 :
      MvPolynomial (D.ML × Fin D.r) K).coeff (eIn D.outP ζ) = if α = D.collapseExponent p ζ then G.coeff α else 0 := by
    intro α _
    split_ifs with h1 h2 h2
    · rw [MvPolynomial.coeff_monomial, if_pos ((D.class_iff p hζ α).2 h2).2]
    · rw [MvPolynomial.coeff_monomial, if_neg]
      intro h3
      exact h2 ((D.class_iff p hζ α).1 ⟨h1, h3⟩)
    · exact absurd ((D.class_iff p hζ α).2 h2).1 h1
    · simp
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq']
  split_ifs with h0
  · rfl
  · exact (by simpa using h0 : G.coeff (D.collapseExponent p ζ) = 0).symm
end Formalism.MainNotions.PlaneGram.TwistData
