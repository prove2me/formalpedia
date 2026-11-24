-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.Th_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:26:29.643484+00:00
-- url     : https://prove2.me/submissions/b44e42ad-7b9d-403f-babb-b6cbe5436cb9

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutionXFirstEmbedding
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MonomialMemPolKSg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_pullE_eIn
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Th_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_outSeg_of_not_segL
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_eIn
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_C_mul_le
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_nonneg_of_vecS
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_outside_linear
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_sum_le


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
variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)
variable {ι : Type} [Fintype ι]
variable (cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K) (PP : ι → MvPolynomial (D.ML × Fin D.r) K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (hPP : ∀ b, ∀ ξ ∈ (PP b).support, ∀ i, ¬ D.SegL j i → ∀ a, ξ (i, a) = 0)
    (S : Finset D.ML) (hS : ∀ i ∈ S, ¬ D.SegL j i) (Z : MvPolynomial (D.ML × Fin D.r) K) :
    valS D.msg S Z ≤ valS D.msg S (D.Th j cc PP Z) := by
  have hIn : ∀ α : D.EM, eIn (fun i => ¬ D.outSeg j i) α = eOut (D.outSeg j) α := by
    intro α
    ext x
    simp [eIn, eOut, Finsupp.filter_apply]
  have hOut : ∀ α : D.EM, eOut (fun i => ¬ D.outSeg j i) α = eIn (D.outSeg j) α := by
    intro α
    ext x
    simp [eIn, eOut, Finsupp.filter_apply]
  have hIn1 : ∀ α : D.EM,
      D.Th j cc PP (monomial (eIn (D.outSeg j) α) 1) = ∑ b, cc (D.pullE j α) b • PP b := by
    intro α
    rw [Th_monomial, eOut_eIn, pullE_eIn, ← C_apply, map_one, one_mul]
  refine valS_outside_linear (fun i => ¬ D.outSeg j i) D.msg S (D.Th j cc PP) ?_ ?_ ?_ Z
  · intro i hi h
    exact h (D.outSeg_of_not_segL j i (hS i hi))
  · intro α
    rw [hIn, hOut, hIn1, Th_monomial]
  · intro α
    rw [hOut, hIn1]
    apply valS_sum_le
    intro b _
    rw [smul_eq_C_mul]
    refine le_trans ?_ (valS_C_mul_le _ _ _ _)
    apply valS_nonneg_of_vecS
    intro ξ hξ i a hne hiS
    exact absurd (hPP b ξ hξ i (hS i hiS) a) hne
end Formalism.MainNotions.PlaneGram.TwistData
