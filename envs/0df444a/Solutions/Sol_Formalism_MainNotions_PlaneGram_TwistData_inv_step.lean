-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.inv_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:30:50.079221+00:00
-- url     : https://prove2.me/submissions/d6a5d6f5-8fdf-4ea9-a950-09bdefde882f

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsOfMemSupportLin
import Theorems.Thm_Formalism_MainNotions_PlaneGram_lin_eq_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_exists_of_mem_support_lin
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ph_lin_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_notSegL_mw
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_notSegL_of_mem_TLset
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_notSegL_of_mem_YPset
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_PreE_of_agree
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_PostE_of_agree
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_of_le


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
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable (D : TwistData K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} (hSeg : SegStep K v p) (hD : DVRHyp v p)
    (hr : 0 < D.r) (hJ : 0 < D.J) (θ : Fin D.J → Fin D.r → ℝ) (Gt : MvPolynomial (D.OL × Fin D.r) K)
    (s : Finset (Fin D.J)) (j : Fin D.J) (hj : j ∉ s) (Z : MvPolynomial (D.ML × Fin D.r) K)
    (hZ : D.Inv v p θ Gt s Z) : ∃ Z', D.Inv v p θ Gt (insert j s) Z' := by
  obtain ⟨hInt, hph, hsupp, hYP, hTL⟩ := hZ
  obtain ⟨Th, tI, tph, tsupp, tval, tS⟩ := hSeg hD D hr hJ j
  have hpre : ∀ ζ ∈ Z.support, D.PreE j ζ := fun ζ hζ => (hsupp ζ hζ).2.2 j hj
  have hne : ∀ j', j' ∈ s → j' ≠ j := fun j' hj' he => hj (he ▸ hj')
  refine ⟨Th Z, ?_, ?_, ?_, ?_, ?_⟩
  · intro α
    rw [lin_eq_sum Th Z, coeff_sum]
    apply AddValuation.map_le_sum
    intro ζ hζ
    rw [coeff_smul, smul_eq_mul, AddValuation.map_mul]
    exact add_nonneg (hInt ζ) (tI ζ (hpre ζ hζ) α)
  · rw [lin_eq_sum Th Z, map_sum, ← hph, D.ph_lin_sum p Z]
    refine Finset.sum_congr rfl fun ζ hζ => ?_
    rw [map_smul, tph ζ (hpre ζ hζ)]
  · intro ζ' hζ'
    obtain ⟨ζ, hζ, hζ'1⟩ := exists_of_mem_support_lin Th Z hζ'
    obtain ⟨hpost, hag⟩ := tsupp ζ (hpre ζ hζ) ζ' hζ'1
    obtain ⟨hw, hs, hns⟩ := hsupp ζ hζ
    refine ⟨fun t a => ?_, fun j' hj' => ?_, fun j' hj' => ?_⟩
    · rw [hag _ (D.notSegL_mw j t) a]
      exact hw t a
    · rcases Finset.mem_insert.mp hj' with h | hj's
      · rw [h]
        exact hpost
      · exact PostE.of_agree D (hne j' hj's) (hs j' hj's) hag
    · have hj's : j' ∉ s := fun h => hj' (Finset.mem_insert_of_mem h)
      have hne' : j' ≠ j := fun he => hj' (he ▸ Finset.mem_insert_self j s)
      exact PreE.of_agree D hne' (hns j' hj's) hag
  · intro j' hj' m hm
    rcases Finset.mem_insert.mp hj' with h | hj's
    · subst h
      exact tval Z hInt hpre m _ hm (hTL _ hj m hm)
    · exact vala_of_le (tS _ (fun i hi => D.notSegL_of_mem_YPset (hne j' hj's) m hi) Z) (hYP j' hj's m hm)
  · intro j' hj' m hm
    have hj's : j' ∉ s := fun h => hj' (Finset.mem_insert_of_mem h)
    have hne' : j' ≠ j := fun he => hj' (he ▸ Finset.mem_insert_self j s)
    exact vala_of_le (tS _ (fun i hi => D.notSegL_of_mem_TLset hne' m hi) Z) (hTL j' hj's m hm)
end Formalism.MainNotions.PlaneGram.TwistData
