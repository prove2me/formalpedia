-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G3.valS_wCoeff_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:59:34.082801+00:00
-- url     : https://prove2.me/submissions/cde6806a-b8fc-48da-b102-a6a3558980bf

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TwistSubXMemSupported
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_wCoeff_mem
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_twistSub_wCoeff
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_trivFil_F
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_wDegHom_eq
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_wDegHom_single
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_untw_C
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_untw_X
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_untw_comp
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_C_mem
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_hom_mem
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_le_valS
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_monomial_mem
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_twistMat_mem


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
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
variable {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
open Classical
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
theorem _root_.solution (w : Set ι) (hw : ∀ l ∈ w, LL.vec l = true) (hd : Disjoint S w) (F : MvPolynomial (ι × Fin n) R)
    (dw : ℕ) (hdeg : ∀ μ ∈ F.support, wDeg w μ ≤ dw) (th : ℤ) (hF : (th : WithTop ℤ) ≤ valS LL (S ∪ w) F)
    (M : ι × Fin n →₀ ℕ) : ((th - dw : ℤ) : WithTop ℤ) ≤ valS LL S (wCoeff w M F) := by
  open Formalism.MainNotions.TestSideWords.TwistedFiltration.G1 in
  have htriv0 : ∀ (B : Type _) [CommRing B] (b : B), b ∈ (trivFil B).F 0 := by
    intro B _ b; simp [trivFil]

  have hB : twistSub LL (S ∪ w) (lastIdx n) F ∈
      (flt_lift (trivFil (GLLaurent R n)) (-wDegHom w)).F (-(dw : ℤ)) := by
    refine flt_hom_mem (trivFil R) _ _ (-wDegHom w) ?_ ?_ ?_
    · intro t b hb
      rw [twistSub, eval₂Hom_C]
      apply flt_C_mem
      by_cases ht : t ≤ 0
      · simp [trivFil, ht]
      · have hb' : b ∈ (⊥ : AddSubgroup R) := by simpa [trivFil, ht] using hb
        rw [AddSubgroup.mem_bot] at hb'
        rw [hb', map_zero]
        exact AddSubgroup.zero_mem _
    · intro v
      have e1 : ∀ b : Fin n, (-wDegHom w) (Finsupp.single (v.1, b) 1) = (-wDegHom w) (Finsupp.single v 1) := by
        intro b; simp [wDegHom_single]
      unfold twistSub
      rw [eval₂Hom_X']
      split_ifs
      · refine AddSubgroup.sum_mem _ fun b _ => ?_
        rw [C_mul_X_eq_monomial]
        apply flt_monomial_mem
        rw [e1 b, sub_self]
        exact htriv0 _ _
      · refine AddSubgroup.sum_mem _ fun b _ => ?_
        rw [C_mul_X_eq_monomial]
        apply flt_monomial_mem
        rw [e1 b, sub_self]
        exact htriv0 _ _
      · apply flt_monomial_mem
        rw [sub_self]
        exact htriv0 _ _
    · intro m
      by_cases hm : m ∈ F.support
      · have h1 := hdeg m hm
        have : -(dw : ℤ) - (-wDegHom w) m ≤ 0 := by
          rw [AddMonoidHom.neg_apply, wDegHom_eq]; omega
        rw [trivFil_F, if_pos this]
        exact AddSubgroup.mem_top _
      · rw [MvPolynomial.notMem_support_iff.1 hm]
        exact AddSubgroup.zero_mem _

  have hC : twistSub LL (S ∪ w) (lastIdx n) F ∈
      (flt_lift (flt_L (GLCoord R n) 1) (-wDegHom w)).F (th - dw) := by
    intro m
    have h1 := ((flt_le_valS LL (S ∪ w) F th).1 hF) m
    have h2 := hB m
    by_cases hm : (wDeg w m : ℤ) ≤ dw
    · refine (flt_L (GLCoord R n) 1).anti ?_ h1
      rw [AddMonoidHom.neg_apply, wDegHom_eq]
      simp only [AddMonoidHom.zero_apply]
      omega
    · have : ¬ (-(dw : ℤ) - (-wDegHom w) m ≤ 0) := by
        rw [AddMonoidHom.neg_apply, wDegHom_eq]; omega
      have h3 : coeff m (twistSub LL (S ∪ w) (lastIdx n) F) ∈ (⊥ : AddSubgroup (GLLaurent R n)) := by
        rw [trivFil_F, if_neg this] at h2
        exact h2
      rw [AddSubgroup.mem_bot] at h3
      rw [h3]
      exact AddSubgroup.zero_mem _

  have hD : untw w (lastIdx n) (twistSub LL (S ∪ w) (lastIdx n) F) ∈
      (laurentCoeffFiltration R n (ι × Fin n) 1).F (th - dw) := by
    refine flt_hom_mem (flt_L (GLCoord R n) 1) (laurentCoeffFiltration R n (ι × Fin n) 1) (untw w (lastIdx n)) (-wDegHom w) ?_ ?_ hC
    · intro t b hb
      rw [untw_C]
      exact flt_C_mem hb
    · intro v
      rw [untw_X]
      split_ifs with hv
      · refine AddSubgroup.sum_mem _ fun b _ => ?_
        rw [C_mul_X_eq_monomial]
        apply flt_monomial_mem
        rw [AddMonoidHom.neg_apply, wDegHom_single, if_pos hv]
        simp only [AddMonoidHom.zero_apply, sub_zero]
        exact flt_twistMat_mem R n (lastIdx n) (-1) 1 (-1) (by norm_num) (by norm_num) b v.2
      · apply flt_monomial_mem
        rw [AddMonoidHom.neg_apply, wDegHom_single, if_neg hv]
        simpa using (flt_L (GLCoord R n) 1).one_mem
  rw [← RingHom.comp_apply, untw_comp LL S w hw hd] at hD
  rw [flt_le_valS, twistSub_wCoeff LL S w hd]
  exact wCoeff_mem w M hD
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
