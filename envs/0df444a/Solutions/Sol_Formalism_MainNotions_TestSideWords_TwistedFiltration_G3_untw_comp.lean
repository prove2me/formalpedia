-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G3.untw_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:34:08.296135+00:00
-- url     : https://prove2.me/submissions/5f04f9e9-891f-4dd9-8f77-fe97ae539513

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TwistSubXMemSupported
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_untw_C
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_untw_X
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_twistMat_mul
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G2_twistSub_X_out


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
theorem _root_.solution (w : Set ι) (hw : ∀ l ∈ w, LL.vec l = true) (hd : Disjoint S w) (j : Fin n) :
    (untw (R := R) (n := n) w j).comp (twistSub LL (S ∪ w) j) = twistSub LL S j := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, twistSub, eval₂Hom_C]
    exact untw_C w j _
  · intro v
    rw [RingHom.comp_apply]
    by_cases hS : v.1 ∈ S
    · have hnw : v.1 ∉ w := Set.disjoint_left.1 hd hS
      unfold twistSub
      rw [eval₂Hom_X', eval₂Hom_X', if_pos (Set.mem_union_left w hS), if_pos hS]
      split_ifs
      · rw [map_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [map_mul, untw_C, untw_X, if_neg hnw]
      · rw [map_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [map_mul, untw_C, untw_X, if_neg hnw]
    · by_cases hW : v.1 ∈ w
      · rw [Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.twistSub_X_out LL S j v hS]
        unfold twistSub
        rw [eval₂Hom_X', if_pos (Set.mem_union_right S hW), if_pos (hw _ hW)]
        rw [map_sum]
        simp_rw [map_mul, untw_C, untw_X, if_pos hW, Finset.mul_sum, ← mul_assoc, ← C_mul]
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_mul, ← map_sum]
        have hm : ∀ b' : Fin n, ∑ b : Fin n, twistMat R n j 1 b v.2 * twistMat R n j (-1) b' b =
            (1 : Matrix (Fin n) (Fin n) (GLLaurent R n)) b' v.2 := by
          intro b'
          have h1 := Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_twistMat_mul R n j (-1)
          rw [neg_neg] at h1
          rw [← h1, Matrix.mul_apply]
          exact Finset.sum_congr rfl fun b _ => mul_comm _ _
        simp_rw [hm, Matrix.one_apply]
        simp
      · rw [Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.twistSub_X_out LL S j v hS,
          Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.twistSub_X_out LL (S ∪ w) j v (by simp [hS, hW]), untw_X, if_neg hW]
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
