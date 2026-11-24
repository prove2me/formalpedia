-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_twistX_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:33:27.474978+00:00
-- url     : https://prove2.me/submissions/10bafc2d-35ad-443b-966d-72ba70079db8

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TMemLaurentFiltration
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_AlmostEverywhereSpherical
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_twistMat_mem
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_cost_single
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_C_mem
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_lift_mem


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
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
open Formalism.MainNotions.G
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
theorem _root_.solution {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    {e : ℤ} {bm : Bool} (h : flt_compat e bm) (v : ι × Fin n) :
    twistSub LL S j (X v : MvPolynomial (ι × Fin n) R) ∈
      (laurentCoeffFiltration R n (ι × Fin n) e).F ((-flt_cost LL S bm) (Finsupp.single v 1)) := by
  classical
  have hX : ∀ w : ι × Fin n,
      (X w : MvPolynomial (ι × Fin n) (GLLaurent R n)) ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F 0 := by
    intro w
    rw [laurentCoeffFiltration, flt_lift_mem]
    intro m
    rw [AddMonoidHom.zero_apply, sub_zero, MvPolynomial.coeff_X]
    split_ifs
    · exact (flt_L (GLCoord R n) e).one_mem
    · exact zero_mem _
  have hterm : ∀ (a : GLLaurent R n) (w : ι × Fin n) (t : ℤ), a ∈ (flt_L (GLCoord R n) e).F t →
      MvPolynomial.C a * X w ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F t := by
    intro a w t ha
    have hm := (laurentCoeffFiltration R n (ι × Fin n) e).mul_mem (flt_C_mem ha) (hX w)
    rwa [add_zero] at hm
  unfold twistSub
  rw [MvPolynomial.eval₂Hom_X', AddMonoidHom.neg_apply, flt_cost_single]
  by_cases hS : v.1 ∈ S
  · rw [if_pos hS]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases hb : LL.vec v.1 <;> simp only [hS, true_and] <;>
      norm_num <;>
      exact sum_mem fun b _ => hterm _ _ _ (flt_twistMat_mem R n j _ _ _ (by norm_num) (by norm_num) _ _)
  · rw [if_neg hS, if_neg (fun h' => hS h'.1), neg_zero]
    exact hX v
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
