-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.word_product_formula_general
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:05.294215+00:00
-- url     : https://prove2.me/submissions/980a2d21-b276-4c67-8ee3-c8cf6529cc22

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_prod_mul_list
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_bT_comm_vlet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_vlet_prod_mul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.Wd8
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
section Abstract
variable {R ι : Type} [Monoid R]
end Abstract
section Basic
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
end Basic
section Sites
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
end Sites
section Product
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
private theorem prod_one_lemma (L : List (Site A)) :
    (L.map fun σ => (bT σ ([] : List (Letter K S)) : SlopeTestRemainingChoices S A)).prod = 1 := by
  induction L with
  | nil => simp
  | cons σ L ih =>
    rw [List.map_cons, List.prod_cons, ih, mul_one] <;> simp only [bT]
end Product
end Formalism.FourierDecayAlt.P.Wd8
end

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd8
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd8
theorem _root_.solution (sites : List (Site A)) (w : List (Letter K S))
    (hs : sites.Pairwise SitesCommute) (hw : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) (z : Ix S) :
    uw sites w z =
      if ∀ c, c ∉ w.map Letter.intersection_update_fsHerm_neg_one → z c = 0 then
        (w.map fun l => (sites.map (lm l)).prod (z l.intersection_update_fsHerm_neg_one) 0).prod
      else 0 := by
  induction w generalizing z with
  | nil =>
    unfold uw
    rw [prod_one_lemma]
    by_cases hz : ∀ c, z c = 0
    · have hz' : z = e1 := funext hz
      subst hz'
      simp [e1]
    · have hz' : z ≠ e1 := fun h => hz fun c => by simp [h, e1]
      simp [Matrix.one_apply, hz', hz]
  | cons l w' ih =>
    have hnd : l.intersection_update_fsHerm_neg_one ∉ w'.map Letter.intersection_update_fsHerm_neg_one ∧ (w'.map Letter.intersection_update_fsHerm_neg_one).Nodup := by
      simpa using hw
    have ih' : ∀ z', uw sites w' z' = if ∀ c, c ∉ w'.map Letter.intersection_update_fsHerm_neg_one → z' c = 0 then
        (w'.map fun l => (sites.map (lm l)).prod (z' l.intersection_update_fsHerm_neg_one) 0).prod else 0 := fun z' => by
      first | exact ih hnd.2 z' | exact ih z' hnd.2
    have hne : ∀ l' ∈ w', l'.intersection_update_fsHerm_neg_one ≠ l.intersection_update_fsHerm_neg_one := fun l' hl' h =>
      hnd.1 (List.mem_map.mpr ⟨l', hl', h⟩)
    have hsplit : (sites.map fun σ => (bT σ (l :: w') : SlopeTestRemainingChoices S A)).prod =
        (sites.map fun σ => (vlet σ l : SlopeTestRemainingChoices S A)).prod * (sites.map fun σ => (bT σ w' : SlopeTestRemainingChoices S A)).prod :=
      prod_mul_list (fun σ => (vlet σ l : SlopeTestRemainingChoices S A)) (fun σ => bT σ w') sites
        (hs.imp fun {σ τ} hst => bT_comm_vlet hst w' l hnd.1)
    have hexp : uw sites (l :: w') z = ∑ j, (sites.map (lm l)).prod (z l.intersection_update_fsHerm_neg_one) j *
        uw sites w' (Function.update z l.intersection_update_fsHerm_neg_one j) := by
      unfold uw
      rw [hsplit, vlet_prod_mul_apply]
    have hval : ∀ j, (w'.map fun l' => (sites.map (lm l')).prod (Function.update z l.intersection_update_fsHerm_neg_one j l'.intersection_update_fsHerm_neg_one) 0).prod =
        (w'.map fun l' => (sites.map (lm l')).prod (z l'.intersection_update_fsHerm_neg_one) 0).prod := fun j => by
      congr 1
      refine List.map_congr_left fun l' hl' => ?_
      rw [Function.update_apply, if_neg (hne l' hl')]
    have hc1 : ¬ ∀ c, c ∉ w'.map Letter.intersection_update_fsHerm_neg_one → Function.update z l.intersection_update_fsHerm_neg_one 1 c = 0 := fun h => by
      have h1 := h l.intersection_update_fsHerm_neg_one hnd.1
      simp at h1
    have hc0 : (∀ c, c ∉ w'.map Letter.intersection_update_fsHerm_neg_one → Function.update z l.intersection_update_fsHerm_neg_one 0 c = 0) ↔
        ∀ c, c ∉ (l :: w').map Letter.intersection_update_fsHerm_neg_one → z c = 0 := by
      constructor
      · intro h c hc
        simp only [List.map_cons, List.mem_cons, not_or] at hc
        have h1 := h c hc.2
        rwa [Function.update_apply, if_neg hc.1] at h1
      · intro h c hc
        rw [Function.update_apply]
        by_cases hca : c = l.intersection_update_fsHerm_neg_one
        · rw [if_pos hca]
        · rw [if_neg hca]
          exact h c (by simp only [List.map_cons, List.mem_cons, not_or]; exact ⟨hca, hc⟩)
    rw [hexp, Fin.sum_univ_two, ih', ih', if_neg hc1, mul_zero, add_zero, hval]
    by_cases hP : ∀ c, c ∉ (l :: w').map Letter.intersection_update_fsHerm_neg_one → z c = 0
    · rw [if_pos (hc0.mpr hP), if_pos hP, List.map_cons, List.prod_cons]
    · rw [if_neg (fun h => hP (hc0.mp h)), if_neg hP, mul_zero]
end Formalism.FourierDecayAlt.P.Wd8
