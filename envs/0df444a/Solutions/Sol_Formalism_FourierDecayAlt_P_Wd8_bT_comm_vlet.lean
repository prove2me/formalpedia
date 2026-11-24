-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.bT_comm_vlet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:16.978321+00:00
-- url     : https://prove2.me/submissions/d6ccc674-20e5-4aeb-9d8f-d05c0f763070

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_io_comm_eU
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_io_comm_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_comm_Ts
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_comm_Ts_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_eU_comm_of_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_eU_comm_of_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_eU_comm_of_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_io_comm_eU
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_io_comm_io

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
private theorem ent_comm_lemma (σ : Site A) (l : Letter K S) (x : A)
    (h : ∀ y ∈ ops σ, Commute y x) (i j : Fin 2) :
    Commute ((if l.plus then Ts σ l.pt else (Ts σ l.pt).map star) i j) x := by
  have hφ : ∀ (k : K) (r : A), Commute ((RingHom.id A) (algebraMap K A k)) r :=
    fun k r => Algebra.commutes k r
  by_cases hl : l.plus = true
  · rw [if_pos hl]
    exact comm_Ts (RingHom.id A) hφ σ x h l.pt i j
  · rw [if_neg hl]
    exact comm_Ts_star (RingHom.id A) hφ σ x h l.pt i j
private theorem vlet_comm_lemma {σ τ : Site A} (h : SitesCommute σ τ) (l' l : Letter K S)
    (hne : l'.intersection_update_fsHerm_neg_one ≠ l.intersection_update_fsHerm_neg_one) : Commute (vlet σ l' : SlopeTestRemainingChoices S A) (vlet τ l) := by
  unfold vlet ins
  refine Commute.sum_left _ _ _ fun i _ => Commute.sum_left _ _ _ fun j _ =>
    Commute.sum_right _ _ _ fun p _ => Commute.sum_right _ _ _ fun q _ => ?_
  have hN : ∀ x ∈ ops σ, Commute x ((if l.plus then Ts τ l.pt else (Ts τ l.pt).map star) p q) :=
    fun x hx => (ent_comm_lemma τ l x (fun y hy => (h x hx y hy).symm) p q).symm
  have hMN := ent_comm_lemma σ l' _ hN i j
  exact ((eU_comm_of_ne hne i j p q).mul_right
      (io_comm_eU ((if l.plus then Ts τ l.pt else (Ts τ l.pt).map star) p q) l'.intersection_update_fsHerm_neg_one i j).symm).mul_left
    ((io_comm_eU ((if l'.plus then Ts σ l'.pt else (Ts σ l'.pt).map star) i j) l.intersection_update_fsHerm_neg_one p q).mul_right
      (io_comm_io hMN))
end Product
end Formalism.FourierDecayAlt.P.Wd8
end

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd8
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd8
theorem _root_.solution {σ τ : Site A} (h : SitesCommute σ τ) (w : List (Letter K S)) (l : Letter K S)
    (ha : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one) : Commute (bT σ w : SlopeTestRemainingChoices S A) (vlet τ l) := by
  induction w with
  | nil =>
    simp only [bT]
    exact Commute.one_left _
  | cons l' w ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at ha
    simp only [bT]
    exact (vlet_comm_lemma h l' l (Ne.symm ha.1)).mul_left (ih ha.2)
end Formalism.FourierDecayAlt.P.Wd8
