-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.MXY_cases
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:56.146044+00:00
-- url     : https://prove2.me/submissions/e480b1d1-22be-41c1-95e3-9f9eddde1bc1

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EtaleIntegralityFacts
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_tri_cases
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_MXY_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_H_zero_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_rhs_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_rhs_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_tri_gt
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_tri_lt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
open Formalism.FourierDecayAlt.G Matrix
noncomputable section
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
theorem _root_.solution (m : ℕ) (i j : Fin (m + 2)) :
    (∀ (D t : ℂ) (p : XY m), MXY m D t p i j = 0) ∨ (∀ (D t : ℂ) (p : XY m), MXY m D t p i j = t) ∨
    (∀ (D t : ℂ) (p : XY m), MXY m D t p i j = rhoXY m D t p) ∨
    (∃ k, ∀ (D t : ℂ) (p : XY m), MXY m D t p i j = p.1 k) ∨
    (∃ e, ∀ (D t : ℂ) (p : XY m), MXY m D t p i j = p.2 e) := by
  simp only [MXY_apply]
  generalize i.rev = a
  induction a using Fin.cases with
  | zero =>
    by_cases hj : j = 0
    · subst hj
      exact Or.inr (Or.inr (Or.inl fun D t p => H_zero_zero m t _ p.1 p.2))
    · have hj' : 0 < j := Fin.pos_of_ne_zero hj
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨(0, j), hj'⟩, fun D t p => ?_⟩)))
      rw [WeakApproximationGL.rhs_zero t _ p.1 p.2 hj', WeakApproximationGL.tri_lt p.1 p.2 hj']
  | succ a =>
    simp only [WeakApproximationGL.rhs_succ]
    by_cases hj : (j : ℕ) = a
    · refine Or.inr (Or.inl fun D t p => ?_)
      have h : j < a.succ := by rw [Fin.lt_def, Fin.val_succ]; omega
      rw [if_pos hj, WeakApproximationGL.tri_gt p.1 p.2 h, add_zero]
    · simp only [if_neg hj, zero_add]
      rcases tri_cases m a.succ j with h | ⟨k, h⟩ | ⟨e, h⟩
      · exact Or.inl fun D t p => h p.1 p.2
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, fun D t p => h p.1 p.2⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e, fun D t p => h p.1 p.2⟩)))
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
