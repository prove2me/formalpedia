-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.Gterm_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:57.608381+00:00
-- url     : https://prove2.me/submissions/c66f3367-4141-4ec3-bf6e-5f9d78db4701

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_inv_exists
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_inv_iso
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_inv_phase
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_card_isoZZ_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_isInt_orbZ_inv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) (w w' : Point K)
    (p p₁ : lowW K w.1 w.2 × upUniG K w.1.sum) (p' p₁' : lowW K w'.1 w'.2 × upUniG K w'.1.sum)
    (h : toCos R p = toCos R p₁) (h' : toCos R p' = toCos R p₁') :
    Gterm R ψ w w' p p' = Gterm R ψ w w' p₁ p₁' := by
  obtain ⟨a, ha, b, hb, rfl⟩ := inv_exists R p p₁ h
  obtain ⟨a', ha', b', hb', rfl⟩ := inv_exists R p' p₁' h'
  obtain ⟨x, y⟩ := p
  obtain ⟨x', y'⟩ := p'
  obtain ⟨φ, hφ⟩ := inv_iso R w a ha b hb x y
  obtain ⟨φ', hφ'⟩ := inv_iso R w' a' ha' b' hb' x' y'
  simp only [Gterm]
  rw [inv_phase R ψ hψ w a ha b hb x y, inv_phase R ψ hψ w' a' ha' b' hb' x' y',
    Formalism.FourierDecayAlt.P.A5x4.card_isoZZ_congr R hφ hφ']
  have e1 := Formalism.FourierDecayAlt.P.A5x4.isInt_orbZ_inv R w a ha b hb x y
  have e2 := Formalism.FourierDecayAlt.P.A5x4.isInt_orbZ_inv R w' a' ha' b' hb' x' y'
  by_cases hc : IsInt R (orbZ w (x, y)) ∧ IsInt R (orbZ w' (x', y'))
  · rw [if_pos hc, if_pos ⟨e1.2 hc.1, e2.2 hc.2⟩]
  · rw [if_neg hc, if_neg (fun h => hc ⟨e1.1 h.1, e2.1 h.2⟩)]
end Formalism.FourierDecayAlt.P.A5x8
