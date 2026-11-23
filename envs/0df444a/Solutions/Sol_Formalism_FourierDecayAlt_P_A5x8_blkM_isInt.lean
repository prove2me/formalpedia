-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.blkM_isInt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:06.794348+00:00
-- url     : https://prove2.me/submissions/89183258-9b43-4a34-9373-d92140a943d0

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
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
variable {K : Type} [CommRing K] {m N : ℕ}
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (R : Subring K) (hN : N = m + 1) (A : Matrix (Fin m) (Fin m) K)
    (b a : Fin m → K) (d : K) : IsInt R (blkM hN A b a d) ↔
      IsInt R A ∧ (∀ i, b i ∈ R) ∧ (∀ j, a j ∈ R) ∧ d ∈ R := by
  constructor
  · intro h
    refine ⟨fun i j => by simpa [blkM_ll] using h (eN hN (Sum.inl i)) (eN hN (Sum.inl j)),
      fun i => by simpa [blkM_lr] using h (eN hN (Sum.inl i)) (eN hN (Sum.inr ())),
      fun j => by simpa [blkM_rl] using h (eN hN (Sum.inr ())) (eN hN (Sum.inl j)),
      by simpa [blkM_rr] using h (eN hN (Sum.inr ())) (eN hN (Sum.inr ()))⟩
  · rintro ⟨hA, hb, ha, hd⟩ i j
    obtain ⟨x, rfl⟩ := (eN hN).surjective i
    obtain ⟨y, rfl⟩ := (eN hN).surjective j
    rcases x with x | ⟨⟩ <;> rcases y with y | ⟨⟩ <;> simp [hA _ _, blkM_ll, blkM_lr, blkM_rl, blkM_rr, hb, ha, hd]
end Formalism.FourierDecayAlt.P.A5x8
