-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.iso_last_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:49:51.417875+00:00
-- url     : https://prove2.me/submissions/9c77cff9-e496-4bd8-96a2-97ee765270cb

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
variable {K : Type} [CommRing K] {m N : ℕ} (hN : N = m + 1)
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (w : Fin N → K) :
    (∑ j : Fin N, if j.val + 1 = N then w j else 0) = w (eN hN (Sum.inr ())) := by
  rw [← (eN hN).sum_comp, Fintype.sum_sum_type]
  have h1 : ∀ i : Fin m, ¬ ((eN hN (Sum.inl i) : Fin N) : ℕ) + 1 = N := by
    intro i
    have := i.isLt
    rw [eN_inl]
    omega
  have h2 : ((eN hN (Sum.inr ()) : Fin N) : ℕ) + 1 = N := by
    rw [eN_inr]
    omega
  simp [h1, h2]
end Formalism.FourierDecayAlt.P.A5x8
