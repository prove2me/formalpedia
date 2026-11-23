-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.inv_phase
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:16:16.060541+00:00
-- url     : https://prove2.me/submissions/59d41ce1-e83d-4043-b11a-164658b3ea35

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_DoubleCosetMeasures_Final_simpleAdd
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_simpleAdd
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
theorem _root_.solution (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) (w : Point K)
    (a : lowW K w.1 w.2) (ha : a ∈ intSub R (lowW K w.1 w.2))
    (b : upUniG K w.1.sum) (hb : b ∈ intSub R (upUniG K w.1.sum))
    (x : lowW K w.1 w.2) (y : upUniG K w.1.sum) :
    phase ψ ((a * x, y * b) : lowW K w.1 w.2 × upUniG K w.1.sum) = phase ψ (x, y) := by
  have hSA := Formalism.DoubleCosetMeasures.Final.simpleAdd
  unfold phase
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [(hSA K _ _ _).1 a.2.1 x.2.1, (hSA K _ _ _).2 y.2 b.2]
  have hLa : sLow ((a : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) ∈ R := by
    unfold sLow
    refine R.sum_mem fun j _ => ?_
    split_ifs
    · exact ha.1 _ _
    · exact R.zero_mem
  have hUb : sUp ((b : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) ∈ R := by
    unfold sUp
    refine R.sum_mem fun j _ => ?_
    split_ifs
    · exact hb.1 _ _
    · exact R.zero_mem
  have key : ∀ p q r s : K, p + q + (r + s) = (q + r) + (p + s) := by
    intro p q r s
    ring
  rw [key, AddChar.map_add_eq_mul, hψ _ (R.add_mem hLa hUb), mul_one]
end Formalism.FourierDecayAlt.P.A5x8
