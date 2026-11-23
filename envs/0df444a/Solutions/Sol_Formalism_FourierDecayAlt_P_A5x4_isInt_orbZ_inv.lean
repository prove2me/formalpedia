-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x4.isInt_orbZ_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:18.695818+00:00
-- url     : https://prove2.me/submissions/c984f523-5080-4011-9d58-d16e77e47b9b

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Theorems.Thm_Formalism_DoubleCosetMeasures_Final_intInv
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_intInv
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
noncomputable section
open MeasureTheory Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x4
namespace Formalism.FourierDecayAlt.P.A5x4
theorem _root_.solution {K : Type} [CommRing K] (R : Subring K) (w : Point K)
    (a : lowW K w.1 w.2) (ha : a ∈ intSub R (lowW K w.1 w.2))
    (b : upUniG K w.1.sum) (hb : b ∈ intSub R (upUniG K w.1.sum))
    (x : lowW K w.1 w.2) (y : upUniG K w.1.sum) :
    IsInt R (orbZ w (a * x, y * b)) ↔ IsInt R (orbZ w (x, y)) := by
  have h := Formalism.DoubleCosetMeasures.P.intInv K R w.1.sum _ _ (orbZ w (x, y)) a.2.1 b.2 ha.1 hb.1
  rw [← h]
  have : orbZ w (a * x, y * b) =
      ((a : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) * orbZ w (x, y) *
        ((b : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) := by
    simp only [orbZ, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
  rw [this]
end Formalism.FourierDecayAlt.P.A5x4
