-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.integral_points_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:47.289512+00:00
-- url     : https://prove2.me/submissions/f0c0c9c4-50df-4087-b508-4a8c271ad4c5

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_isCompact_intPairs
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_isInt_orbZ_inv
import Theorems.Thm_Formalism_DoubleCosetMeasures_Final_intTwoSided
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_intTwoSided
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_isOpen_intSub
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A5.IntFinite := by
  intro K _ _ _ R ψ hL w
  have := hL.t2
  classical
  let f : lowW K w.1 w.2 × upUniG K w.1.sum → ℝ := fun p => if IsInt R (orbZ w p) then 1 else 0
  have hinv : ∀ a ∈ intSub R (lowW K w.1 w.2), ∀ b ∈ intSub R (upUniG K w.1.sum),
      ∀ (x : lowW K w.1 w.2) (y : upUniG K w.1.sum), f (a * x, y * b) = f (x, y) := by
    intro a ha b hb x y
    simp only [f, isInt_orbZ_inv R w a ha b hb x y]
  have hS := isCompact_intPairs R hL.isCompact w.1 w.2
  have hc : HasCompactSupport f := by
    refine hS.of_isClosed_subset isClosed_closure (closure_minimal ?_ hS.isClosed)
    intro p hp
    by_contra hn
    apply hp
    simp only [f]
    rw [if_neg]
    exact hn
  have : (0 : Measure (lowW K w.1 w.2)).IsMulRightInvariant := ⟨fun g => by simp⟩
  have : (0 : Measure (upUniG K w.1.sum)).IsMulLeftInvariant := ⟨fun g => by simp⟩
  have key := (Formalism.DoubleCosetMeasures.P.intTwoSided (lowW K w.1 w.2) (upUniG K w.1.sum) 0 0
    (intSub R (lowW K w.1 w.2)) (intSub R (upUniG K w.1.sum))
    (Formalism.DoubleCosetMeasures.P.isOpen_intSub R hL.isOpen _) (Formalism.DoubleCosetMeasures.P.isOpen_intSub R hL.isOpen _) ℝ f hinv hc).1
  refine key.subset ?_
  intro q hq
  have hq' : IsInt R (orbZ w (q.1.out, q.2.out)) := hq
  simp [f, hq']
end Formalism.FourierDecayAlt.P
