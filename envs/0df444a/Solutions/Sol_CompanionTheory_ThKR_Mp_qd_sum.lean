-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.qd_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:23:53.885805+00:00
-- url     : https://prove2.me/submissions/d359b1fe-7faf-4deb-8667-a1397ea2c31a

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MpFOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real ContDiff RealInnerProductSpace
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
namespace CompanionTheory.ThKR.Mp
theorem _root_.solution (X : Mat l) (f : Sch l) : ∑ a, ∑ b, X a b • Qd (Matrix.single a b 1) f = Qd X f := by
  show _ = qdLin f X
  conv_rhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [show Matrix.single a b (X a b) = X a b • Matrix.single a b (1 : ℝ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul]
  rfl
end CompanionTheory.ThKR.Mp
