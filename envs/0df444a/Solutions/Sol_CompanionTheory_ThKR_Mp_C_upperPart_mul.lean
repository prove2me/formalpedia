-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.C.upperPart_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:21:24.849417+00:00
-- url     : https://prove2.me/submissions/f74c7585-efa6-48dd-8ab1-0cb1cf0d695b

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MapOfRealMul

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
open scoped Real
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open CompanionTheory.ThKR.Mp.C
namespace CompanionTheory.ThKR.Mp.C
theorem _root_.solution (s s' : Mat l) :
    upperParabolic (s * s') = s.toBlocks₁₁.map Complex.ofReal * upperParabolic s' + s.toBlocks₁₂.map Complex.ofReal * loQ s' := by
  ext a b
  have e : ∀ x y : ℂ, x * (I * y) = I * (x * y) := fun x y => mul_left_comm x I y
  simp only [upperParabolic, loQ, Matrix.mul_apply, Matrix.add_apply, Matrix.map_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
    Matrix.of_apply, Fintype.sum_sum_type, Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul, mul_sub,
    Finset.sum_sub_distrib, mul_add, Finset.mul_sum, e]
  ring
end CompanionTheory.ThKR.Mp.C
