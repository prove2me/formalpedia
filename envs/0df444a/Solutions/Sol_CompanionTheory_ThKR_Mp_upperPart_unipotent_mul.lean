-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.upperPart_unipotent_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:27:18.417959+00:00
-- url     : https://prove2.me/submissions/0fb5f445-0a61-4b6d-af4c-64990b5ad12d

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticUnipotentBlockSecondDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
namespace CompanionTheory.ThKR.Mp
theorem _root_.solution (S : Matrix l l ℝ) (t : ℝ) (s : Mat l) :
    upperParabolic (nn S t * s) = upperParabolic s + (t : ℂ) • (S.map ofReal * loQ s) := by
  ext a b
  simp only [upperParabolic, loQ, nn, Matrix.add_apply, Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, Matrix.one_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, ofReal_add, ofReal_sum, ofReal_mul]
  have e : ∀ u v : l → ℝ, ∑ c, (t : ℂ) * (S a c : ℂ) * (u c : ℂ) - I * ∑ c, (t : ℂ) * (S a c : ℂ) * (v c : ℂ) =
      (t : ℂ) * ∑ c, (S a c : ℂ) * ((u c : ℂ) - I * (v c : ℂ)) := fun u v => by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [← e]
  ring
end CompanionTheory.ThKR.Mp
