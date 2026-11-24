-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.PrincipalizationRules.outputLevelData_maxOrderReduction_eq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:32:15.475338+00:00
-- url     : https://prove2.me/submissions/8566219d-a540-4b51-b923-5473dcbd116c

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReductionProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_DimensionRecursion
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedIdealWithBoundary_SameNontrivialBoundary_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
namespace PrincipalizationRules
private theorem nextLevel_orderReduction_congr (B : PrincipalizationRules.{u}) (L L' : OrderReductionData.{u})
    (T : MarkedIdealWithBoundary.{u})
    (h : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → L.maxOrderRed S = L'.maxOrderRed S) :
    (B.nextLevel L).orderRed T = (B.nextLevel L').orderRed T := by
  have hfun : (fun (S : MarkedIdealWithBoundary.{u}) (_ : S.krullDimSucc ≤ T.krullDimSucc) (j : ℕ) =>
        B.divisorFamily L.maxOrderRed j S)
      = (fun (S : MarkedIdealWithBoundary.{u}) (_ : S.krullDimSucc ≤ T.krullDimSucc) (j : ℕ) =>
        B.divisorFamily L'.maxOrderRed j S) := by
    funext S hS j
    have hinner : (fun (S' : MarkedIdealWithBoundary.{u}) (_ : S'.krullDimSucc < S.krullDimSucc) => L.maxOrderRed S')
        = (fun (S' : MarkedIdealWithBoundary.{u}) (_ : S'.krullDimSucc < S.krullDimSucc) => L'.maxOrderRed S') := by
      funext S' h'
      exact h S' (lt_of_lt_of_le h' hS)
    show B.divisorRed S (fun S' _ => L.maxOrderRed S') j
        = B.divisorRed S (fun S' _ => L'.maxOrderRed S') j
    exact congrArg (fun f => B.divisorRed S f j) hinner
  show B.orderRed T (fun S _ j => B.divisorFamily L.maxOrderRed j S)
      = B.orderRed T (fun S _ j => B.divisorFamily L'.maxOrderRed j S)
  exact congrArg (B.orderRed T) hfun
private theorem nextLevel_maxOrderReduction_congr (B : PrincipalizationRules.{u}) (L L' : OrderReductionData.{u})
    (T : MarkedIdealWithBoundary.{u})
    (h : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → L.maxOrderRed S = L'.maxOrderRed S) :
    (B.nextLevel L).maxOrderRed T = (B.nextLevel L').maxOrderRed T := by
  have hfun : (fun (S : MarkedIdealWithBoundary.{u}) (_ : S.krullDimSucc ≤ T.krullDimSucc) => (B.nextLevel L).orderRed S)
      = (fun (S : MarkedIdealWithBoundary.{u}) (_ : S.krullDimSucc ≤ T.krullDimSucc) => (B.nextLevel L').orderRed S) := by
    funext S hS
    exact nextLevel_orderReduction_congr B L L' S (fun S' h' => h S' (lt_of_lt_of_le h' hS))
  show B.maxOrderRed T (fun S _ => (B.nextLevel L).orderRed S)
      = B.maxOrderRed T (fun S _ => (B.nextLevel L').orderRed S)
  exact congrArg (B.maxOrderRed T) hfun
private theorem inputLevelData_reductions_eq_of_dim_lt (B : PrincipalizationRules.{u}) :
    ∀ (d : ℕ) (T : MarkedIdealWithBoundary.{u}), T.krullDimSucc ≤ d → ∀ m M : ℕ, d < m → m ≤ M →
      (B.inputLevelData m).maxOrderRed T = (B.inputLevelData M).maxOrderRed T ∧
        (B.inputLevelData m).orderRed T = (B.inputLevelData M).orderRed T := by
  intro d
  induction d with
  | zero =>
      intro T hT m M hm hmM
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      have h0 : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc →
          (B.inputLevelData m').maxOrderRed S = (B.inputLevelData M').maxOrderRed S := by
        intro S hS
        exact absurd (lt_of_lt_of_le hS hT) (Nat.not_lt_zero _)
      exact ⟨nextLevel_maxOrderReduction_congr B (B.inputLevelData m') (B.inputLevelData M') T h0,
        nextLevel_orderReduction_congr B (B.inputLevelData m') (B.inputLevelData M') T h0⟩
  | succ d ih =>
      intro T hT m M hm hmM
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      have h0 : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc →
          (B.inputLevelData m').maxOrderRed S = (B.inputLevelData M').maxOrderRed S := by
        intro S hS
        exact (ih S (by omega) m' M' (by omega) (by omega)).1
      exact ⟨nextLevel_maxOrderReduction_congr B (B.inputLevelData m') (B.inputLevelData M') T h0,
        nextLevel_orderReduction_congr B (B.inputLevelData m') (B.inputLevelData M') T h0⟩
end PrincipalizationRules
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.PrincipalizationRules
namespace FunctorialResolution.EmbeddedResolution.PrincipalizationRules
theorem _root_.solution (B : PrincipalizationRules.{u}) {n N : ℕ} (hnN : n ≤ N)
    (T : MarkedIdealWithBoundary.{u}) (hT : T.krullDimSucc ≤ n) :
    (B.outputLevelData N).maxOrderRed T = (B.outputLevelData n).maxOrderRed T :=
  (inputLevelData_reductions_eq_of_dim_lt B n T hT (n + 1) (N + 1) (Nat.lt_succ_self n)
    (Nat.succ_le_succ hnN)).1.symm
end FunctorialResolution.EmbeddedResolution.PrincipalizationRules
