-- Prove2me | solution 1 for CompanionTheory.ThKR.LL.intw_of_sympl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:02.942701+00:00
-- url     : https://prove2.me/submissions/2d16c465-5893-4270-991b-0abf9ed47120

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_NormExpSubLe
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_LocalLift
import Theorems.Thm_CompanionTheory_ThKR_LL_pPart_mulVec
import Theorems.Thm_CompanionTheory_ThKR_LL_qPart_mulVec
import Theorems.Thm_CompanionTheory_ThKR_LL_intw_big


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.LL
variable {l : Type} [Fintype l] [DecidableEq l]
namespace CompanionTheory.ThKR.LL
theorem _root_.solution {g : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hg : ∀ w w', sympl (g *ᵥ w) (g *ᵥ w') = sympl w w')
    (h : IsUnit (bl Sum.inl Sum.inl g)) (c : ℝ) (w : l ⊕ l → ℝ) :
    Intw (big (Ring.inverse (bl Sum.inl Sum.inl g)) (bl Sum.inl Sum.inr g) (bl Sum.inr Sum.inl g) c) (pPart w) (qPart w)
      (pPart (g *ᵥ w)) (qPart (g *ᵥ w)) := by
  have key : ∀ p q p' q' : Eu l, ⟪bl Sum.inl Sum.inl g p + bl Sum.inl Sum.inr g q,
      bl Sum.inr Sum.inl g p' + bl Sum.inr Sum.inr g q'⟫ - ⟪bl Sum.inr Sum.inl g p + bl Sum.inr Sum.inr g q,
      bl Sum.inl Sum.inl g p' + bl Sum.inl Sum.inr g q'⟫ = ⟪p, q'⟫ - ⟪q, p'⟫ := fun p q p' q' => by
    have := hg (Sum.elim (fun i => p i) fun i => q i) (Sum.elim (fun i => p' i) fun i => q' i)
    simp only [sympl, pPart_mulVec, qPart_mulVec] at this
    exact this
  rw [pPart_mulVec, qPart_mulVec]
  refine intw_big h.ringInverse (fun x => ?_) (fun x => ?_) (fun y z => ?_) (fun y z => ?_) (fun y z => ?_) c _ _
  · rw [← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ h, ContinuousLinearMap.one_apply]
  · rw [← ContinuousLinearMap.mul_apply, Ring.inverse_mul_cancel _ h, ContinuousLinearMap.one_apply]
  · simpa [sub_eq_zero] using key y 0 z 0
  · simpa [sub_eq_zero] using key 0 y 0 z
  · simpa using key y 0 0 z
end CompanionTheory.ThKR.LL
