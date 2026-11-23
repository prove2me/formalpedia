-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.skew_of_hf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:35.473677+00:00
-- url     : https://prove2.me/submissions/fb1836e0-77e8-4b0d-b654-35d0c3759b03

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpAlg
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpotentSubgroupRepresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.RF
variable {K : Type} [Field K] [StarRing K] {n : ℕ} {J : Matrix (Fin n) (Fin n) K} {W : Submodule K (Fin n → K)}
namespace CompanionTheory.D.gk.RF
theorem _root_.solution {X : Matrix (Fin n) (Fin n) K} (h : ∀ x y, hf J (X *ᵥ x) y = -hf J x (X *ᵥ y)) :
    Xᴴ * J + J * X = 0 := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  unfold hf at this
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, ← dotProduct_neg, ← neg_mulVec] at this
  have e : star (Pi.single i 1 : Fin n → K) = Pi.single i 1 := by
    ext k; by_cases hk : k = i <;> simp [hk]
  simp only [e, mulVec_single_one, single_one_dotProduct, Matrix.col_apply, Matrix.neg_apply] at this
  simp [this]
end CompanionTheory.D.gk.RF
