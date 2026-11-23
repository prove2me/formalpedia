-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.rep_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:31.291852+00:00
-- url     : https://prove2.me/submissions/d2c53ba5-6a1c-4a96-ad44-808c918cc01e

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpAlg
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpotentSubgroupRepresentation
import Theorems.Thm_CompanionTheory_D_gk_RF_rep_basis

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
theorem _root_.solution [CharZero K] (hJ : Jᴴ = J) (hd : IsUnit J.det) (hW : Isot J W) {d : ℕ} {w : Fin d → Fin n → K}
    (hs : Submodule.span K (Set.range w) = W) {X : Matrix (Fin n) (Fin n) K} (hX : InL J W X) :
    ∃ b : Fin d → Fin n → K, (∀ k, b k ∈ perp J W) ∧ ((∀ z, X *ᵥ z ∈ W) → ∀ k, b k ∈ W) ∧
      X = ∑ k, xw J (w k) (b k) := by
  classical
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K w
  have := Fintype.ofInjective a ha
  obtain ⟨b, h1, h2, h3⟩ := rep_basis hJ hd hW hli (hsp.trans hs) hX
  have hP : ∀ (S : Submodule K (Fin n → K)), (∀ k, b k ∈ S) → ∀ i, Function.extend a b 0 i ∈ S := fun S h i => by
    by_cases hi : ∃ k, a k = i
    · obtain ⟨k, rfl⟩ := hi
      rw [ha.extend_apply]; exact h k
    · rw [Function.extend_apply' _ _ _ hi]; exact S.zero_mem
  refine ⟨Function.extend a b 0, hP _ h1, fun h => hP _ (h2 h), h3.trans ?_⟩
  refine Fintype.sum_of_injective a ha _ _ (fun i hi => ?_) fun k => by rw [ha.extend_apply]; rfl
  rw [Function.extend_apply' _ _ _ hi]
  simp [xw]
end CompanionTheory.D.gk.RF
