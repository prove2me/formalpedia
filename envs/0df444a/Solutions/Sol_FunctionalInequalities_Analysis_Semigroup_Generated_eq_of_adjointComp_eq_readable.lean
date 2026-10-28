-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Semigroup.Generated.eq_of_adjointComp_eq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:28:04.790878+00:00
-- url     : https://prove2.me/submissions/9e34dc51-cdce-45ef-be49-643dc85ff3ce

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Convergence
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Inverse

section
noncomputable section
open Filter Topology Set
open scoped RealInnerProductSpace LinearPMap
section
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
omit [CompleteSpace H₁] in
include hd in
/-- On the operator domain, `A y = 0` exactly when `T y = 0`. -/
theorem FunctionalInequalities.Analysis.Semigroup.Generated.adjointComp_eq_zero_iff (y : (adjointComp T).domain) :
    adjointComp T y = 0 ↔ T ⟨y, y.2.2⟩ = 0 := by
  constructor
  · intro hA
    have hnorm2 : ‖T ⟨(y : H₀), y.2.2⟩‖ ^ 2 = 0 := by
      rw [← inner_adjointComp_self hd y, hA, inner_zero_left]
    have hnorm : ‖T ⟨(y : H₀), y.2.2⟩‖ = 0 := by
      nlinarith [hnorm2]
    exact norm_eq_zero.mp hnorm
  · intro h
    refine hd.eq_zero_of_inner_left ℝ (fun z hz => ?_)
    rw [inner_adjointComp hd y hz, h, inner_zero_left]
end
end
end

noncomputable section
open scoped InnerProductSpace RealInnerProductSpace
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
open Filter Topology Set
omit [CompleteSpace H₁] in
include hd in
/-- Uniqueness: two operator-domain vectors orthogonal to `ker T` with the same image under `A`
coincide. -/
theorem solution (u v : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain)
    (hu : ∀ k : T.domain, T k = 0 → ⟪(u : H₀), (k : H₀)⟫ = 0)
    (hv : ∀ k : T.domain, T k = 0 → ⟪(v : H₀), (k : H₀)⟫ = 0)
    (huv : FunctionalInequalities.Analysis.Semigroup.adjointComp T u = FunctionalInequalities.Analysis.Semigroup.adjointComp T v) : (u : H₀) = v := by
    let w : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain := u - v
    have hAw : FunctionalInequalities.Analysis.Semigroup.adjointComp T w = 0 := by
      change FunctionalInequalities.Analysis.Semigroup.adjointComp T (u - v) = 0
      rw [LinearPMap.map_sub, huv, sub_self]
    have hTw : T ⟨(w : H₀), w.2.2⟩ = 0 :=
      (FunctionalInequalities.Analysis.Semigroup.Generated.adjointComp_eq_zero_iff T hd w).mp hAw
    have hinneru : ⟪(u : H₀), (w : H₀)⟫_ℝ = 0 := by
      exact hu ⟨(w : H₀), w.2.2⟩ hTw
    have hinnerv : ⟪(v : H₀), (w : H₀)⟫_ℝ = 0 := by
      exact hv ⟨(w : H₀), w.2.2⟩ hTw
    have hww : ⟪(w : H₀), (w : H₀)⟫_ℝ = 0 := by
      change ⟪(u : H₀) - (v : H₀), (w : H₀)⟫_ℝ = 0
      rw [inner_sub_left, hinneru, hinnerv, sub_zero]
    have hwzero : (w : H₀) = 0 := inner_self_eq_zero.mp hww
    change (u : H₀) - (v : H₀) = 0 at hwzero
    exact sub_eq_zero.mp hwzero
