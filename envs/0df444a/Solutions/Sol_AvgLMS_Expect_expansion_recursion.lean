-- Prove2me | solution 1 for AvgLMS.Expect.expansion_recursion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:21:38.338046+00:00
-- url     : https://prove2.me/submissions/758d998e-6a51-451d-9d8a-6da7a2b1e196

import Mathlib
import Definitions.Def_AvgLMS_Expect_Model

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

set_option autoImplicit false

open AvgLMS.Expect InnerProductSpace RealInnerProductSpace in
theorem AvgLMS_Expect_etaR_sum_succ {Ω : Type*} {d : ℕ} (γ : ℝ) (H : Hs d →L[ℝ] Hs d)
    (x ξ : ℕ → Ω → Hs d) (n : ℕ) (ω : Ω) (r : ℕ) :
    ∑ i ∈ Finset.range (r + 1), etaR γ H x ξ i (n + 1) ω =
      (∑ i ∈ Finset.range (r + 1), etaR γ H x ξ i n ω) -
        γ • H (∑ i ∈ Finset.range (r + 1), etaR γ H x ξ i n ω) + γ • ξ (n + 1) ω +
        γ • (H (∑ i ∈ Finset.range r, etaR γ H x ξ i n ω) -
          ⟪x (n + 1) ω, ∑ i ∈ Finset.range r, etaR γ H x ξ i n ω⟫_ℝ • x (n + 1) ω) := by
  induction r with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, Finset.range_zero, Finset.sum_empty, map_zero,
      inner_zero_right, zero_smul, sub_zero, smul_zero, add_zero]
    rw [etaR]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.smul_apply]
  | succ r ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun i => etaR γ H x ξ i n ω) (r + 1),
      Finset.sum_range_succ (fun i => etaR γ H x ξ i n ω) r]
    rw [etaR]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.smul_apply, map_add, inner_add_right, add_smul, smul_add, smul_sub]
    abel

open AvgLMS.Expect InnerProductSpace RealInnerProductSpace in
theorem solution {Ω : Type*} {d : ℕ} (x z : ℕ → Ω → Hs d) (H : Hs d →L[ℝ] Hs d)
    (θstar θ0 : Hs d) (γ : ℝ) (r n : ℕ) (ω : Ω) :
    (lmsIter γ θ0 x z (n + 1) ω - θstar) -
        ∑ i ∈ Finset.range (r + 1), etaR γ H x (residual x z θstar) i (n + 1) ω =
      (lmsIter γ θ0 x z n ω - θstar -
          ∑ i ∈ Finset.range (r + 1), etaR γ H x (residual x z θstar) i n ω) -
        γ • (⟪x (n + 1) ω, lmsIter γ θ0 x z n ω - θstar -
          ∑ i ∈ Finset.range (r + 1), etaR γ H x (residual x z θstar) i n ω⟫_ℝ • x (n + 1) ω) +
        γ • (H (etaR γ H x (residual x z θstar) r n ω) -
          ⟪x (n + 1) ω, etaR γ H x (residual x z θstar) r n ω⟫_ℝ • x (n + 1) ω) := by
  rw [AvgLMS_Expect_etaR_sum_succ, Finset.sum_range_succ (fun i => etaR γ H x _ i n ω) r]
  have hl : lmsIter γ θ0 x z (n + 1) ω = lmsIter γ θ0 x z n ω -
      γ • (⟪lmsIter γ θ0 x z n ω, x (n + 1) ω⟫_ℝ • x (n + 1) ω - z (n + 1) ω) := rfl
  rw [hl]
  have hres : AvgLMS.Expect.residual x z θstar (n + 1) ω =
      z (n + 1) ω - ⟪θstar, x (n + 1) ω⟫_ℝ • x (n + 1) ω := rfl
  rw [hres]
  generalize (∑ i ∈ Finset.range r, etaR γ H x (AvgLMS.Expect.residual x z θstar) i n ω) = A
  generalize etaR γ H x (AvgLMS.Expect.residual x z θstar) r n ω = B
  generalize lmsIter γ θ0 x z n ω = θ
  generalize x (n + 1) ω = X
  generalize z (n + 1) ω = Z
  simp only [map_add, inner_add_right, inner_sub_right, real_inner_comm θ X,
    real_inner_comm θstar X]
  module
