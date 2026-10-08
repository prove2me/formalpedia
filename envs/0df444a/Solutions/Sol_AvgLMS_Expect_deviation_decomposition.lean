-- Prove2me | solution 1 for AvgLMS.Expect.deviation_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:16:10.68685+00:00
-- url     : https://prove2.me/submissions/4b209a5b-5c4e-48e9-93ca-9d6629c96151

import Mathlib
import Definitions.Def_AvgLMS_Expect_Model

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

open AvgLMS.Expect in
theorem AvgLMS_dd_step {Ω : Type*} {d : ℕ} (x z : ℕ → Ω → Hs d) (θstar θ0 : Hs d)
    (γ : ℝ) (n : ℕ) (ω : Ω) :
    lmsIter γ θ0 x z (n + 1) ω - θstar =
      (1 - γ • rankOne (x (n + 1) ω)) (lmsIter γ θ0 x z n ω - θstar) +
        γ • residual x z θstar (n + 1) ω := by
  simp only [lmsIter, AvgLMS.Expect.residual, rankOne, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_sub_right]
  rw [real_inner_comm (x (n + 1) ω) θstar,
    real_inner_comm (x (n + 1) ω) (lmsIter γ θ0 x z n ω)]
  module

open AvgLMS.Expect in
theorem AvgLMS_dd_Mprod_succ {Ω : Type*} {d : ℕ} (γ : ℝ) (x : ℕ → Ω → Hs d) (i m : ℕ) (ω : Ω) :
    Mprod γ x i (m + 1) ω = (1 - γ • rankOne (x (i + m) ω)) * Mprod γ x i m ω := rfl

open AvgLMS.Expect in
theorem solution {Ω : Type*} {d : ℕ} (x z : ℕ → Ω → Hs d) (θstar θ0 : Hs d)
    (γ : ℝ) (n : ℕ) (ω : Ω) :
    lmsIter γ θ0 x z n ω - θstar =
      Mprod γ x 1 n ω (θ0 - θstar) +
        γ • ∑ k ∈ Finset.Icc 1 n, Mprod γ x (k + 1) (n - k) ω (residual x z θstar k ω) := by
  induction n with
  | zero => simp [lmsIter, Mprod]
  | succ n ih =>
    rw [AvgLMS_dd_step, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    have hM : ∀ k ∈ Finset.Icc 1 n,
        Mprod γ x (k + 1) (n + 1 - k) ω (residual x z θstar k ω) =
          (1 - γ • rankOne (x (n + 1) ω))
            (Mprod γ x (k + 1) (n - k) ω (residual x z θstar k ω)) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have h1 : n + 1 - k = (n - k) + 1 := by omega
      have h2 : k + 1 + (n - k) = n + 1 := by omega
      rw [h1, AvgLMS_dd_Mprod_succ, h2, ContinuousLinearMap.mul_apply]
    rw [Finset.sum_congr rfl hM, ← map_sum]
    have h0 : Mprod γ x 1 (n + 1) ω = (1 - γ • rankOne (x (n + 1) ω)) * Mprod γ x 1 n ω := by
      rw [AvgLMS_dd_Mprod_succ, Nat.add_comm 1 n]
    rw [h0, ContinuousLinearMap.mul_apply, Nat.sub_self]
    simp only [Mprod, ContinuousLinearMap.one_apply, map_add, map_smul, smul_add]
    abel
