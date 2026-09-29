-- Prove2me | solution 1 for FoundationsML.ReinforcementLearning.value_iteration_converges
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T16:35:19.660993+00:00
-- url     : https://prove2.me/submissions/4fbe731e-8335-4ddc-9a74-78fc0330a0e6

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_BellmanOperator

set_option autoImplicit false

open FoundationsML.ReinforcementLearning in
theorem rl_bellop_pt_le {S A : Type*} [Fintype S] [Fintype A]
    (hA : (Finset.univ : Finset A).Nonempty)
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (Er : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (V W : S → ℝ) (s : S) :
    BellmanOperator hA P Er γ V s ≤ BellmanOperator hA P Er γ W s + γ * ‖V - W‖ := by
  unfold BellmanOperator
  refine Finset.sup'_le hA _ (fun a _ => ?_)
  have hle : ∑ s' : S, P s a s' * V s' ≤ ∑ s' : S, P s a s' * W s' + ‖V - W‖ := by
    have h1 : ∑ s' : S, P s a s' * V s' - ∑ s' : S, P s a s' * W s'
        = ∑ s' : S, P s a s' * (V s' - W s') := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    have h2 : ∑ s' : S, P s a s' * (V s' - W s') ≤ ∑ s' : S, P s a s' * ‖V - W‖ := by
      apply Finset.sum_le_sum
      intro s' _
      apply mul_le_mul_of_nonneg_left _ ((hP s a).1 s')
      have h3 : ‖(V - W) s'‖ ≤ ‖V - W‖ := norm_le_pi_norm (V - W) s'
      rw [Pi.sub_apply, Real.norm_eq_abs] at h3
      exact le_trans (le_abs_self _) h3
    have h4 : ∑ s' : S, P s a s' * ‖V - W‖ = ‖V - W‖ := by
      rw [← Finset.sum_mul, (hP s a).2, one_mul]
    linarith
  have hW : Er s a + γ * ∑ s' : S, P s a s' * W s' ≤
      Finset.univ.sup' hA (fun a : A => Er s a + γ * ∑ s' : S, P s a s' * W s') :=
    Finset.le_sup' (fun a : A => Er s a + γ * ∑ s' : S, P s a s' * W s') (Finset.mem_univ a)
  have hm : γ * ∑ s' : S, P s a s' * V s' ≤ γ * (∑ s' : S, P s a s' * W s' + ‖V - W‖) :=
    mul_le_mul_of_nonneg_left hle hγ0
  nlinarith

open FoundationsML.ReinforcementLearning in
theorem rl_bellop_lip {S A : Type*} [Fintype S] [Fintype A]
    (hA : (Finset.univ : Finset A).Nonempty)
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (Er : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (V W : S → ℝ) :
    ‖BellmanOperator hA P Er γ V - BellmanOperator hA P Er γ W‖ ≤ γ * ‖V - W‖ := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hγ0 (norm_nonneg _))).2 (fun s => ?_)
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_le_iff]
  have h1 := rl_bellop_pt_le hA P hP Er γ hγ0 V W s
  have h2 := rl_bellop_pt_le hA P hP Er γ hγ0 W V s
  rw [norm_sub_rev W V] at h2
  constructor <;> linarith

open FoundationsML.ReinforcementLearning in
theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (hA : (Finset.univ : Finset A).Nonempty)
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (Er : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (Vstar : S → ℝ) (hVstar : BellmanOperator hA P Er γ Vstar = Vstar)
    (V0 : S → ℝ) :
    Filter.Tendsto (fun n : ℕ => (BellmanOperator hA P Er γ)^[n] V0) Filter.atTop
      (nhds Vstar) := by
  have hb : ∀ n : ℕ, ‖(BellmanOperator hA P Er γ)^[n] V0 - Vstar‖ ≤ γ ^ n * ‖V0 - Vstar‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc ‖BellmanOperator hA P Er γ ((BellmanOperator hA P Er γ)^[n] V0) - Vstar‖
          = ‖BellmanOperator hA P Er γ ((BellmanOperator hA P Er γ)^[n] V0) -
              BellmanOperator hA P Er γ Vstar‖ := by rw [hVstar]
        _ ≤ γ * ‖(BellmanOperator hA P Er γ)^[n] V0 - Vstar‖ :=
            rl_bellop_lip hA P hP Er γ hγ0 _ _
        _ ≤ γ * (γ ^ n * ‖V0 - Vstar‖) := mul_le_mul_of_nonneg_left ih hγ0
        _ = γ ^ (n + 1) * ‖V0 - Vstar‖ := by ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Filter.Tendsto (fun n : ℕ => γ ^ n * ‖V0 - Vstar‖) Filter.atTop (nhds 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).mul_const ‖V0 - Vstar‖
    simpa using this
  exact squeeze_zero (fun n => norm_nonneg _) hb hlim
