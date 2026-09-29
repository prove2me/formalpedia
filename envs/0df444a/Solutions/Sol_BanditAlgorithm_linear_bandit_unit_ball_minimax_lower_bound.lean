-- Prove2me | solution 1 for BanditAlgorithm.linear_bandit_unit_ball_minimax_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T18:02:01.183822+00:00
-- url     : https://prove2.me/submissions/321ff845-72a2-43cf-876e-411ed7225001

import Theorems.Thm_BanditAlgorithm_linear_bandit_unit_ball_hypercube_regret_sum_lower_bound
import Mathlib.Tactic

open Matrix MeasureTheory
open BanditAlgorithm

/-!
The deterministic averaging and constant calculation finishing Lattimore--
Szepesvári, Theorem 24.2, pp. 290--291, from the hypercube regret-sum
inequality proved by the imported source-faithful probabilistic core.
-/

theorem solution {d n : ℕ}
    (hd : 0 < d) (hdn : d ≤ 2 * n) (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π) :
    ∃ θ : Fin d → ℝ, θ ⬝ᵥ θ = (d : ℝ) ^ 2 / (48 * n) ∧
      d * Real.sqrt n / (16 * Real.sqrt 3) ≤
        linearBanditExpectedRegret {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} θ π n := by
  classical
  have hn : 0 < n := by omega
  let Δ : ℝ := Real.sqrt ((d : ℝ) / (48 * n))
  let target : ℝ := n * Δ * Real.sqrt d / 4
  let regret : (Fin d → Bool) → ℝ := fun σ ↦
    linearBanditExpectedRegret
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1}
      (fun i ↦ Δ * if σ i then 1 else -1) π n
  have hsum :
      (Fintype.card (Fin d → Bool) : ℝ) * target ≤
        ∑ σ : Fin d → Bool, regret σ := by
    simpa [Δ, target, regret] using
      linear_bandit_unit_ball_hypercube_regret_sum_lower_bound
        hd hdn π hsupp
  have hexists : ∃ σ : Fin d → Bool, target ≤ regret σ := by
    by_contra h
    push_neg at h
    have hlt :
        (∑ σ : Fin d → Bool, regret σ) <
          ∑ _σ : Fin d → Bool, target := by
      apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      intro σ hσ
      exact h σ
    have hconst :
        (∑ _σ : Fin d → Bool, target) =
          (Fintype.card (Fin d → Bool) : ℝ) * target := by simp
    rw [hconst] at hlt
    exact (not_lt_of_ge hsum) hlt
  obtain ⟨σ, hσ⟩ := hexists
  let θ : Fin d → ℝ := fun i ↦ Δ * if σ i then 1 else -1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdenR : (0 : ℝ) < 48 * (n : ℝ) := by positivity
  have hratio : 0 ≤ (d : ℝ) / (48 * n) := by positivity
  have hΔsq : Δ ^ 2 = (d : ℝ) / (48 * n) := by
    dsimp [Δ]
    exact Real.sq_sqrt hratio
  have hθnorm : θ ⬝ᵥ θ = (d : ℝ) ^ 2 / (48 * n) := by
    calc
      θ ⬝ᵥ θ = ∑ i : Fin d, Δ ^ 2 := by
        simp only [θ, dotProduct]
        apply Finset.sum_congr rfl
        intro i hi
        split <;> ring
      _ = d * Δ ^ 2 := by simp
      _ = (d : ℝ) ^ 2 / (48 * n) := by
        rw [hΔsq]
        field_simp
  have hsqrtd : Real.sqrt (d : ℝ) ^ 2 = d :=
    Real.sq_sqrt hdR.le
  have hsqrtn : Real.sqrt (n : ℝ) ^ 2 = n :=
    Real.sq_sqrt hnR.le
  have hsqrt3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := by norm_num
  have hsqrt3pos : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have htarget_nonneg : 0 ≤ target := by
    dsimp [target, Δ]
    positivity
  have hrhs_nonneg :
      0 ≤ (d : ℝ) * Real.sqrt n / (16 * Real.sqrt 3) := by
    positivity
  have htarget_sq :
      target ^ 2 =
        ((d : ℝ) * Real.sqrt n / (16 * Real.sqrt 3)) ^ 2 := by
    calc
      target ^ 2 =
          (n : ℝ) ^ 2 * Δ ^ 2 * (Real.sqrt d) ^ 2 / 16 := by
        dsimp [target]
        ring
      _ = (n : ℝ) ^ 2 * Δ ^ 2 * d / 16 := by rw [hsqrtd]
      _ = (d : ℝ) ^ 2 * n / 768 := by
        rw [hΔsq]
        field_simp [ne_of_gt hnR]
        ring
      _ = (d : ℝ) ^ 2 * (Real.sqrt n) ^ 2 /
          (256 * (Real.sqrt 3) ^ 2) := by
        rw [hsqrtn, hsqrt3]
        ring
      _ = ((d : ℝ) * Real.sqrt n /
          (16 * Real.sqrt 3)) ^ 2 := by ring
  have htarget :
      target = (d : ℝ) * Real.sqrt n / (16 * Real.sqrt 3) := by
    nlinarith
  refine ⟨θ, hθnorm, ?_⟩
  rw [← htarget]
  simpa [regret, θ] using hσ
