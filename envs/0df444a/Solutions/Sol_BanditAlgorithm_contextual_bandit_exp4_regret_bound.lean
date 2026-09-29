-- Prove2me | solution 1 for BanditAlgorithm.contextual_bandit_exp4_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-28T23:31:14.012618+00:00
-- url     : https://prove2.me/submissions/685778a7-27a8-4dd5-84a5-fd2e9ef2e13f

import Theorems.Thm_BanditAlgorithm_exp4_regret_general_eta_bound

open MeasureTheory ProbabilityTheory

open BanditAlgorithm

/-!
Lattimore--Szepesvári, *Bandit Algorithms*, Theorem 18.1, printed p. 230,
Eq. (18.7).  The imported theorem is the source's pre-optimization estimate
`Rₙ ≤ log M / η + η n k / 2`, obtained from Eqs. (18.11)--(18.12).
-/

theorem solution
    {k M : ℕ} (hk : 0 < k) (hM : 1 < M) (n : ℕ) (hn : 0 < n)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ a : Fin k, x t a ∈ Set.Icc (0 : ℝ) 1)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (π : BanditPolicy k)
    (hπ : IsExp4Policy (Real.sqrt (2 * Real.log M / (n * k))) 0 E π) :
    exp4Regret n x E π ≤ Real.sqrt (2 * n * k * Real.log M) := by
  let η : ℝ := Real.sqrt (2 * Real.log M / ((n : ℝ) * k))
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hMR : 1 < (M : ℝ) := by exact_mod_cast hM
  have hlog : 0 < Real.log (M : ℝ) := Real.log_pos hMR
  have hbase : 0 < 2 * Real.log M / ((n : ℝ) * k) := by positivity
  have hη : 0 < η := Real.sqrt_pos.2 hbase
  have hηsq : η ^ 2 = 2 * Real.log M / ((n : ℝ) * k) := by
    dsimp [η]
    exact Real.sq_sqrt hbase.le
  have hgeneral :=
    exp4_regret_general_eta_bound hk hM n hn η hη x hx E hE0 hE1 π
      (by simpa [η] using hπ)
  calc
    exp4Regret n x E π
        ≤ Real.log M / η + η * ((n : ℝ) * k) / 2 := hgeneral
    _ = η * ((n : ℝ) * k) := by
      field_simp [ne_of_gt hη, ne_of_gt hnR, ne_of_gt hkR] at hηsq ⊢
      nlinarith
    _ = Real.sqrt (2 * n * k * Real.log M) := by
      have hleft : 0 ≤ η * ((n : ℝ) * k) := by positivity
      have hright : 0 ≤ Real.sqrt (2 * (n : ℝ) * k * Real.log M) :=
        Real.sqrt_nonneg _
      have hrad : 0 ≤ 2 * (n : ℝ) * k * Real.log M := by positivity
      apply (sq_eq_sq₀ hleft hright).mp
      rw [Real.sq_sqrt hrad]
      field_simp [ne_of_gt hnR, ne_of_gt hkR] at hηsq
      nlinarith
