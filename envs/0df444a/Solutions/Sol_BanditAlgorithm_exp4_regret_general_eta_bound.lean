-- Prove2me | solution 1 for BanditAlgorithm.exp4_regret_general_eta_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T00:00:03.428503+00:00
-- url     : https://prove2.me/submissions/16d80315-6196-4d92-8674-34ee4e3930aa

import Theorems.Thm_BanditAlgorithm_exp4_estimate_unbiased
import Theorems.Thm_BanditAlgorithm_exp4_estimate_advantage_bound

open MeasureTheory ProbabilityTheory

open BanditAlgorithm

/-!
Lattimore--Szepesvári, *Bandit Algorithms*, Theorem 18.1 proof, printed
p. 230.  Equation (18.10) identifies every expert's estimated score with its
true reward in expectation.  Equations (18.11)--(18.12) bound the estimated
advantage for each expert.  The remaining argument is the formal bridge that
takes the supremum over experts in the definition of Exp4 regret.
-/

theorem solution
    {k M : ℕ} (hk : 0 < k) (hM : 1 < M) (n : ℕ) (hn : 0 < n)
    (η : ℝ) (hη : 0 < η)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ a : Fin k, x t a ∈ Set.Icc (0 : ℝ) 1)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (π : BanditPolicy k)
    (hπ : IsExp4Policy η 0 E π) :
    exp4Regret n x E π ≤
      Real.log M / η + η * ((n : ℝ) * k) / 2 := by
  letI : Nonempty (Fin M) := ⟨⟨0, by omega⟩⟩
  rw [exp4Regret]
  rw [sub_le_iff_le_add]
  apply ciSup_le
  intro m
  have hbound :=
    exp4_estimate_advantage_bound hk hM n hn η hη x hx E hE0 hE1 π hπ m
  rw [exp4_estimate_unbiased hk hM n hn η hη x hx E hE0 hE1 π hπ m] at hbound
  linarith
