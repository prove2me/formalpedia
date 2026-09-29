-- Prove2me | solution 1 for BanditAlgorithm.mdp_optimal_gain_le_of_bellman_ineq
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-02T04:34:10.241867+00:00
-- url     : https://prove2.me/submissions/897d0b66-ca3b-458d-82e0-2e39c30bb493

import Theorems.Thm_BanditAlgorithm_mdp_expected_reward_le_of_bellman_ineq

open MeasureTheory ProbabilityTheory Finset BanditAlgorithm

/-!
Dividing the finite-horizon bound `E[∑_{t≤n} r] ≤ n ρ + span(v)` by `n` and
letting `n → ∞` kills the span, so every policy has gain at most `ρ` from every
starting state; the optimal gain `ρ*` is the supremum of those gains.
-/

variable {S A : ℕ}

/-- The gain of any policy from any state is at most `ρ`. -/
private lemma gain_le (M : FiniteMDP S A) (π : MDPPolicy S A) (ρ : ℝ)
    (v : Fin S → ℝ) (lo hi : ℝ) (hv : ∀ s, v s ∈ Set.Icc lo hi)
    (hbell : ∀ s a, M.r s a + ∑ s', (M.P s a s' : ℝ) * v s' ≤ ρ + v s) (s : Fin S) :
    mdpGain M π s ≤ ρ := by
  set u : ℕ → ℝ := fun n ↦ mdpExpectedReward M (mdpStateDirac s) π n / n with hu
  set w : ℕ → ℝ := fun n ↦ ρ + (hi - lo) / n with hw
  have hle : ∀ᶠ n : ℕ in Filter.atTop, u n ≤ w n := by
    refine Filter.eventually_atTop.mpr ⟨1, fun n hn ↦ ?_⟩
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have := BanditAlgorithm.mdp_expected_reward_le_of_bellman_ineq M (mdpStateDirac s) π ρ v
      lo hi hv hbell n
    rw [hu, hw, div_le_iff₀ hnR]
    field_simp
    linarith
  have hlow : ∀ n : ℕ, 0 ≤ u n := by
    intro n
    have hrew : (0 : ℝ) ≤ mdpExpectedReward M (mdpStateDirac s) π n := by
      rw [mdpExpectedReward]
      refine integral_nonneg fun h ↦ ?_
      exact Finset.sum_nonneg fun t _ ↦ (M.r_mem_Icc (h t).1 (h t).2).1
    exact div_nonneg hrew (Nat.cast_nonneg n)
  have hwlim : Filter.Tendsto w Filter.atTop (nhds ρ) := by
    have : Filter.Tendsto (fun n : ℕ ↦ (hi - lo) / n) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    simpa [hw] using tendsto_const_nhds.add this
  calc mdpGain M π s = Filter.limsup u Filter.atTop := rfl
    _ ≤ Filter.limsup w Filter.atTop :=
        Filter.limsup_le_limsup hle (Filter.isCoboundedUnder_le_of_le _ hlow)
          hwlim.isBoundedUnder_le
    _ = ρ := hwlim.limsup_eq

/-- **Optimism from the Bellman optimality inequality** (Lattimore and
Szepesvári, Theorem 38.2; the direction used at Eq. 38.17 of the UCRL2
analysis).  A pair `(ρ, v)` with `r_a(s) + ⟨P_a(s), v⟩ ≤ ρ + v(s)` for every
state and action bounds the optimal gain of the MDP. -/
theorem solution (hS : 0 < S) (hA : 0 < A)
    (M : FiniteMDP S A) (ρ : ℝ) (v : Fin S → ℝ) (lo hi : ℝ)
    (hv : ∀ s, v s ∈ Set.Icc lo hi)
    (hbell : ∀ s a, M.r s a + ∑ s', (M.P s a s' : ℝ) * v s' ≤ ρ + v s) :
    mdpOptimalGain M ≤ ρ := by
  haveI : Nonempty (Fin S) := Fin.pos_iff_nonempty.mp hS
  haveI : Nonempty (MDPPolicy S A) := ⟨mdpMemorylessDetPolicy fun _ ↦ ⟨0, hA⟩⟩
  exact ciSup_le fun s ↦ ciSup_le fun π ↦ gain_le M π ρ v lo hi hv hbell s
