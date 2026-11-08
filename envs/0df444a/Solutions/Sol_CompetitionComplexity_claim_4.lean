-- Prove2me | solution 1 for CompetitionComplexity.claim_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:36:14.323683+00:00
-- url     : https://prove2.me/submissions/74fb164d-70f4-450a-8673-fa902195f54b

import Mathlib
import Definitions.Def_CompetitionComplexity_Recursion

namespace Aux_CCc4

open CompetitionComplexity

theorem rho_succ (ε : ℝ) (n i : ℕ) (hi : 1 ≤ i) :
    rho ε n (i + 1) = ((((n : ℝ) - 1) * rho ε n i ^ n - ε) / n) ^ (1 / ((n : ℝ) - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rfl

end Aux_CCc4

open CompetitionComplexity Aux_CCc4 in
theorem solution (n : ℕ) (hn : 2 ≤ n) (ε ε' : ℝ) (hε' : 0 < ε') (hle : ε' ≤ ε) (j : ℕ)
    (hw : WellDef ε n j) :
    WellDef ε' n j ∧ rho ε n j ≤ rho ε' n j := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hexp : (0 : ℝ) ≤ 1 / ((n : ℝ) - 1) := by positivity
  have key : ∀ i, 1 ≤ i → i ≤ j → 0 ≤ rho ε n i ∧ rho ε n i ≤ rho ε' n i := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base => intro _; simp [rho]
    | succ i hi ih =>
      intro hij
      obtain ⟨h0, hle'⟩ := ih (by omega)
      have hb : 0 < ((n : ℝ) - 1) * rho ε n i ^ n - ε := by
        have := hw.2 (i + 1) (by omega) hij
        simpa using this
      have hpow : rho ε n i ^ n ≤ rho ε' n i ^ n := pow_le_pow_left₀ h0 hle' n
      have hb' : ((n : ℝ) - 1) * rho ε n i ^ n - ε ≤ ((n : ℝ) - 1) * rho ε' n i ^ n - ε' := by
        nlinarith
      rw [rho_succ ε n i hi, rho_succ ε' n i hi]
      have hnpos : (0 : ℝ) < n := by linarith
      constructor
      · exact Real.rpow_nonneg (by positivity) _
      · apply Real.rpow_le_rpow (by positivity) _ hexp
        exact div_le_div_of_nonneg_right hb' hnpos.le
  refine ⟨⟨hw.1, fun i hi2 hij => ?_⟩, (key j hw.1 le_rfl).2⟩
  obtain ⟨h0, hle'⟩ := key (i - 1) (by omega) (by omega)
  have hb := hw.2 i hi2 hij
  have hpow : rho ε n (i - 1) ^ n ≤ rho ε' n (i - 1) ^ n := pow_le_pow_left₀ h0 hle' n
  nlinarith
