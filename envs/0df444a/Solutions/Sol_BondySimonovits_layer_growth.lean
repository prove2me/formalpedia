-- Prove2me | solution 1 for BondySimonovits.layer_growth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:09:46.461484+00:00
-- url     : https://prove2.me/submissions/19211fb7-3264-4136-ada1-014cb868062c

module
public import Definitions.Def_BondySimonovitsLib_BSCycle
public import Definitions.Def_BondySimonovitsLib_BSGrowth

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
namespace BondySimonovits
theorem _root_.solution (a : ℕ → ℕ) (k d D : ℕ) (hD : 0 < D) (hdD : 4 * D ≤ d) (h0 : a 0 ≤ 1)
    (h1 : d ≤ a 1)
    (hrec : ∀ i, 1 ≤ i → i + 1 ≤ k → d * a i ≤ D * (a (i - 1) + a i) + D * (a i + a (i + 1))) :
    ∀ i, 1 ≤ i → i ≤ k → ((d : ℝ) / D - 3) ^ i ≤ a i ∧ a (i - 1) ≤ a i := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hr1 : (1 : ℝ) ≤ (d : ℝ) / D - 3 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hDr]
    have : (4 * D : ℝ) ≤ d := by exact_mod_cast hdD
    linarith
  intro i hi
  induction i, hi using Nat.le_induction with
  | base =>
    intro _
    refine ⟨?_, ?_⟩
    · rw [pow_one]
      have : (d : ℝ) / D ≤ d := div_le_self (by positivity) (by exact_mod_cast hD)
      have : (d : ℝ) ≤ a 1 := by exact_mod_cast h1
      linarith
    · simp only [Nat.sub_self]; omega
  | succ i hi ih =>
    intro hik
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hr := hrec i hi hik
    have key : (D : ℝ) * a (i + 1) ≥ (d - 3 * D) * a i := by
      have h2 : (a (i - 1) : ℝ) ≤ a i := by exact_mod_cast ih2
      have h3 : (d : ℝ) * a i ≤ D * (a (i - 1) + a i) + D * (a i + a (i + 1)) := by
        exact_mod_cast hr
      nlinarith
    have key2 : ((d : ℝ) / D - 3) * a i ≤ a (i + 1) := by
      rw [sub_mul, div_mul_eq_mul_div, div_sub' (ne_of_gt hDr), div_le_iff₀ hDr]
      linarith
    have hai : (0 : ℝ) ≤ a i := by positivity
    refine ⟨?_, ?_⟩
    · rw [pow_succ]
      calc ((d : ℝ) / D - 3) ^ i * ((d : ℝ) / D - 3) ≤ a i * ((d : ℝ) / D - 3) :=
            mul_le_mul_of_nonneg_right ih1 (by linarith)
        _ = ((d : ℝ) / D - 3) * a i := mul_comm _ _
        _ ≤ a (i + 1) := key2
    · simp only [Nat.add_sub_cancel]
      have : (a i : ℝ) ≤ a (i + 1) := by nlinarith
      exact_mod_cast this
end BondySimonovits
