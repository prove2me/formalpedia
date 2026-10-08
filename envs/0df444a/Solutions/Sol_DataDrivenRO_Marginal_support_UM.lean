-- Prove2me | solution 1 for DataDrivenRO.Marginal.support_UM
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:35:40.324284+00:00
-- url     : https://prove2.me/submissions/818550cc-5a86-4bba-ab91-9592a5d2e5a6

import Mathlib
import Definitions.Def_DataDrivenRO_Marginal_Setting

open MeasureTheory

namespace DataDrivenRO.Marginal.P53840060

theorem box_support {d : ℕ} (a b : Fin d → ℝ) (hab : ∀ i, a i ≤ b i) (v : Fin d → ℝ) :
    sSup ((fun p : Fin d → ℝ => ∑ j, p j * v j) '' {u | ∀ i, a i ≤ u i ∧ u i ≤ b i}) =
      ∑ i, max (v i * a i) (v i * b i) := by
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨fun i => if 0 ≤ v i then b i else a i, ?_, ?_⟩
    · intro i
      have := hab i
      show a i ≤ (if 0 ≤ v i then b i else a i) ∧ (if 0 ≤ v i then b i else a i) ≤ b i
      split_ifs <;> constructor <;> linarith
    · simp only
      apply Finset.sum_congr rfl
      intro i _
      have := hab i
      split_ifs with h
      · rw [max_eq_right (by nlinarith)]; ring
      · rw [max_eq_left (by nlinarith)]; ring
  · rintro x ⟨u, hu, rfl⟩
    simp only
    apply Finset.sum_le_sum
    intro i _
    obtain ⟨h1, h2⟩ := hu i
    rcases le_or_gt 0 (v i) with h | h
    · exact le_trans (by nlinarith) (le_max_right _ _)
    · exact le_trans (by nlinarith) (le_max_left _ _)

theorem uhat_mono {d N : ℕ} (S : Fin N → Fin d → ℝ) (lo hi : Fin d → ℝ) (hlohi : lo ≤ hi)
    (i : Fin d) (a b : ℕ) (hab : a < b) (hsum : a + b = N + 1 ∨ (a = 0 ∧ N + 1 ≤ b)) :
    uhat S lo hi i a ≤ uhat S lo hi i b := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    have hb : N < b := by omega
    simp [uhat, hb, show b ≠ 0 by omega]
    exact hlohi i
  · have hb : ¬ N < b := by omega
    have ha' : ¬ N < a := by omega
    simp only [uhat, dif_neg (show a ≠ 0 by omega), dif_neg (show b ≠ 0 by omega), dif_neg hb,
      dif_neg ha']
    apply Tuple.monotone_sort
    show a - 1 ≤ b - 1
    omega

end DataDrivenRO.Marginal.P53840060

open MeasureTheory in
open DataDrivenRO.Marginal in
theorem solution {d N : ℕ} (hd : 0 < d) (ε α : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hα0 : 0 < α) (hα1 : α < 1) (lo hi : Fin d → ℝ) (hlohi : lo ≤ hi)
    (hs : N + 1 - sIndex N d ε α < sIndex N d ε α) (S : Fin N → Fin d → ℝ) (v : Fin d → ℝ) :
    RobustMDP.Shared.supportFunction (UM S lo hi ε α) v =
      ∑ i, max (v i * uhat S lo hi i (N + 1 - sIndex N d ε α))
        (v i * uhat S lo hi i (sIndex N d ε α)) := by
  unfold RobustMDP.Shared.supportFunction UM
  apply DataDrivenRO.Marginal.P53840060.box_support
  intro i
  apply DataDrivenRO.Marginal.P53840060.uhat_mono S lo hi hlohi i _ _ hs
  omega
