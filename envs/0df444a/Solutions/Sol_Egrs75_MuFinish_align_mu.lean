-- Prove2me | solution 1 for Egrs75.MuFinish.align_mu
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:44.583534+00:00
-- url     : https://prove2.me/submissions/cd0b7201-cf7c-4f98-9b3d-4cdc1cc767de

module
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Definitions.Def_LeanPool_Egrs75_ConditionThreeWindow
public import Definitions.Def_LeanPool_Egrs75_AddBranch
public import Definitions.Def_LeanPool_Egrs75_MoveDigits
public import Definitions.Def_LeanPool_Egrs75_Reduction
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_SeedWindow
public import Definitions.Def_LeanPool_Egrs75_SubtractBranch
public import Mathlib.Data.Nat.Totient
public import Definitions.Def_LeanPool_Egrs75_MuFinish
public import Theorems.Thm_Egrs75_LeafInduction_badCountQ_eq_zero_iff_lowDigits
public import Theorems.Thm_Egrs75_MoveDigits_div_mul_pow_mono


set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.MuFinish
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
open Egrs75.P4
namespace Egrs75.MuFinish
theorem _root_.solution {p q : ℕ} (hq3 : 3 ≤ q) (N : ℕ)
    (hmove : ∀ {n : ℕ}, LowDigits p n → ∀ (hbad : 0 < badCountQ q n),
        N < n / q ^ (leastGoodAbove hq3 hbad) * q ^ (leastGoodAbove hq3 hbad) →
        ∃ n', LowDigits p n' ∧
          N < n' / q ^ (leastGoodAbove hq3 hbad) * q ^ (leastGoodAbove hq3 hbad) ∧
          (muVal q hq3 n' < muVal q hq3 n ∨
            (muVal q hq3 n' = muVal q hq3 n ∧ n' < n)))
    (seed : ℕ) (hsN : N < seed) (hsp : LowDigits p seed)
    (hsfl : ∀ (hbad : 0 < badCountQ q seed),
        N < seed / q ^ (leastGoodAbove hq3 hbad) * q ^ (leastGoodAbove hq3 hbad)) :
    ∃ n, N < n ∧ LowDigits p n ∧ LowDigits q n := by
  suffices H : ∀ k n, muVal q hq3 n = k → LowDigits p n → N < n →
      (∀ (hbad : 0 < badCountQ q n),
        N < n / q ^ (leastGoodAbove hq3 hbad) * q ^ (leastGoodAbove hq3 hbad)) →
      ∃ m, N < m ∧ LowDigits p m ∧ LowDigits q m by
    exact H _ seed rfl hsp hsN hsfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
      intro hk hpn hNn hfl
      rcases Nat.eq_zero_or_pos (badCountQ q n) with hz | hbad
      · exact ⟨n, hNn, hpn, badCountQ_eq_zero_iff_lowDigits.mp hz⟩
      obtain ⟨n', hpn', hfl', hdrop⟩ := hmove hpn hbad (hfl hbad)
      have hNn' : N < n' := lt_of_lt_of_le hfl' (Nat.div_mul_le_self _ _)
      have hfl'' : ∀ (hbad' : 0 < badCountQ q n'),
          N < n' / q ^ (leastGoodAbove hq3 hbad') * q ^ (leastGoodAbove hq3 hbad') := by
        intro hbad'
        have hmle : muVal q hq3 n' ≤ muVal q hq3 n := by
          rcases hdrop with h | ⟨h, _⟩
          · exact le_of_lt h
          · exact le_of_eq h
        have hile : leastGoodAbove hq3 hbad' ≤ leastGoodAbove hq3 hbad := by
          by_contra hcon
          push Not at hcon
          have h1 : muVal q hq3 n' = leastGoodAbove hq3 hbad' * q
              + ((q - 1) / 2 - n' / q ^ (leastGoodAbove hq3 hbad') % q) := by
            simp only [muVal, dif_pos hbad']
          have h2 : muVal q hq3 n = leastGoodAbove hq3 hbad * q
              + ((q - 1) / 2 - n / q ^ (leastGoodAbove hq3 hbad) % q) := by
            simp only [muVal, dif_pos hbad]
          have h3 : (leastGoodAbove hq3 hbad + 1) * q ≤ leastGoodAbove hq3 hbad' * q :=
            Nat.mul_le_mul_right _ (by omega)
          have h4 : (leastGoodAbove hq3 hbad + 1) * q
              = leastGoodAbove hq3 hbad * q + q := by ring
          have h5 : (q - 1) / 2 - n / q ^ (leastGoodAbove hq3 hbad) % q < q := by omega
          omega
        exact lt_of_lt_of_le hfl'
          (MoveDigits.div_mul_pow_mono (by omega) n' hile)
      rcases hdrop with hlt | ⟨heq, hltn⟩
      · exact ihk (muVal q hq3 n') (by omega) n' rfl hpn' hNn' hfl''
      · exact ihn n' hltn (by omega) hpn' hNn' hfl''
end Egrs75.MuFinish
