-- Prove2me | solution 1 for Egrs75.MuFinish.align_finish_mu
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:43:11.77218+00:00
-- url     : https://prove2.me/submissions/fe680a41-ea93-4414-9f0d-f8936391f3c4

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
public import Theorems.Thm_Egrs75_MuFinish_egrs_move
public import Theorems.Thm_Egrs75_MuFinish_align_mu
public import Theorems.Thm_Egrs75_LeafInduction_badCountQ_eq_zero_iff_lowDigits
public import Theorems.Thm_Egrs75_LeafInduction_seed_lowDigits_pow
public import Theorems.Thm_Egrs75_MoveDigits_div_mul_pow_mono
public import Theorems.Thm_Egrs75_MoveDigits_topBad_lt_of_good_from
public import Theorems.Thm_Egrs75_SeedWindow_seed_window


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
theorem _root_.solution {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) :
    ∀ N, ∃ n, N < n ∧ LowDigits p n ∧ LowDigits q n := by
  intro N
  have hp3 : 3 ≤ p := by have h2 := hp.two_le; rcases hpo with ⟨c, hc⟩; omega
  have hq3 : 3 ≤ q := by have h2 := hq.two_le; rcases hqo with ⟨c, hc⟩; omega
  have hq1 : 1 < q := by omega
  have hBq1 : 1 ≤ (q - 1) / 2 := by omega
  -- the Diophantine seed
  obtain ⟨α, e, hα1, hF, hlo, hhi⟩ := SeedWindow.seed_window hp hq hq3 hpq N
  have hsp : LowDigits p (p ^ α) := seed_lowDigits_pow hp3 α
  -- seed magnitude
  have hBmul : q ^ (e + 3) ≤ (q - 1) / 2 * q ^ (e + 3) := by
    have h := Nat.mul_le_mul_right (q ^ (e + 3)) hBq1
    omega
  have hsN : N < p ^ α := by omega
  -- seed digit structure
  have hpow13 : q ^ (e + 1) ≤ q ^ (e + 3) := Nat.pow_le_pow_right (by omega) (by omega)
  have hpow12 : q ^ (e + 1) ≤ q ^ (e + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hupper : p ^ α < ((q - 1) / 2 + 1) * q ^ (e + 3) := by
    have hexp : ((q - 1) / 2 + 1) * q ^ (e + 3)
        = (q - 1) / 2 * q ^ (e + 3) + q ^ (e + 3) := by ring
    omega
  have hdiv3 : p ^ α / q ^ (e + 3) = (q - 1) / 2 :=
    Nat.div_eq_of_lt_le (le_of_lt hlo) hupper
  have hsplit23 : q ^ (e + 3) = q ^ (e + 2) * q := pow_succ q (e + 2)
  have hdiv2 : p ^ α / q ^ (e + 2) = (q - 1) / 2 * q := by
    apply Nat.div_eq_of_lt_le
    · have hexp2 : (q - 1) / 2 * q * q ^ (e + 2) = (q - 1) / 2 * q ^ (e + 3) := by
        rw [hsplit23]; ring
      omega
    · have hexp3 : ((q - 1) / 2 * q + 1) * q ^ (e + 2)
          = (q - 1) / 2 * q ^ (e + 3) + q ^ (e + 2) := by
        rw [hsplit23]; ring
      omega
  have hsmall : p ^ α < q ^ (e + 4) := by
    have h1 : ((q - 1) / 2 + 1) * q ^ (e + 3) ≤ q * q ^ (e + 3) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : q ^ (e + 4) = q ^ (e + 3) * q := pow_succ q (e + 3)
    have h3 : q * q ^ (e + 3) = q ^ (e + 3) * q := Nat.mul_comm _ _
    omega
  have hgood2 : ∀ idx, e + 2 ≤ idx → p ^ α / q ^ idx % q ≤ (q - 1) / 2 := by
    intro idx hidx
    rcases Nat.lt_or_ge idx (e + 3) with h2 | h3
    · -- idx = e + 2
      have heq2 : idx = e + 2 := by omega
      simp_all
    · rcases Nat.lt_or_ge idx (e + 4) with h4 | h5
      · -- idx = e + 3
        have heq3 : idx = e + 3 := by omega
        subst heq3
        rw [hdiv3, Nat.mod_eq_of_lt (by omega : (q - 1) / 2 < q)]
      · -- idx ≥ e + 4: digit 0
        have hz : p ^ α / q ^ idx = 0 := by
          apply Nat.div_eq_of_lt
          calc p ^ α < q ^ (e + 4) := hsmall
            _ ≤ q ^ idx := Nat.pow_le_pow_right (by omega) h5
        rw [hz]
        simp_all
  rcases Nat.eq_zero_or_pos (badCountQ q (p ^ α)) with hz | hbads
  · -- the seed is already fully good
    exact ⟨p ^ α, hsN, hsp, badCountQ_eq_zero_iff_lowDigits.mp hz⟩
  · -- run the μ-machine from the seed
    have htb : topBadIndex q (p ^ α) < e + 2 :=
      MoveDigits.topBad_lt_of_good_from hq1 hbads hgood2
    have hsg : StrictGoodAt q (e + 2) (p ^ α) := by
      unfold StrictGoodAt
      rw [hdiv2, Nat.mul_mod_left]
      omega
    have hple : leastGoodAbove hq3 hbads ≤ e + 2 := Nat.find_min' _ ⟨htb, hsg⟩
    have hsfl : ∀ (hbad : 0 < badCountQ q (p ^ α)),
        N < p ^ α / q ^ (leastGoodAbove hq3 hbad) * q ^ (leastGoodAbove hq3 hbad) := by
      intro hbad
      have hBe : (q - 1) / 2 * q ^ (e + 3) = (q - 1) / 2 * q * q ^ (e + 2) := by
        rw [hsplit23]; ring
      calc N < q ^ (e + 3) := hF
        _ ≤ (q - 1) / 2 * q ^ (e + 3) := hBmul
        _ = (q - 1) / 2 * q * q ^ (e + 2) := hBe
        _ = p ^ α / q ^ (e + 2) * q ^ (e + 2) := by rw [hdiv2]
        _ ≤ p ^ α / q ^ (leastGoodAbove hq3 hbad) * q ^ (leastGoodAbove hq3 hbad) :=
            MoveDigits.div_mul_pow_mono (by omega) _ hple
    exact align_mu hq3 N
      (fun {m'} hpm hbad' hfl' => egrs_move hp hq hpo hqo hpq hq3 N hpm hbad' hfl')
      (p ^ α) hsN hsp hsfl
end Egrs75.MuFinish
