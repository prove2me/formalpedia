-- Prove2me | solution 1 for Egrs75.MuFinish.egrs_move
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:42:06.76118+00:00
-- url     : https://prove2.me/submissions/64244c2c-1a9c-4294-9d33-855dc5e00fad

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
public import Theorems.Thm_Egrs75_MuFinish_muVal_lt_of
public import Theorems.Thm_Egrs75_ClearingP2_add_U_lowDigits_p
public import Theorems.Thm_Egrs75_ClearingP3_mod_pow_lowPDigitIndex
public import Theorems.Thm_Egrs75_ClearingP3_sub_div_pow_eq
public import Theorems.Thm_Egrs75_ClearingP3_sub_high_digits_frozen
public import Theorems.Thm_Egrs75_ClearingP3_sub_preserves_lowDigits
public import Theorems.Thm_Egrs75_MoveDigits_add_digit_i
public import Theorems.Thm_Egrs75_MoveDigits_add_div_pow_eq
public import Theorems.Thm_Egrs75_MoveDigits_add_high_frozen
public import Theorems.Thm_Egrs75_MoveDigits_add_low_digit
public import Theorems.Thm_Egrs75_MoveDigits_staircase
public import Theorems.Thm_Egrs75_MoveDigits_topBad_lt_of_good_from
public import Theorems.Thm_Egrs75_P4_cond3_of_tail_small
public import Theorems.Thm_Egrs75_P4_geomQ_mul
public import Theorems.Thm_Egrs75_P4_strictGoodAt_leastGoodAbove
public import Theorems.Thm_Egrs75_P4_tail_ge
public import Theorems.Thm_Egrs75_P4_topBad_lt_leastGoodAbove
public import Theorems.Thm_Egrs75_RepairDV_digit_good_above_top
public import Theorems.Thm_Egrs75_RoundUp_exists_lowDigits_between


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
theorem _root_.solution {p q : ℕ} (hp : p.Prime) (_hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (_hpq : p ≠ q) (hq3 : 3 ≤ q) (N : ℕ)
    {n : ℕ} (hpn : LowDigits p n) (hbad : 0 < badCountQ q n)
    (hfloor : N < n / q ^ (leastGoodAbove hq3 hbad) * q ^ (leastGoodAbove hq3 hbad)) :
    ∃ n', LowDigits p n' ∧
      N < n' / q ^ (leastGoodAbove hq3 hbad) * q ^ (leastGoodAbove hq3 hbad) ∧
      (muVal q hq3 n' < muVal q hq3 n ∨
        (muVal q hq3 n' = muVal q hq3 n ∧ n' < n)) := by
  have hq1 : 1 < q := by omega
  have hp3 : 3 ≤ p := by have h2 := hp.two_le; rcases hpo with ⟨c, hc⟩; omega
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp [badCountQ, badDigitsQ] at hbad
  set i := leastGoodAbove hq3 hbad with hidef
  set m := ClearingP3.lowPDigitIndex p n with hmdef
  set T := n % q ^ i with hTdef
  set S := (p ^ m + 1) / 2 with hSdef
  have hji : topBadIndex q n < i := topBad_lt_leastGoodAbove hq3 hbad
  have hi1 : 1 ≤ i := by omega
  have hbi : n / q ^ i % q < (q - 1) / 2 := strictGoodAt_leastGoodAbove hq3 hbad
  have hqipos : 0 < q ^ i := pow_pos (by omega) i
  have hTlt : T < q ^ i := by rw [hTdef]; exact Nat.mod_lt _ hqipos
  have htail : (q - 1) / 2 * geomQ q i + 1 ≤ T := by
    rw [hTdef, hidef]; exact tail_ge hq3 hbad
  have hB2 : 2 * ((q - 1) / 2) = q - 1 := by obtain ⟨c, hc⟩ := hqo; omega
  have hgold : (q - 1) * geomQ q i = q ^ i - 1 := geomQ_mul (by omega) i
  have hqi1 : 1 ≤ q ^ i := Nat.one_le_pow _ _ (by omega)
  have hT2 : q ^ i + 1 ≤ 2 * T := by
    have h2 : 2 * ((q - 1) / 2 * geomQ q i) = (q - 1) * geomQ q i := by
      calc 2 * ((q - 1) / 2 * geomQ q i)
          = 2 * ((q - 1) / 2) * geomQ q i := by ring
        _ = (q - 1) * geomQ q i := by rw [hB2]
    omega
  have hmun : muVal q hq3 n = i * q + ((q - 1) / 2 - n / q ^ i % q) := by
    simp only [muVal, dif_pos hbad, ← hidef]
  have hq_le_iq : q ≤ i * q := by
    calc q = 1 * q := (one_mul q).symm
      _ ≤ i * q := Nat.mul_le_mul_right _ hi1
  rcases Nat.lt_or_ge T S with hTS | hST
  · -- ════════════ ADD branch (T < S; condition (3) fires) ════════════
    have hTS' : T < (p ^ m + 1) / 2 := by omega
    have hcond3 : q ^ i < p ^ m :=
      cond3_of_tail_small hq3 hpo hqo m i T htail hTS'
    have hx1 : 1 ≤ q ^ i - T := by omega
    obtain ⟨U, hUlo, hUhi, hUlow⟩ :=
      RoundUp.exists_lowDigits_between hp3 hpo (q ^ i - T) hx1
    have hUp : U < p ^ m := by omega
    have hmod : n % p ^ m = 0 := by
      rw [hmdef]; exact ClearingP3.mod_pow_lowPDigitIndex (by omega) hn0
    have hpn' : LowDigits p (n + U) :=
      ClearingP2.add_U_lowDigits_p (by omega) hpn hUlow hUp hmod (by omega)
    have hclo : q ^ i ≤ n % q ^ i + U := by omega
    have hchi : n % q ^ i + U < 2 * q ^ i := by omega
    have hdiv_i : (n + U) / q ^ i = n / q ^ i + 1 :=
      MoveDigits.add_div_pow_eq hq1 n U i hclo hchi
    have hfl' : N < (n + U) / q ^ i * q ^ i := by
      rw [hdiv_i]
      have hmono : n / q ^ i * q ^ i ≤ (n / q ^ i + 1) * q ^ i :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    refine ⟨n + U, hpn', hfl', ?_⟩
    rcases Nat.eq_zero_or_pos (badCountQ q (n + U)) with hz | hbad'
    · -- terminal: fully good, μ' = 0 < μ
      left
      have hmu0 : muVal q hq3 (n + U) = 0 := by
        simp only [muVal, dif_neg (by omega : ¬ 0 < badCountQ q (n + U))]
      omega
    · -- the staircase: the working index drops strictly
      left
      have hRst : 2 * (n % q ^ i + U - q ^ i) + 3 ≤ q ^ i := by omega
      obtain ⟨k, hki, hkstrict, hkbet⟩ :=
        MoveDigits.staircase hq3 hqo i (n % q ^ i + U - q ^ i) hRst
      have hlow : ∀ t, t < i →
          (n + U) / q ^ t % q = (n % q ^ i + U - q ^ i) / q ^ t % q :=
        fun t ht => MoveDigits.add_low_digit hq1 n U i t ht hclo
      have hbiq : n / q ^ i % q < q - 1 := by omega
      have hdig_i : (n + U) / q ^ i % q = n / q ^ i % q + 1 :=
        MoveDigits.add_digit_i hq1 n U i hclo hchi hbiq
      have hhigh : ∀ idx, i < idx → (n + U) / q ^ idx % q = n / q ^ idx % q :=
        fun idx hidx => MoveDigits.add_high_frozen hq1 n U i idx hclo hchi hbiq hidx
      have hgoodk : ∀ idx, k ≤ idx → (n + U) / q ^ idx % q ≤ (q - 1) / 2 := by
        intro idx hidx
        rcases Nat.lt_trichotomy idx i with hlt | heqi | hgt
        · rcases Nat.eq_or_lt_of_le hidx with heqk | hgtk
          · rw [hlow idx hlt, ← heqk]
            exact le_of_lt hkstrict
          · rw [hlow idx hlt, hkbet idx hgtk hlt]
        · simp_all
        · rw [hhigh idx hgt]
          exact digit_good_above_top hq1 hbad (by omega)
      have htb' : topBadIndex q (n + U) < k :=
        MoveDigits.topBad_lt_of_good_from hq1 hbad' hgoodk
      have hsgk : StrictGoodAt q k (n + U) := by
        unfold StrictGoodAt
        rw [hlow k hki]; exact hkstrict
      have hi'le : leastGoodAbove hq3 hbad' ≤ k := Nat.find_min' _ ⟨htb', hsgk⟩
      exact muVal_lt_of hq3 hbad (Or.inr ⟨hbad', Or.inl (by omega)⟩)
  · -- ════════════ SUBTRACT branch (S ≤ T; tail strip, block frozen) ════════════
    have hppos : 1 ≤ p ^ m := Nat.one_le_pow _ _ (by omega)
    have hSpos : 1 ≤ S := by omega
    have hTn : T ≤ n := by rw [hTdef]; exact Nat.mod_le _ _
    have hlt_n : n - S < n := by omega
    have hST' : S ≤ n % q ^ i := by omega
    have hpn' : LowDigits p (n - S) := by
      rw [hSdef, hmdef]
      exact ClearingP3.sub_preserves_lowDigits hp hpo hpn hn0
    have hfrozen : ∀ idx, i ≤ idx → (n - S) / q ^ idx % q = n / q ^ idx % q :=
      fun idx hidx => ClearingP3.sub_high_digits_frozen (by omega) hST' hidx
    have hdivfr : (n - S) / q ^ i = n / q ^ i :=
      ClearingP3.sub_div_pow_eq (by omega) hST'
    have hfl' : N < (n - S) / q ^ i * q ^ i := by rw [hdivfr]; exact hfloor
    refine ⟨n - S, hpn', hfl', ?_⟩
    rcases Nat.eq_zero_or_pos (badCountQ q (n - S)) with hz | hbad'
    · left
      have hmu0 : muVal q hq3 (n - S) = 0 := by
        simp only [muVal, dif_neg (by omega : ¬ 0 < badCountQ q (n - S))]
      omega
    · have hgoodi : ∀ idx, i ≤ idx → (n - S) / q ^ idx % q ≤ (q - 1) / 2 := by
        intro idx hidx
        rw [hfrozen idx hidx]
        rcases Nat.eq_or_lt_of_le hidx with heqi | hgti
        · rw [← heqi]; exact le_of_lt hbi
        · exact digit_good_above_top hq1 hbad (by omega)
      have htb' : topBadIndex q (n - S) < i :=
        MoveDigits.topBad_lt_of_good_from hq1 hbad' hgoodi
      have hsgi : StrictGoodAt q i (n - S) := by
        unfold StrictGoodAt
        rwa [hfrozen i (le_refl i)]
      have hi'le : leastGoodAbove hq3 hbad' ≤ i := Nat.find_min' _ ⟨htb', hsgi⟩
      rcases Nat.eq_or_lt_of_le hi'le with heq' | hlt'
      · -- index and digit frozen: μ unchanged, n strictly drops
        right
        refine ⟨?_, hlt_n⟩
        have h1 : muVal q hq3 (n - S)
            = leastGoodAbove hq3 hbad' * q
              + ((q - 1) / 2 - (n - S) / q ^ (leastGoodAbove hq3 hbad') % q) := by
          simp only [muVal, dif_pos hbad']
        simp_all
      · -- index dropped: μ strictly drops
        left
        exact muVal_lt_of hq3 hbad (Or.inr ⟨hbad', Or.inl (by omega)⟩)
end Egrs75.MuFinish
