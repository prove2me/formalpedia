-- Prove2me | solution 1 for BookProof.SirkBandLedger.nestedBands_of_wf
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-12T13:37:23.011923+00:00
-- url     : https://prove2.me/submissions/f4954bfa-2694-4d70-999a-28a04cf81de2

import Mathlib
import Definitions.Def_ChapterSirkBandLedger
open BookProof.SirkBandLedger
open BookProof.BandEnclosure
open BookProof.SirkCertificateReader

theorem solution {L : List BandRecord} (h : LedgerWf L) :
    NestedBands (ledgerLo L) (ledgerHi L) := by
  have leB_toQ {d e : Decimal} (hle : Decimal.leB d e) : d.toQ ≤ e.toQ := by
    unfold Decimal.leB Decimal.toQ at *
    have h10 : (0 : ℚ) < (10 : ℚ) := by norm_num
    rw [div_le_div_iff₀ (pow_pos h10 _) (pow_pos h10 _)]
    exact_mod_cast hle
  have hne : L ≠ [] := by
    have hwf : ledgerWfB L = true := h
    simp [ledgerWfB, Bool.and_eq_true] at hwf
    exact hwf.1.1.1.1
  have stabilize (k : ℕ) (hk : L.length ≤ k + 1) :
      recAt L (k + 1) = recAt L k := by
    unfold recAt
    match L, hne with
    | [], hbot => exact (hbot rfl).elim
    | a :: t, _ =>
      have ht : t.length ≤ k := Nat.succ_le_succ_iff.mp (by simpa using hk)
      simp [Nat.min_eq_right ht, Nat.min_eq_right (le_trans ht (Nat.le_succ k))]
  have rec_get {k : ℕ} (hk : k < L.length) :
      recAt L k = L.getD k default := by
    unfold recAt
    have hle : k ≤ L.length - 1 := by
      simpa [Nat.pred_eq_sub_one] using Nat.le_pred_of_lt hk
    rw [Nat.min_eq_left hle]
  intro m
  refine Set.Icc_subset_Icc ?hlo ?hhi
  · unfold ledgerLo loQ
    by_cases hlen : m + 1 < L.length
    · have hwf : ledgerWfB L = true := h
      simp [ledgerWfB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
        List.mem_range] at hwf
      rcases hwf with ⟨⟨⟨⟨_hne', _hop⟩, _hord⟩, hmesh⟩, _hencl⟩
      have hm : m < L.length - 1 := Nat.lt_sub_of_add_lt hlen
      have hmono := (hmesh m hm).1
      have : (recAt L m).lo.toQ ≤ (recAt L (m + 1)).lo.toQ := by
        rw [rec_get (Nat.lt_of_succ_lt hlen), rec_get hlen]
        exact leB_toQ (by simpa [List.getD_eq_getElem?_getD] using hmono)
      exact_mod_cast this
    · simp [stabilize m (le_of_not_gt hlen)]
  · unfold ledgerHi hiQ
    by_cases hlen : m + 1 < L.length
    · have hwf : ledgerWfB L = true := h
      simp [ledgerWfB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
        List.mem_range] at hwf
      rcases hwf with ⟨⟨⟨⟨_hne', _hop⟩, _hord⟩, hmesh⟩, _hencl⟩
      have hm : m < L.length - 1 := Nat.lt_sub_of_add_lt hlen
      have hmono := (hmesh m hm).2
      have : (recAt L (m + 1)).hi.toQ ≤ (recAt L m).hi.toQ := by
        rw [rec_get (Nat.lt_of_succ_lt hlen), rec_get hlen]
        exact leB_toQ (by simpa [List.getD_eq_getElem?_getD] using hmono)
      exact_mod_cast this
    · simp [stabilize m (le_of_not_gt hlen)]
