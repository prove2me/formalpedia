-- Prove2me | solution 1 for BitDFT.staged_low_magnitude_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T02:57:45.957099+00:00
-- url     : https://prove2.me/submissions/7b33fbe4-c60e-49f5-924a-dba65b57f580

import Theorems.Thm_BitDFT_staged_qbit_product
import Theorems.Thm_BitDFT_scalar_scaled_word_complete_v2
import Definitions.Def_IntMul_TrackedBankedCall
import Mathlib.Tactic

set_option autoImplicit false
open IntMul BitDFT
open IntMul.TrackedBankPreparation (inputWord)

namespace BitDFT.StagedLowMagnitudeLemmas
open IntMul

private theorem bin_succ (k z : ℕ) : bin (k+1) z = bin k (z/2) ++ [z.testBit 0] := by
  unfold bin
  rw [List.ofFn_succ', List.concat_eq_append]
  congr 1
  · congr 1
    funext i
    rw [Nat.testBit_div_two]
    congr 1
    simp only [Fin.val_castSucc]
    omega
  · simp

private theorem val_append_bit (w : List Bool) (b : Bool) :
    val (w ++ [b]) = 2*val w + b.toNat := by
  simp [val, List.foldl_append]

private theorem low_bit (z : ℕ) : (z.testBit 0).toNat = z%2 := by
  have h := Nat.mod_lt z (by decide : 0 < 2)
  simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.div_one]
  by_cases hz : z%2 = 1
  · simp [hz]
  · have h0 : z%2 = 0 := by omega
    simp [h0]

theorem val_bin (k z : ℕ) (hz : z < 2^k) : val (bin k z) = z := by
  induction k generalizing z with
  | zero =>
      have h : z = 0 := by simpa using hz
      subst z
      rfl
  | succ k ih =>
      rw [bin_succ, val_append_bit, ih, low_bit]
      · omega
      · have hpow : 2^(k+1) = 2^k*2 := pow_succ _ _
        omega

end BitDFT.StagedLowMagnitudeLemmas

/-- A pre-staged q-bit multiplier call computes the exact scaled value and
its widened output encoding whenever the magnitude is below the boundary. -/
theorem solution (M : MultitapeTM) (T : ℕ → ℝ) (hM : Multiplier M T)
    (q n a : ℕ) (hn : 1 ≤ n) (hq : lg n + 1 ≤ q)
    (hnwide : n ≤ 2^(lg n)) (ha : a < 2^q)
    (base : (TrackedBankedCall.machine M).Cfg)
    (hs : base.state = (TrackedBankedCall.machine M).qStart)
    (hbuf : base.cells (TrackedBankedCall.machine M).outTape =
      (TrackedBankedCall.machine M).tapeOf
        ((TrackedBankedCall.machine M).blank ::
          (inputWord M (bin q n) (bin q a)).map (fun s => some (s, true))))
    (hh : base.head (TrackedBankedCall.machine M).outTape = 1)
    (hwork : ∀ i : Fin (M.k + 2), 2 ≤ i.val →
      base.cells i = (TrackedBankedCall.machine M).tapeOf [] ∧ base.head i = 1) :
    ∃ t tm : ℕ,
      (tm : ℝ) ≤ T q ∧
      (t : ℝ) ≤ 6 * T q + 14 * q + 20 ∧
      (TrackedBankedCall.machine M).step^[t] base =
        TrackedBankedCall.finalFrame M base 1 (fun _ => 1)
          (TrackedBankedSimulation.extents M (M.initCfg (bin q n) (bin q a))
            (TrackedBankPreparation.initialExtent M (bin q n) (bin q a)) tm)
          (M.step^[tm] (M.initCfg (bin q n) (bin q a)))
          (bin (2*q) (n*a)) ∧
      bin (2*q) (n*a) =
        List.replicate (2*q-(q+lg n+1)) false ++ bin (q+lg n+1) (n*a) := by
  have hqpos : 1 ≤ q := by omega
  have hnlt : n < 2^q := by
    have hp : 2^(lg n) < 2^q := Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
    omega
  have hmod : a % 2^q = a := Nat.mod_eq_of_lt ha
  have hnv := BitDFT.StagedLowMagnitudeLemmas.val_bin q n hnlt
  have hav := BitDFT.StagedLowMagnitudeLemmas.val_bin q a ha
  have hx : (bin q n).length = q := by simp [bin]
  have hy : (bin q a).length = q := by simp [bin]
  obtain ⟨t, tm, htm, ht, hr⟩ :=
    BitDFT.staged_qbit_product M T hM q hqpos base (bin q n) (bin q a)
      hx hy hs hbuf hh hwork
  have hscaled := BitDFT.scalar_scaled_word_complete_v2 q n a hq hnwide (Nat.le_of_lt ha)
  rcases hscaled with ⟨hselect, _, hword⟩
  have hbit : a.testBit q = false := Nat.testBit_eq_false_of_lt ha
  have hselect' : n*a = n*a := by simpa [hbit, hmod] using hselect.symm
  have hr' : (TrackedBankedCall.machine M).step^[t] base =
      TrackedBankedCall.finalFrame M base 1 (fun _ => 1)
        (TrackedBankedSimulation.extents M (M.initCfg (bin q n) (bin q a))
          (TrackedBankPreparation.initialExtent M (bin q n) (bin q a)) tm)
        (M.step^[tm] (M.initCfg (bin q n) (bin q a)))
        (bin (2*q) (n*a)) := by
    simpa [hnv, hav] using hr
  refine ⟨t, tm, htm, ht, hr', ?_⟩
  simpa [hbit, hmod] using hword
