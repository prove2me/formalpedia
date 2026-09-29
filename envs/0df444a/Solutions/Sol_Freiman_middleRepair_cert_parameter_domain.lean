-- Prove2me | solution 1 for Freiman.middleRepair_cert_parameter_domain
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:53:33.410091+00:00
-- url     : https://prove2.me/submissions/777ae8ab-6494-471d-a34f-c673d98daa6f

import Definitions.Def_Freiman_middleRepairLedger

open Freiman

private theorem cd_pos (w : List ℕ+) : 0 ≤ (middleCD w).1 ∧ 0 < (middleCD w).2 := by
  have aux : ∀ (w : List ℕ+) (z : ℝ × ℝ), 0 ≤ z.1 → 0 < z.2 →
      0 ≤ (w.foldl (fun z a => (z.2, z.1 + ((a : ℕ) : ℝ) * z.2)) z).1 ∧
      0 < (w.foldl (fun z a => (z.2, z.1 + ((a : ℕ) : ℝ) * z.2)) z).2 := by
    intro w
    induction w with
    | nil => intro z hz hp; exact ⟨hz, hp⟩
    | cons a w ih =>
      intro z hz hp
      have ha : (0 : ℝ) < ((a : ℕ) : ℝ) := by exact_mod_cast a.pos
      exact ih _ (le_of_lt hp) (add_pos_of_nonneg_of_pos hz (mul_pos ha hp))
  exact aux w (0,1) (by norm_num) (by norm_num)

theorem solution :
    ∀ c : MiddleCore, middleRegular c → certRectangleMem middleCertRectangle (middleParameter (middleNormalized c).left) (middleParameter (middleNormalized c).right) ∧ 0 < middleQ c := by
  intro c hc
  have hd : middleRegular (middleNormalized c) := by
    unfold middleNormalized
    split
    · exact hc
    · exact ⟨hc.2.1, hc.1, hc.2.2.2, hc.2.2.1⟩
  constructor
  · simpa [certRectangleMem, middleCertRectangle] using
      (show (1/4:ℝ) ≤ middleParameter (middleNormalized c).left ∧
        middleParameter (middleNormalized c).left ≤ (4/5:ℝ) ∧
        (1/4:ℝ) ≤ middleParameter (middleNormalized c).right ∧
        middleParameter (middleNormalized c).right ≤ (4/5:ℝ) from
        ⟨hd.1.1, hd.1.2, hd.2.1.1, hd.2.1.2⟩)
  · exact div_pos (pow_pos (cd_pos _).2 2) (pow_pos (cd_pos _).2 2)

#print axioms solution
