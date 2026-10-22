-- Prove2me | solution 1 for GDGen3.rootJ_reference_factor
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:37:31.132394+00:00
-- url     : https://prove2.me/submissions/37748f50-02aa-48ca-9027-cbc02fdfe840

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

open GDGen3

namespace GDGen3Proof_rootJ_reference_factor

lemma pj_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (j : ℕ) (hj : j ≠ 0) :
    0 < pj r j := by
  have ht : r ^ (2 * j) < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
  exact div_pos (by linarith) (by positivity)

end GDGen3Proof_rootJ_reference_factor

open GDGen3Proof_rootJ_reference_factor

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) (hi : 1 ≤ i) :
    rootJ r (1 + r) (referenceXi r (i - 1)) i =
      r ^ i * rootE r i / ((1 - r ^ i) * (1 - (r ^ i * r) ^ 2)) := by
  have hprev : r ^ (i - 1) = r ^ i / r := by
    apply (eq_div_iff (ne_of_gt hr)).2
    rw [← pow_succ, Nat.sub_add_cancel hi]
  have hci : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
    have hplus : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by exact_mod_cast Nat.sub_add_cancel hi
    linarith
  have hpi : pj r i ≠ 0 := ne_of_gt (pj_pos r hr hr1 i (by omega))
  have hpi1 : pj r (i + 1) ≠ 0 := ne_of_gt (pj_pos r hr hr1 (i + 1) (by omega))
  unfold rootJ rootNu referenceXi rootE
  rw [Nat.sub_add_cancel hi, hprev, hci]
  unfold pj
  have he : r ^ (2 * i) = (r ^ i) ^ 2 := by rw [Nat.mul_comm 2 i, pow_mul]
  have he1 : r ^ (2 * (i + 1)) = (r ^ i * r) ^ 2 := by
    rw [Nat.mul_comm 2 (i + 1), pow_mul, pow_succ r i]
  rw [he, he1]
  set b := r ^ i
  have hbpos : 0 < b := pow_pos hr i
  have hblt : b < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
  have hbrlt : b * r < 1 := by nlinarith
  have hbrpos : 0 < b * r := by positivity
  have hbnz : 1 - b ≠ 0 := by linarith
  have hbne : 1 - b ^ 2 ≠ 0 := by nlinarith
  have hbrne : 1 - (b * r) ^ 2 ≠ 0 := by nlinarith
  have hbrne' : 1 - b ^ 2 * r ^ 2 ≠ 0 := by convert hbrne using 1 <;> ring
  field_simp [hbnz, hbne, hbrne, hbrne']
  ring
