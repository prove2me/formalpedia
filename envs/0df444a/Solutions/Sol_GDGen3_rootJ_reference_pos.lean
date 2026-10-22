-- Prove2me | solution 1 for GDGen3.rootJ_reference_pos
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:37:32.708506+00:00
-- url     : https://prove2.me/submissions/7e4771e5-570f-4c06-8d92-cd0735de18db

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

open GDGen3

namespace GDGen3Proof_rootJ_reference_pos

lemma pj_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (j : ℕ) (hj : j ≠ 0) :
    0 < pj r j := by
  have ht : r ^ (2 * j) < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
  exact div_pos (by linarith) (by positivity)

lemma rootE_one (r : ℝ) (hr : 0 < r) : rootE r 1 = (1 + r) * (1 - r) ^ 2 / r := by
  unfold rootE
  norm_num only [pow_one, Nat.cast_one]
  field_simp
  ring

lemma rootE_step (r : ℝ) (hr : 0 < r) (i : ℕ) :
    rootE r (i + 1) - rootE r i = (1 + r) * (1 - r) * (1 / r ^ (i + 1) - 1) := by
  unfold rootE
  push_cast
  rw [pow_succ r i]
  field_simp
  ring

lemma rootE_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) (hi : 1 ≤ i) : 0 < rootE r i := by
  induction i, hi using Nat.le_induction with
  | base =>
    rw [rootE_one r hr]
    have hd : 0 < 1 - r := by linarith
    positivity
  | succ i hi ih =>
    have hp : 1 < 1 / r ^ (i + 1) := by
      apply (lt_div_iff₀ (pow_pos hr _)).2
      simpa using pow_lt_one₀ (le_of_lt hr) hr1 (by omega : i + 1 ≠ 0)
    have hstep := rootE_step r hr i
    have hg : 0 < (1 + r) * (1 - r) * (1 / r ^ (i + 1) - 1) := by
      have hd : 0 < 1 - r := by linarith
      have hp' : 0 < 1 / r ^ (i + 1) - 1 := by linarith
      positivity
    linarith

lemma rootJ_reference_factor (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) (hi : 1 ≤ i) :
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

end GDGen3Proof_rootJ_reference_pos

open GDGen3Proof_rootJ_reference_pos

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) (hi : 1 ≤ i) :
    0 < rootJ r (1 + r) (referenceXi r (i - 1)) i := by
  rw [rootJ_reference_factor r hr hr1 i hi]
  have hp : 0 < r ^ i := pow_pos hr i
  have hi1 : r ^ i < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
  have hp1 : r ^ i * r < 1 := by nlinarith
  have hp1pos : 0 < r ^ i * r := by positivity
  have hden : 0 < (1 - r ^ i) * (1 - (r ^ i * r) ^ 2) := by
    have hd1 : 0 < 1 - r ^ i := by linarith
    have hd2 : 0 < 1 - (r ^ i * r) ^ 2 := by nlinarith
    positivity
  exact div_pos (mul_pos hp (rootE_pos r hr hr1 i hi)) hden
