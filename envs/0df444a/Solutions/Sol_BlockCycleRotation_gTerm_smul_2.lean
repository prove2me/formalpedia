-- Prove2me | solution 2 for BlockCycleRotation.gTerm_smul
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-05T11:39:18.839382+00:00
-- url     : https://prove2.me/submissions/fd6e89da-af3b-4677-b3a4-204487a4bacb

import Definitions.Def_BlockCycleRotation_Remark21
import Mathlib

open BlockCycleRotation
open Real Finset Filter Topology

theorem solution {k a a' : ℕ} (hk : 0 < k) (h1 : 1 ≤ a') (h2 : a' < a) :
    gTerm (k * a, k * a') = gTerm (a, a') / (k : ℝ) ^ 3 := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have ha : (0 : ℝ) < (a : ℝ) := by
    have : 0 < a := by omega
    exact_mod_cast this
  have ha' : (0 : ℝ) < (a' : ℝ) := by
    have : 0 < a' := by omega
    exact_mod_cast this
  have hk1 : 1 ≤ k * a' := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hk2 : k * a' < k * a := by
    rw [Nat.mul_comm k a', Nat.mul_comm k a]
    exact Nat.mul_lt_mul_of_lt_of_le h2 (le_refl k) hk
  unfold gTerm
  rw [if_pos ⟨hk1, hk2⟩, if_pos ⟨h1, h2⟩]
  push_cast
  field_simp
