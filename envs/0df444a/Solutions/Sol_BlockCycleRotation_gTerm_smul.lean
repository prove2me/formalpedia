-- Prove2me | solution 1 for BlockCycleRotation.gTerm_smul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:35:46.790308+00:00
-- url     : https://prove2.me/submissions/991044e8-bfd9-4b4d-8161-546a96824ddc

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Remark21
import Mathlib

open Real Finset Filter Topology

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **`gTerm` is homogeneous of degree `-3`.** -/
theorem solution {k a a' : ℕ} (hk : 0 < k) (h1 : 1 ≤ a') (h2 : a' < a) :
    gTerm (k * a, k * a') = gTerm (a, a') / (k : ℝ) ^ 3:= by
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
