-- Prove2me | solution 1 for Corless.fam_of_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:45:51.694332+00:00
-- url     : https://prove2.me/submissions/018d6f3c-d2c8-4f32-bb8e-b97fdbba5f5a

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
public import Theorems.Thm_Corless_fold_of_mod4
public import Theorems.Thm_Corless_Dv_coeff_zero
public import Theorems.Thm_Corless_eq_one_of_sq
public import Theorems.Thm_Corless_fold_eq
public import Theorems.Thm_Corless_IsSign_mono
public import Theorems.Thm_Corless_folded_sizes


set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless
namespace Corless
theorem _root_.solution {s : ℕ → ℤ} : ∀ k, IsSign s (2 ^ (k + 1) - 1) →
    Dv s (2 ^ (k + 1) - 1) = 1 → Fam k s
  | 0, _, _ => trivial
  | k + 1, hs, h => by
      have folded := fold_of_mod4 k hs ⟨0, by rw [h]; ring⟩
      have hsize : 2 ^ (k + 1) - 1 ≤ 2 ^ (k + 2) - 1 := by
        obtain ⟨half, full⟩ := folded_sizes k
        rw [half, full]
        omega
      refine ⟨folded, solution k (hs.mono hsize) ?_⟩
      apply eq_one_of_sq _ (Dv_coeff_zero s _)
      rw [← fold_eq folded, h]
end Corless
