-- Prove2me | solution 1 for Corless.Dv_sub_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:43:00.380092+00:00
-- url     : https://prove2.me/submissions/a28969e9-ec0d-4d06-b00d-df23e8fd02d9

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
public import Theorems.Thm_Corless_Dv_hyb_step
public import Theorems.Thm_Corless_Dv_congr
public import Theorems.Thm_Corless_Dv_one
public import Theorems.Thm_Corless_Dv_zero
attribute [local simp] Corless.Dv_one
attribute [local simp] Corless.Dv_zero



set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless
namespace Corless
theorem _root_.solution (s t : ℕ → ℤ) (M : ℕ) :
    Dv s M - Dv t M = ∑ j ∈ range (M - 1),
      C (s j - t j) * X * Dv (hyb s t j) j * Dv (fun i => hyb s t j (i + j + 2)) (M - 2 - j) := by
  have hs : Dv s M = Dv (hyb s t (M - 1)) M :=
    Dv_congr fun i hi => by simp [hyb, show i < M - 1 by omega]
  have ht : Dv t M = Dv (hyb s t 0) M := Dv_congr fun i _ => by simp [hyb]
  rw [hs, ht, ← Finset.sum_range_sub (fun j => Dv (hyb s t j) M)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have := Dv_hyb_step s t j (M - 2 - j)
  rwa [show j + (M - 2 - j) + 2 = M by omega] at this
end Corless
