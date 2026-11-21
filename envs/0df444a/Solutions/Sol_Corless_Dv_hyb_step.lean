-- Prove2me | solution 1 for Corless.Dv_hyb_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:42:23.606558+00:00
-- url     : https://prove2.me/submissions/f974b7ab-2169-471a-b6ff-bad5eabf1967

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
public import Theorems.Thm_Corless_Dv_congr
public import Theorems.Thm_Corless_Dv_one
public import Theorems.Thm_Corless_Dv_split
public import Theorems.Thm_Corless_Dv_zero
attribute [local simp] Corless.Dv_one
attribute [local simp] Corless.Dv_zero



set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless
namespace Corless
theorem _root_.solution (s t : ℕ → ℤ) (j m : ℕ) :
    Dv (hyb s t (j + 1)) (j + m + 2) - Dv (hyb s t j) (j + m + 2)
      = C (s j - t j) * X * Dv (hyb s t j) j * Dv (fun i => hyb s t j (i + j + 2)) m := by
  rw [Dv_split (hyb s t (j + 1)) j m, Dv_split (hyb s t j) j m]
  have agree (i : ℕ) (hi : i ≠ j) : hyb s t (j + 1) i = hyb s t j i := by
    simp only [hyb, show i < j + 1 ↔ i < j by omega]
  have e1 : Dv (hyb s t (j + 1)) (j + 1) = Dv (hyb s t j) (j + 1) :=
    Dv_congr fun i hi => agree i (by omega)
  have e2 : Dv (hyb s t (j + 1)) j = Dv (hyb s t j) j :=
    Dv_congr fun i hi => agree i (by omega)
  have e3 : Dv (fun i => hyb s t (j + 1) (i + j + 1)) (m + 1)
      = Dv (fun i => hyb s t j (i + j + 1)) (m + 1) :=
    Dv_congr fun i _ => agree (i + j + 1) (by omega)
  have e4 : Dv (fun i => hyb s t (j + 1) (i + j + 2)) m = Dv (fun i => hyb s t j (i + j + 2)) m :=
    Dv_congr fun i _ => agree (i + j + 2) (by omega)
  have e5 : hyb s t (j + 1) j = s j := by simp [hyb]
  have e6 : hyb s t j j = t j := by simp [hyb]
  rw [e1, e2, e3, e4, e5, e6, C_sub]
  ring
end Corless
