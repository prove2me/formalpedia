-- Prove2me | solution 1 for Champernowne.err_mul_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:41:18.451999+00:00
-- url     : https://prove2.me/submissions/61b4b511-a077-4f28-b4fa-4c38b33df9ca

module
public import Definitions.Def_LeanPool_Champernowne_Positions
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic
public import Definitions.Def_LeanPool_Champernowne_Asymptotics
public import Theorems.Thm_Champernowne_cohort_le_n

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
open Filter Asymptotics Topology
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) (n : ℕ) (w : List ℕ) :
    7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n * ((b - 1) * (champM b n - 1))
      ≤ (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ 2) * n := by
  rcases Nat.lt_or_ge (champM b n) 2 with h2 | h2
  · rw [show champM b n - 1 = 0 by omega]
    simp
  · have hD := cohort_le_n hb n
    have hpow : b ^ champM b n = b ^ 2 * b ^ (champM b n - 2) := by
      rw [← pow_add]; congr 1; omega
    calc 7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n
        * ((b - 1) * (champM b n - 1))
        = (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ 2)
          * ((b - 1) * b ^ (champM b n - 2) * (champM b n - 1)) := by
          rw [hpow]; ring
    _ ≤ (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ 2) * n := Nat.mul_le_mul_left _ hD
end Champernowne
