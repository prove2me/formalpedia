-- Prove2me | solution 1 for Erdos3.leng_sah_sawhney
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:02:32.829817+00:00
-- url     : https://prove2.me/submissions/545bce83-bec5-459d-87a2-cc5581e37810

import Mathlib
import Definitions.Def_Erdos142Basic
import Theorems.Thm_Erdos142_leng_sah_sawhney

open Erdos142

theorem solution (k : ℕ) (hk : 5 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop,
      (r k N : ℝ) ≤ (N : ℝ) * Real.exp (-((Real.log (Real.log N)) ^ c)) :=
  Erdos142.leng_sah_sawhney k hk
