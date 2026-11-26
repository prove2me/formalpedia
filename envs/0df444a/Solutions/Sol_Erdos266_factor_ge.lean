-- Prove2me | solution 1 for Erdos266.factor_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:40:21.617686+00:00
-- url     : https://prove2.me/submissions/0ac84b6b-18d8-4dbc-94da-01b9a073a5d4

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth
public import Theorems.Thm_Erdos266_abs_tSeq_le


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution {i j : ℕ} (hj : j ∈ range i) {x : ℝ} (hx : (2 * i : ℝ) ≤ x) :
    x / 2 ≤ x + (tSeq j : ℝ) := by
  have h1 : |(tSeq j : ℝ)| ≤ (i : ℝ) := by
    have h2 : |tSeq j| ≤ (j : ℚ) + 1 := abs_tSeq_le j
    have h3 : |(tSeq j : ℝ)| ≤ (j : ℝ) + 1 := by exact_mod_cast h2
    have h4 : (j : ℝ) + 1 ≤ i := by exact_mod_cast mem_range.mp hj
    linarith
  rw [abs_le] at h1
  linarith [h1.1]
end Erdos266
