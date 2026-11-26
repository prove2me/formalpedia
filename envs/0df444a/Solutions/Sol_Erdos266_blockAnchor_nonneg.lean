-- Prove2me | solution 1 for Erdos266.blockAnchor_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:49:46.964922+00:00
-- url     : https://prove2.me/submissions/25b8b4fa-6b23-4ef6-ac68-63fd21c8c131

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm
public import Theorems.Thm_Erdos266_sample_ge
public import Theorems.Thm_Erdos266_bigN_pos
public import Theorems.Thm_Erdos266_f_pos


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution {i l : ℕ} (h2i : (2 * i : ℝ) ≤ (bigN l : ℝ)) :
    0 ≤ blockAnchor i l := by
  refine sum_nonneg fun j _ => ?_
  have h1 : (2 * i : ℝ) ≤ (((j + 1) * bigN l : ℕ) : ℝ) := le_trans h2i sample_ge
  have h0 : (0:ℝ) < (((j + 1) * bigN l : ℕ) : ℝ) := by
    have := bigN_pos l
    have h2 : 0 < (j + 1) * bigN l := by positivity
    exact_mod_cast h2
  exact (f_pos h1 h0).le
end Erdos266
