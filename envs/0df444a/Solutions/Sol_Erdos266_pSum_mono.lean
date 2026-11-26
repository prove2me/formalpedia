-- Prove2me | solution 1 for Erdos266.pSum_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:16:22.446639+00:00
-- url     : https://prove2.me/submissions/3c3b06f8-6e10-44c3-b91b-73fd45ea09aa

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_term_nonneg

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution {i' r s : ℕ} (hr : cnt (4 * i' + 4) ≤ r) (hrs : r ≤ s) :
    pSum i' r ≤ pSum i' s := by
  have hs : pSum i' (r + (s - r))
      = pSum i' r + ∑ x ∈ range (s - r), f (i' + 1) ((aSeq (r + x) : ℕ) : ℝ) := by
    rw [pSum, sum_range_add]
    rfl
  have h1 : 0 ≤ ∑ x ∈ range (s - r), f (i' + 1) ((aSeq (r + x) : ℕ) : ℝ) :=
    sum_nonneg fun x _ => term_nonneg (by omega)
  calc pSum i' r ≤ pSum i' r + ∑ x ∈ range (s - r), f (i' + 1) ((aSeq (r + x) : ℕ) : ℝ) := by
        linarith
  _ = pSum i' (r + (s - r)) := hs.symm
  _ = pSum i' s := by rw [show r + (s - r) = s from by omega]
end Erdos266
