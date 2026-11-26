-- Prove2me | solution 1 for Erdos266.inv_inf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:12:28.898451+00:00
-- url     : https://prove2.me/submissions/30785e6c-2b91-4862-88c5-2795174af0db

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_Sinf_eq
public import Theorems.Thm_Erdos266_xinf_eq
public import Theorems.Thm_Erdos266_finSum_congr
public import Theorems.Thm_Erdos266_inv_run
public import Theorems.Thm_Erdos266_mseq_dOf_le
public import Theorems.Thm_Erdos266_mseq_strictMono


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution {k : ℕ} (hk : 2 ≤ k) {i : ℕ} (hi : i < dOf k) :
    |finSum i k Sinf + tailAnchor (i + 1) k - (xinf i : ℝ)|
      ≤ εA (dOf k) * bigM k / (bigN k : ℝ) ^ (i + 2) := by
  have h := (inv_run k hk).2.2 i hi
  have e1 : finSum i k (run k).1 = finSum i k Sinf :=
    finSum_congr fun l hl j _ => Sinf_eq hk hl j
  have e2 : (run k).2 i = xinf i := by
    refine xinf_eq (le_trans (mseq_strictMono.monotone ?_) (mseq_dOf_le hk))
    omega
  rw [e1, e2] at h
  exact h
end Erdos266
