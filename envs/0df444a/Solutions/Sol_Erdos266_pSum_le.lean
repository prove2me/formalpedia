-- Prove2me | solution 1 for Erdos266.pSum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:20:13.822193+00:00
-- url     : https://prove2.me/submissions/97cc6b08-ffc2-4493-8267-85cd8be98d8b

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_pSum_mono
public import Theorems.Thm_Erdos266_pSum_tendsto

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution {i' n : ℕ} (hn : cnt (4 * i' + 4) ≤ n) :
    pSum i' n ≤ ((xinf i' : ℚ) : ℝ) := by
  refine ge_of_tendsto (pSum_tendsto i') ?_
  rw [eventually_atTop]
  exact ⟨n, fun s hs => pSum_mono hn hs⟩
end Erdos266
