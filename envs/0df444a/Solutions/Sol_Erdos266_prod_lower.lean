-- Prove2me | solution 1 for Erdos266.prod_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:40:38.534807+00:00
-- url     : https://prove2.me/submissions/2ed2a622-80af-4ae0-9a38-a442d48e34d7

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_SlopeLemma

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution {ι : Type*} {s : Finset ι} {c : ι → ℝ} {N B : ℝ}
    (hB : 0 ≤ B) (hB2 : B ≤ N / 2) (hc : ∀ j ∈ s, |c j| ≤ B) :
    (N / 2) ^ s.card ≤ ∏ j ∈ s, (N + c j) := by
  have hN0 : 0 ≤ N := by linarith
  rw [← prod_const]
  refine prod_le_prod (fun j _ => by positivity) fun j hj => ?_
  have := hc j hj
  rw [abs_le] at this
  linarith [this.1]
end Erdos266
