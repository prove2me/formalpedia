-- Prove2me | solution 1 for Erdos266.abs_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:40:31.553537+00:00
-- url     : https://prove2.me/submissions/da8acbd6-d38c-4688-b919-a60975ac9984

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
    (hB : 0 ≤ B) (hBN : B ≤ N) (hc : ∀ j ∈ s, |c j| ≤ B) :
    |∏ j ∈ s, (N + c j)| ≤ (2 * N) ^ s.card := by
  have hN0 : 0 ≤ N := hB.trans hBN
  rw [abs_prod, ← prod_const]
  refine prod_le_prod (fun j _ => abs_nonneg _) fun j hj => ?_
  have := hc j hj
  rw [abs_le] at this ⊢
  constructor <;> nlinarith
end Erdos266
