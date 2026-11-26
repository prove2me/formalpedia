-- Prove2me | solution 1 for Erdos266.f_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:43:27.203928+00:00
-- url     : https://prove2.me/submissions/57684e55-007e-4cb3-8347-38a81b34eacd

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth
public import Theorems.Thm_Erdos266_factor_ge

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution {i : ℕ} {x : ℝ} (hx : (2 * i : ℝ) ≤ x) (hx0 : 0 < x) : 0 < f i x := by
  rw [f]
  apply inv_pos.mpr
  apply prod_pos
  intro j hj
  have := factor_ge hj hx
  linarith [half_pos hx0]
end Erdos266
