-- Prove2me | solution 1 for Erdos266.f_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:43:21.95627+00:00
-- url     : https://prove2.me/submissions/e06bcba3-0ce2-4126-9da2-b99795a218d3

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
theorem _root_.solution {i : ℕ} {x : ℝ} (hx : (2 * i : ℝ) ≤ x) (hx0 : 0 < x) :
    f i x ≤ (2 / x) ^ i := by
  rw [f]
  have hprod : (x / 2) ^ i ≤ ∏ j ∈ range i, (x + (tSeq j : ℝ)) := by
    calc (x / 2) ^ i = ∏ _j ∈ range i, (x / 2) := by rw [prod_const, card_range]
    _ ≤ ∏ j ∈ range i, (x + (tSeq j : ℝ)) :=
        prod_le_prod (fun j _ => (half_pos hx0).le) fun j hj => factor_ge hj hx
  have h1 : (0:ℝ) < (x / 2) ^ i := by positivity
  calc (∏ j ∈ range i, (x + (tSeq j : ℝ)))⁻¹
      ≤ ((x / 2) ^ i)⁻¹ := inv_anti₀ h1 hprod
  _ = (2 / x) ^ i := by
        rw [← inv_pow, inv_div]
end Erdos266
