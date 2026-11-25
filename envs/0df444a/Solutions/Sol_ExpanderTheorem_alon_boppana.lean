-- Prove2me | solution 1 for ExpanderTheorem.alon_boppana
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:15:56.093533+00:00
-- url     : https://prove2.me/submissions/bc83fb8f-348b-4dc1-8443-9e8143d4eccd

module
public import Mathlib
public import Definitions.Def_ExpanderLib_Expanders
public import Definitions.Def_ExpanderSpectral_Solution
public import Theorems.Thm_Expanders_alon_boppana_of_dist


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix
open ExpanderTheorem
variable {V : Type*} [Fintype V]
namespace ExpanderTheorem
theorem _root_.solution (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} (hd2 : 2 ≤ d)
    (hd : G.IsRegularOfDegree d) {k : ℕ} {u w : V} (huw : 2 * k + 4 ≤ G.dist u w) :
    ∃ x : V → ℝ, x ≠ 0 ∧ ∑ v, x v = 0 ∧
      (2 * Real.sqrt (d - 1) - (2 * Real.sqrt (d - 1) - 1) / (k + 1)) * dotProduct x x ≤
        dotProduct x (G.adjMatrix ℝ *ᵥ x) :=
  Expanders.alon_boppana_of_dist G hd2 hd huw
end ExpanderTheorem
