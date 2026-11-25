-- Prove2me | solution 1 for ExpanderTheorem.expander_mixing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:00:49.278688+00:00
-- url     : https://prove2.me/submissions/d9e8561c-c982-4677-8ed6-d5e6612f1f0c

module
public import Mathlib
public import Definitions.Def_ExpanderLib_Expanders
public import Definitions.Def_ExpanderSpectral_Solution
public import Theorems.Thm_Expanders_expander_mixing_of_two_le_card


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix
open ExpanderTheorem
variable {V : Type*} [Fintype V]
namespace ExpanderTheorem
theorem _root_.solution (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : G.IsRegularOfDegree d) (hV : 2 ≤ Fintype.card V) {μ : ℝ}
    (hμ : ∀ x : V → ℝ, ∑ v, x v = 0 → |dotProduct x (G.adjMatrix ℝ *ᵥ x)| ≤ μ * dotProduct x x)
    (S T : Finset V) :
    |(edgeCount G S T : ℝ) - d * S.card * T.card / Fintype.card V| ≤
      μ * Real.sqrt (S.card * T.card) :=
  Expanders.expander_mixing_of_two_le_card G hd hV hμ S T
end ExpanderTheorem
