-- Prove2me | solution 1 for Expanders.expander_mixing_of_two_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:53:05.534452+00:00
-- url     : https://prove2.me/submissions/b45971b0-e821-4a13-9868-c4edc3d6f807

module
public import Mathlib
public import Definitions.Def_ExpanderLib_MixingAux
public import Definitions.Def_ExpanderLib_NilliBall
public import Definitions.Def_ExpanderLib_Expanders
public import Theorems.Thm_Expanders_expander_mixing_of_nonneg

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix
open Expanders
variable {V : Type*} [Fintype V]
namespace Expanders
theorem _root_.solution (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : G.IsRegularOfDegree d) (hV : 2 ≤ Fintype.card V) {μ : ℝ}
    (hμ : ∀ x : V → ℝ, ∑ v, x v = 0 → |dotProduct x (G.adjMatrix ℝ *ᵥ x)| ≤ μ * dotProduct x x)
    (S T : Finset V) :
    |(edgeCount G S T : ℝ) - d * S.card * T.card / Fintype.card V| ≤
      μ * Real.sqrt (S.card * T.card) := by
  classical
  refine expander_mixing_of_nonneg G hd ?_ hμ S T
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card V)
  set x : V → ℝ := Pi.single a 1 - Pi.single b 1 with hx
  have hxs : ∑ v, x v = 0 := by simp [hx, Finset.sum_sub_distrib]
  have hxx : dotProduct x x = 2 := by
    simp only [hx, dotProduct_sub, dotProduct_single, Pi.sub_apply, Pi.single_apply, hab,
      hab.symm, ↓reduceIte]
    norm_num
  have := (abs_nonneg _).trans (hμ x hxs)
  rw [hxx] at this
  linarith
end Expanders
