-- Prove2me | solution 1 for ErdosRubinTaylor.reach_cut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:39:26.454474+00:00
-- url     : https://prove2.me/submissions/4f194477-d6ac-4ffd-9e32-c85a6932542b

module
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Definitions.Def_ChoosabilityLib_ERTGallai
public import Theorems.Thm_ErdosRubinTaylor_SConn_rtg


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*} {G : SimpleGraph V}
namespace ErdosRubinTaylor
theorem _root_.solution {T : Set V} (hT : SConn G T) {x : V} (hx : x ∈ T) {v : V} (hv : v ∈ T \ {x}) :
    ∃ c ∈ T \ {x}, G.Adj c x ∧ Relation.ReflTransGen (adjIn G (T \ {x})) v c := by
  by_contra hno
  push Not at hno
  have key : ∀ w, Relation.ReflTransGen (adjIn G T) v w →
      w ∈ T \ {x} ∧ Relation.ReflTransGen (adjIn G (T \ {x})) v w := by
    intro w hw
    induction hw with
    | refl => exact ⟨hv, .refl⟩
    | @tail b c _ hbc ih =>
      obtain ⟨ih1, ih2⟩ := ih
      by_cases hcx : c = x
      · subst hcx; exact absurd ih2 (hno b ih1 hbc.2.2)
      · have hc : c ∈ T \ {x} := ⟨hbc.2.1, hcx⟩
        exact ⟨hc, ih2.tail ⟨ih1, hc, hbc.2.2⟩⟩
  exact (key x (hT.rtg hv.1 hx)).1.2 rfl
end ErdosRubinTaylor
