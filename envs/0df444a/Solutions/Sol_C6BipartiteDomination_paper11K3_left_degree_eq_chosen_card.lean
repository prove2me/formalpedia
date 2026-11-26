-- Prove2me | solution 1 for C6BipartiteDomination.paper11K3_left_degree_eq_chosen_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:57:52.6958+00:00
-- url     : https://prove2.me/submissions/2b6edd77-da2a-4a16-b97e-dcc331500b9f

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
import Theorems.Thm_C6BipartiteDomination_paper11K3_edge_mem

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w : V}
    (hw : w ∈ paper11K3Supports G D) :
    paper11LeftDegree (paper11K3Edges G D hCan hmax)
      (paper11K3RightVertices G D hCan hmax) w =
        (paperChosenRepairSet G D hCan hmax w).card := by
  classical
  let R := paperChosenRepairSet G D hCan hmax w
  have hImage :
      (paper11K3Edges G D hCan hmax).filter (fun e => e.1 = w) =
        R.image (fun u : V => (w, u)) := by
    ext e
    rcases e with ⟨a, b⟩
    simp only [Finset.mem_filter]
    rw [paper11K3_edge_mem G hCan hmax]
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨⟨ha, hb⟩, hab⟩
      have hEq : a = w := hab
      subst a
      exact ⟨b, hb, rfl⟩
    · rintro ⟨u, hu, heq⟩
      cases heq
      exact ⟨⟨hw, hu⟩, rfl⟩
  rw [paper11LeftDegree, hImage]
  have hinj : Function.Injective (fun u : V => (w, u)) := by
    intro a b hab
    exact congrArg Prod.snd hab
  simpa [R] using (Finset.card_image_of_injective R hinj)
end C6BipartiteDomination
