-- Prove2me | solution 1 for C6BipartiteDomination.paper11K3_right_degree_eq_incident_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:57:54.860992+00:00
-- url     : https://prove2.me/submissions/c67f37b0-639f-46e5-b3ed-61edea0045b4

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
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V} :
    paper11RightDegree (paper11K3Edges G D hCan hmax)
      (paper11K3Supports G D) u =
        (paper11K3IncidentSupports G D hCan hmax u).card := by
  classical
  let T := paper11K3IncidentSupports G D hCan hmax u
  have hImage :
      (paper11K3Edges G D hCan hmax).filter (fun e => e.2 = u) =
        T.image (fun w : V => (w, u)) := by
    ext e
    rcases e with ⟨a, b⟩
    simp only [Finset.mem_filter]
    rw [paper11K3_edge_mem G hCan hmax]
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨⟨ha, hb⟩, hbu⟩
      subst b
      exact ⟨a, Finset.mem_filter.mpr ⟨ha, hb⟩, rfl⟩
    · rintro ⟨w, hw, heq⟩
      cases heq
      have hw' : a ∈ paper11K3IncidentSupports G D hCan hmax u := by
        simpa [T] using hw
      simp only [paper11K3IncidentSupports, Finset.mem_filter] at hw'
      exact ⟨⟨hw'.1, hw'.2⟩, rfl⟩
  rw [paper11RightDegree, hImage]
  have hinj : Function.Injective (fun w : V => (w, u)) := by
    intro a b hab
    exact congrArg Prod.fst hab
  simpa [T] using (Finset.card_image_of_injective T hinj)
end C6BipartiteDomination
