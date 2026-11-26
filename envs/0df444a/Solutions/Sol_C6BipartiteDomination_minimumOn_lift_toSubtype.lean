-- Prove2me | solution 1 for C6BipartiteDomination.minimumOn_lift_toSubtype
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:08:23.48325+00:00
-- url     : https://prove2.me/submissions/b28f2ee8-ce97-455e-9d9f-0f00a6f5ea1c

import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Definitions.Def_C6BipartiteDomination_MainResults
import Theorems.Thm_C6BipartiteDomination_mem_liftFinsetToSubtype
import Theorems.Thm_C6BipartiteDomination_card_liftFinsetToSubtype
import Theorems.Thm_C6BipartiteDomination_mem_projectFinsetFromSubtype
import Theorems.Thm_C6BipartiteDomination_card_projectFinsetFromSubtype

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {S E : Finset V}
    (hE : MinimumBipartiteDominatingOn G S E) :
    MinimumBipartiteDominatingSet (G.induce (S : Set V))
      (liftFinsetToSubtype S E hE.1.1) := by
  classical
  let H := G.induce (S : Set V)
  let E' := liftFinsetToSubtype S E hE.1.1
  refine ⟨?_, ?_⟩
  · constructor
    · intro x hx
      have hxNotE : x.1 ∉ E := by
        intro hxE
        exact hx ((mem_liftFinsetToSubtype hE.1.1 x).2 hxE)
      obtain ⟨y, hyE, hyx⟩ := hE.1.2.1 x.2 hxNotE
      refine ⟨⟨y, hE.1.1 hyE⟩, ?_, ?_⟩
      · exact (mem_liftFinsetToSubtype hE.1.1 _).2 hyE
      · simpa [H, SimpleGraph.induce] using hyx
    · obtain ⟨c, hc⟩ := hE.1.2.2
      refine ⟨fun x => c x.1, ?_⟩
      intro x y hx hy hadj
      apply hc
      · exact (mem_liftFinsetToSubtype hE.1.1 x).mp hx
      · exact (mem_liftFinsetToSubtype hE.1.1 y).mp hy
      · simpa [H, SimpleGraph.induce] using hadj
  · intro F hF
    let F' := projectFinsetFromSubtype (S := S) F
    have hFsub : F' ⊆ S := by
      intro v hv
      obtain ⟨x, hx, rfl⟩ := (mem_projectFinsetFromSubtype (S := S) F v).mp hv
      exact x.2
    have hFdom : ∀ ⦃v⦄, v ∈ S → v ∉ F' →
        ∃ y ∈ F', G.Adj y v := by
      intro v hvS hvNot
      let x : {v // v ∈ S} := ⟨v, hvS⟩
      have hxNot : x ∉ F := by
        intro hx
        apply hvNot
        apply (mem_projectFinsetFromSubtype (S := S) F v).mpr
        exact ⟨x, hx, rfl⟩
      obtain ⟨y, hyF, hyx⟩ := hF.1 hxNot
      refine ⟨y.1, ?_, ?_⟩
      · exact (mem_projectFinsetFromSubtype (S := S) F y.1).mpr ⟨y, hyF, rfl⟩
      · simpa [H, SimpleGraph.induce] using hyx
    have hFbip : IsBipartiteOn G F' := by
      obtain ⟨c, hc⟩ := hF.2
      refine ⟨fun v => if hv : v ∈ S then c ⟨v, hv⟩ else false, ?_⟩
      intro a b ha hb hadj
      obtain ⟨xa, hxa, rfl⟩ :=
        (mem_projectFinsetFromSubtype (S := S) F a).mp ha
      obtain ⟨xb, hxb, rfl⟩ :=
        (mem_projectFinsetFromSubtype (S := S) F b).mp hb
      have hadj' : H.Adj xa xb := by
        simpa [H, SimpleGraph.induce] using hadj
      simpa using hc hxa hxb hadj'
    have hFLocal : BipartiteDominatingOn G S F' := ⟨hFsub, hFdom, hFbip⟩
    have hmin := hE.2 F' hFLocal
    have hcardE : E'.card = E.card := by
      simpa [E'] using card_liftFinsetToSubtype hE.1.1
    have hcardF : F'.card = F.card := by
      simpa [F'] using card_projectFinsetFromSubtype (S := S) F
    calc
      E'.card = E.card := hcardE
      _ ≤ F'.card := hmin
      _ = F.card := hcardF
end C6BipartiteDomination
