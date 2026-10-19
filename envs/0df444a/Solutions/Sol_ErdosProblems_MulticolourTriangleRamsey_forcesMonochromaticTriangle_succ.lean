-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.forcesMonochromaticTriangle_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/b5fa98e1-2751-44de-b40a-f002d0f89d74

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_labelGraph_pullback_embedding
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_cliqueFree_pullback_embedding
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_triangleFree_deleteUnusedColour

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution {n k : ℕ}
    (hn : ForcesMonochromaticTriangle n k) :
    ForcesMonochromaticTriangle (1 + (k + 1) * n) (k + 1) := by
  classical
  intro C hC
  let root : Fin (1 + (k + 1) * n) := ⟨0, by omega⟩
  let others : Finset (Fin (1 + (k + 1) * n)) :=
    Finset.univ.erase root
  let edgeColour : Fin (1 + (k + 1) * n) → Fin (k + 1) :=
    fun v => if h : root ≠ v then C.get root v h else 0
  have hothers : others.card = (k + 1) * n := by
    simp [others]
  have hpigeon :
      (Finset.univ : Finset (Fin (k + 1))).card * n ≤ others.card := by
    simp [hothers]
  obtain ⟨omitted, _, hfiber⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (f := edgeColour) (s := others)
      (t := (Finset.univ : Finset (Fin (k + 1))))
      (fun _ _ => Finset.mem_univ _)
      (Finset.univ_nonempty) hpigeon
  let fiber := others.filter (fun v => edgeColour v = omitted)
  have hlarge : n ≤ fiber.card := by
    simpa [fiber] using hfiber
  let embedding : Fin n ↪ Fin (1 + (k + 1) * n) :=
    ((Fin.castLEEmb hlarge).trans
      (Finset.equivFin fiber).symm.toEmbedding).trans
        (Function.Embedding.subtype (fun v => v ∈ fiber))
  have hmember (v : Fin n) : embedding v ∈ fiber := by
    exact ((Finset.equivFin fiber).symm (Fin.castLE hlarge v)).property
  have hrootedge (v : Fin n) :
      (C.labelGraph omitted).Adj root (embedding v) := by
    have hfilter := Finset.mem_filter.mp (hmember v)
    have herase : embedding v ∈ Finset.univ.erase root := by
      simpa only [others] using hfilter.1
    have hrootne : root ≠ embedding v :=
      Ne.symm (Finset.mem_erase.mp herase).1
    apply (SimpleGraph.TopEdgeLabeling.labelGraph_adj
      root (embedding v)).mpr
    refine ⟨hrootne, ?_⟩
    simpa [edgeColour, hrootne] using hfilter.2
  let restricted : SimpleGraph.TopEdgeLabeling (Fin n) (Fin (k + 1)) :=
    C.pullback embedding
  have hrestricted : TriangleFree restricted :=
    cliqueFree_pullback_embedding C embedding hC
  have hnoedge (u v : Fin n) :
      ¬ (restricted.labelGraph omitted).Adj u v := by
    intro hadj
    have horiginal : (C.labelGraph omitted).Adj (embedding u) (embedding v) := by
      have hcomap :
          restricted.labelGraph omitted =
            (C.labelGraph omitted).comap embedding :=
        labelGraph_pullback_embedding C embedding omitted
      rw [hcomap] at hadj
      exact hadj
    exact hC omitted {root, embedding u, embedding v}
      ((SimpleGraph.is3Clique_triple_iff).mpr
        ⟨hrootedge u, hrootedge v, horiginal⟩)
  have hunused :
      ∀ edge : (⊤ : SimpleGraph (Fin n)).edgeSet,
        restricted edge ≠ omitted := by
    intro edge hcolour
    rcases edge with ⟨edge, hedge⟩
    induction edge using Sym2.inductionOn with
    | _ u v =>
      exact hnoedge u v
        ((SimpleGraph.TopEdgeLabeling.labelGraph_adj u v).mpr
          ⟨hedge, hcolour⟩)
  exact hn (deleteUnusedColour restricted omitted hunused)
    (triangleFree_deleteUnusedColour restricted omitted hunused hrestricted)
end ErdosProblems.MulticolourTriangleRamsey
