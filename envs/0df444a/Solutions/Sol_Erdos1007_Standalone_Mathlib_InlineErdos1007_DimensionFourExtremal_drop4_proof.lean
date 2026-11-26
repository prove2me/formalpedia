-- Prove2me | solution 1 for Erdos1007.Standalone.Mathlib.InlineErdos1007.DimensionFourExtremal.drop4.proof
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:56:44.288896+00:00
-- url     : https://prove2.me/submissions/7bb306f1-976c-46d3-83b9-0552b92feb75

module
public import Definitions.Def_Erdos1007_Standalone_Mathlib_InlineErdos1007
public import Definitions.Def_Erdos1007_Combinatorics_SimpleGraph_FiveVertices
public import Definitions.Def_Erdos1007_Combinatorics_SimpleGraph_NineEdges
public import Definitions.Def_Erdos1007_Combinatorics_SimpleGraph_SixVertices
public import Definitions.Def_Erdos1007_Geometry_CompleteBipartite
public import Definitions.Def_Erdos1007_Geometry_CompleteBipartiteLowerBound
public import Definitions.Def_Erdos1007_Geometry_CompleteMinusEdge
public import Definitions.Def_Erdos1007_Geometry_FinLe
public import Definitions.Def_Erdos1007_Geometry_LowDegree
public import Definitions.Def_Erdos1007_Geometry_Prism
public import Definitions.Def_Erdos1007_Geometry_UnitDistanceComap
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Logic.Basic
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.Bounds.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Definitions.Def_Erdos1007_Standalone_Mathlib_InlineErdos1007Proof
public import Theorems.Thm_Erdos1007_Standalone_Mathlib_InlineErdos1007_completeBipartiteGraph_three_three_edgeSet_ncard
public import Theorems.Thm_Erdos1007_completeBipartiteGraph_three_three_unitDistance
public import Theorems.Thm_Erdos1007_not_exists_completeBipartiteGraph_three_three_unitDistance_three
public import Theorems.Thm_Erdos1007_unitDistance_of_embedding
public import Theorems.Thm_Erdos1007_unitDistance_of_fin_le


set_option autoImplicit false
@[expose] public section
public section
open Erdos1007 Erdos1007.Standalone Erdos1007.Standalone.Mathlib Erdos1007.Standalone.Mathlib.InlineErdos1007
open SimpleGraph
namespace Erdos1007.Standalone.Mathlib.InlineErdos1007
namespace DimensionFourExtremal.drop4
theorem _root_.solution : DimensionFourExtremal.drop4 := by
  intro hyp
  let e : Fin 3 ⊕ Fin 3 ≃ Fin 6 := finSumFinEquiv
  let K : SimpleGraph (Fin 3 ⊕ Fin 3) := completeBipartiteGraph (Fin 3) (Fin 3)
  let K6 : SimpleGraph (Fin 6) := K.map e
  let ι : Fin 6 ↪ Fin 7 := Fin.castSuccEmb
  let G : SimpleGraph (Fin 7) := K6.map ι
  let φ : K ≃g K6 := Iso.map e K
  have hpull {u w : Fin 6} (hadj : K6.Adj u w) : K.Adj (e.symm u) (e.symm w) := by
    have hu : φ (e.symm u) = u :=
      (Iso.map_apply e K (e.symm u)).trans (e.apply_symm_apply u)
    have hw : φ (e.symm w) = w :=
      (Iso.map_apply e K (e.symm w)).trans (e.apply_symm_apply w)
    exact (φ.map_adj_iff).mp (hu.symm ▸ hw.symm ▸ hadj)
  have hK6 : K6.edgeSet.ncard = 9 :=
    (Set.ncard_congr' φ.mapEdgeSet).symm.trans
      completeBipartiteGraph_three_three_edgeSet_ncard
  have hG : G.edgeSet.ncard = 9 := by
    have hset : G.edgeSet = ι.sym2Map '' K6.edgeSet := by
      rw [show G = K6.map ι from rfl]
      exact edgeSet_map ι K6
    rw [hset, Set.ncard_image_of_injective K6.edgeSet ι.sym2Map.injective, hK6]
  have hdim : HasDimension G 4 := by
    refine ⟨?_, ?_⟩
    · obtain ⟨f, hfInj, hfDist⟩ := completeBipartiteGraph_three_three_unitDistance
      let f6 : Fin 6 → EuclideanSpace ℝ (Fin 4) := fun x => f (e.symm x)
      have hf6Inj : Function.Injective f6 := hfInj.comp e.symm.injective
      obtain ⟨p, hp⟩ := (Set.finite_range f6).exists_notMem
      let g : Fin 7 → EuclideanSpace ℝ (Fin 4) := fun i =>
        if h : (i : ℕ) < 6 then f6 ⟨i, h⟩ else p
      have hg_lt {i : Fin 7} (h : (i : ℕ) < 6) : g i = f6 ⟨i, h⟩ := by
        have heq : g i = (if h' : (i : ℕ) < 6 then f6 ⟨i, h'⟩ else p) := rfl
        rw [dif_pos h] at heq
        exact heq
      have hg_ge {i : Fin 7} (h : ¬ (i : ℕ) < 6) : g i = p := by
        have heq : g i = (if h' : (i : ℕ) < 6 then f6 ⟨i, h'⟩ else p) := rfl
        rw [dif_neg h] at heq
        exact heq
      refine ⟨g, ?_, ?_⟩
      · intro a b hab
        by_cases ha : (a : ℕ) < 6
        · by_cases hb : (b : ℕ) < 6
          · exact Fin.ext (congrArg (fun j : Fin 6 => (j : ℕ))
              (hf6Inj ((hg_lt ha).symm.trans (hab.trans (hg_lt hb)))))
          · exact False.elim
              (hp ⟨⟨a, ha⟩, (hg_lt ha).symm.trans (hab.trans (hg_ge hb))⟩)
        · by_cases hb : (b : ℕ) < 6
          · exact False.elim
              (hp ⟨⟨b, hb⟩, (hg_lt hb).symm.trans (hab.symm.trans (hg_ge ha))⟩)
          · have ha6 : (a : ℕ) = 6 := by have := a.isLt; omega
            have hb6 : (b : ℕ) = 6 := by have := b.isLt; omega
            exact Fin.ext (ha6.trans hb6.symm)
      · intro u v huv
        obtain ⟨u', v', hu', rfl, rfl⟩ := (map_adj ι K6 u v).mp huv
        have hg_emb {i : Fin 6} : g (ι i) = f6 i := by
          have hlt : ((ι i : Fin 7) : ℕ) < 6 := by
            simp only [ι, Fin.castSuccEmb_apply, Fin.val_castSucc]
            exact i.isLt
          rw [hg_lt hlt]
          congr 1
        rw [hg_emb (i := u'), hg_emb (i := v')]
        exact hfDist (e.symm u') (e.symm v') (hpull hu')
    · rw [mem_lowerBounds]
      intro m hm
      obtain ⟨g0, hgInj, hgDist⟩ := hm
      have hKrep := unitDistance_of_embedding
        ((Embedding.map ι K6).comp φ.toEmbedding) ⟨g0, hgInj, hgDist⟩
      have hmle : ¬ m ≤ 3 := fun hle =>
        not_exists_completeBipartiteGraph_three_three_unitDistance_three
          (unitDistance_of_fin_le hle hKrep)
      exact Nat.succ_le_of_lt (Nat.gt_of_not_le hmle)
  have hnot : ¬ Nonempty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3)) := by
    intro ⟨ψ⟩
    have hc := ψ.card_eq
    simp only [Fintype.card_fin, Fintype.card_sum] at hc
    omega
  exact hnot (hyp 7 G hdim hG)
end DimensionFourExtremal.drop4
end Erdos1007.Standalone.Mathlib.InlineErdos1007
