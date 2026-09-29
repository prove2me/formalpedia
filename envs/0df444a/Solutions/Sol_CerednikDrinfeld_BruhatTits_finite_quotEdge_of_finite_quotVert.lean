-- Prove2me | solution 1 for CerednikDrinfeld.BruhatTits.finite_quotEdge_of_finite_quotVert
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/cb7ab237-9b33-5af9-acb3-3c7689536804

import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_LatticeTreeBaseChange
import Theorems.Thm_CerednikDrinfeld_BruhatTits_finite_setOf_dist_le
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_BruhatTits_finite_quotEdge_of_finite_quotVert

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

theorem solution
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    {G : Type} [Group G] [MulAction G (LT.LatticeTree.Vertex R K₀)]
    [CerednikDrinfeld.Mumford.GraphAction G (CerednikDrinfeld.BruhatTits.tree R K₀)]
    [Finite (CerednikDrinfeld.Mumford.QuotVert G (LT.LatticeTree.Vertex R K₀))] :
    Finite (CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀)) := by
  classical
  set 𝒯 := CerednikDrinfeld.BruhatTits.tree R K₀ with h𝒯

  have hloc : ∀ v : LT.LatticeTree.Vertex R K₀, Finite {d : 𝒯.Dart // d.fst = v} := by
    intro v
    have hball := CerednikDrinfeld.BruhatTits.finite_setOf_dist_le R K₀ ϖ hϖ v 1

    have hsub : ∀ d : {d : 𝒯.Dart // d.fst = v}, d.1.snd ∈ {w : LT.LatticeTree.Vertex R K₀ | 𝒯.dist v w ≤ 1} := by
      intro d
      obtain ⟨d, hd⟩ := d
      subst hd
      show 𝒯.dist d.fst d.snd ≤ 1
      exact (SimpleGraph.dist_le (SimpleGraph.Walk.cons d.adj SimpleGraph.Walk.nil)).trans (by simp)
    haveI : Finite ↥{w : LT.LatticeTree.Vertex R K₀ | 𝒯.dist v w ≤ 1} := hball.to_subtype
    refine Finite.of_injective (fun d : {d : 𝒯.Dart // d.fst = v} =>
      (⟨d.1.snd, hsub d⟩ : ↥{w : LT.LatticeTree.Vertex R K₀ | 𝒯.dist v w ≤ 1})) ?_
    intro d d' h
    have h' : d.1.snd = d'.1.snd := congrArg Subtype.val h
    apply Subtype.ext
    ext
    · exact d.2.trans d'.2.symm
    · exact h'

  haveI : ∀ q : QuotVert G (LT.LatticeTree.Vertex R K₀), Finite {d : 𝒯.Dart // d.fst = q.out} := fun q => hloc _
  refine Finite.of_surjective
    (fun p : (Σ q : QuotVert G (LT.LatticeTree.Vertex R K₀), {d : 𝒯.Dart // d.fst = q.out}) =>
      (Quotient.mk (orbitRel G 𝒯.Dart) p.2.1 : QuotEdge G 𝒯)) ?_
  intro e
  induction e using Quotient.inductionOn with
  | h d =>
    set q : QuotVert G (LT.LatticeTree.Vertex R K₀) := Quotient.mk (orbitRel G (LT.LatticeTree.Vertex R K₀)) d.fst with hq
    have hrel : (orbitRel G (LT.LatticeTree.Vertex R K₀)) q.out d.fst := by
      rw [← Quotient.eq (r := orbitRel G (LT.LatticeTree.Vertex R K₀)), Quotient.out_eq, hq]
    obtain ⟨γ, hγ⟩ := hrel
    refine ⟨⟨q, ⟨γ • d, ?_⟩⟩, ?_⟩
    · rw [smul_dart_fst]; exact hγ
    · show Quotient.mk (orbitRel G 𝒯.Dart) (γ • d) = Quotient.mk (orbitRel G 𝒯.Dart) d
      exact Quotient.sound ⟨γ, rfl⟩

end S_CerednikDrinfeld_BruhatTits_finite_quotEdge_of_finite_quotVert
end P2MW
export P2MW.S_CerednikDrinfeld_BruhatTits_finite_quotEdge_of_finite_quotVert (solution)
