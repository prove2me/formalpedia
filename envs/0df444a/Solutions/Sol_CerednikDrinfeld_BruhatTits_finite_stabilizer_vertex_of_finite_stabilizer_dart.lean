-- Prove2me | solution 1 for CerednikDrinfeld.BruhatTits.finite_stabilizer_vertex_of_finite_stabilizer_dart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/75a5b117-accc-5bd1-99ac-abc3253b1bae

import Mathlib
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Theorems.Thm_CerednikDrinfeld_Mumford_finite_stabilizer_of_finite_stabilizer_dart
import Theorems.Thm_CerednikDrinfeld_BruhatTits_finite_setOf_dist_le
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_BruhatTits_finite_stabilizer_vertex_of_finite_stabilizer_dart

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction LT.LatticeTree

theorem solution
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    (K₀ : Type) [Field K₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (G : Type) [Group G] [MulAction G (LT.LatticeTree.Vertex R₀ K₀)] [GraphAction G (BruhatTits.tree R₀ K₀)]
    (hfinD : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (stabilizer G d))
    (v : LT.LatticeTree.Vertex R₀ K₀) : Finite (stabilizer G v) := by
  classical

  obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible R₀
  have hmax : IsLocalRing.maximalIdeal R₀ = Ideal.span {ϖ₀} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ₀).mp hϖ₀
  haveI : Finite (R₀ ⧸ IsLocalRing.maximalIdeal R₀) := ‹Finite (IsLocalRing.ResidueField R₀)›
  haveI : Finite (R₀ ⧸ Ideal.span {ϖ₀}) := Finite.of_equiv _ (Ideal.quotEquivOfEq hmax).toEquiv
  refine CerednikDrinfeld.Mumford.finite_stabilizer_of_finite_stabilizer_dart G (BruhatTits.tree R₀ K₀) v ?_ ?_
    (fun d _ => hfinD d)
  ·
    refine Set.Finite.subset (CerednikDrinfeld.BruhatTits.finite_setOf_dist_le R₀ K₀ ϖ₀ hϖ₀ v 1) ?_
    intro w hw
    show (BruhatTits.tree R₀ K₀).dist v w ≤ 1
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hw]
  ·
    obtain ⟨hconn, -⟩ := CerednikDrinfeld.BruhatTits.tree_connected_and_colorable_two R₀ K₀
    have hne : Vertex.act (diagSnd (unitOfNeZero (K := K₀) hϖ₀.ne_zero)) (stdVertex R₀ K₀) ≠ stdVertex R₀ K₀ :=
      stdVertex_ne_act_diagSnd hϖ₀

    obtain ⟨x, hx⟩ : ∃ x : LT.LatticeTree.Vertex R₀ K₀, x ≠ v := by
      by_cases h : stdVertex R₀ K₀ = v
      · exact ⟨_, fun h' => hne (h'.trans h.symm)⟩
      · exact ⟨_, h⟩
    obtain ⟨p⟩ := hconn.preconnected v x
    cases p with
    | nil => exact absurd rfl hx
    | cons h _ => exact ⟨_, h⟩

#print axioms solution

end S_CerednikDrinfeld_BruhatTits_finite_stabilizer_vertex_of_finite_stabilizer_dart
end P2MW
export P2MW.S_CerednikDrinfeld_BruhatTits_finite_stabilizer_vertex_of_finite_stabilizer_dart (solution)
