-- Prove2me | solution 1 for CerednikDrinfeld.BruhatTits.exists_pos_forall_mem_stabilizer_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/8054b15c-1270-57f7-9dfb-64eb4ac875c4

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_LatticeTreeBaseChange
import Theorems.Thm_CerednikDrinfeld_BruhatTits_finite_setOf_dist_le
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_BruhatTits_exists_pos_forall_mem_stabilizer_pow_eq_one

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_BruhatTits_exists_pos_forall_mem_stabilizer_pow_eq_one.CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "tree BruhatTits.tree Mumford.QuotVert BruhatTits.finite_setOf_dist_le BruhatTits.tree_connected_and_colorable_two"
namespace BruhatTits
p2m_export "CerednikDrinfeld.BruhatTits" "tree finite_setOf_dist_le tree_connected_and_colorable_two"
namespace StabExp
p2m_open "CerednikDrinfeld.BruhatTits CerednikDrinfeld"

open MulAction LT.LatticeTree

variable {R₀ : Type} [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
  {K₀ : Type} [Field K₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]

theorem exists_adj (w : Vertex R₀ K₀) : ∃ x : Vertex R₀ K₀, (tree R₀ K₀).Adj w x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R₀
  have hconn := (CerednikDrinfeld.BruhatTits.tree_connected_and_colorable_two R₀ K₀).1

  have hns := not_subsingleton_fixedVertexSet_scalarGL (R := R₀) (K := K₀) hϖ 1
  rw [fixedVertexSet_scalarGL, Set.subsingleton_univ_iff, not_subsingleton_iff_nontrivial] at hns
  obtain ⟨w', hw'⟩ := exists_ne w
  obtain ⟨p⟩ := hconn.preconnected w w'
  cases p with
  | nil => exact absurd rfl hw'.symm
  | cons h _ => exact ⟨_, h⟩

theorem finite_setOf_dart_fst_eq [Finite (IsLocalRing.ResidueField R₀)] (w : Vertex R₀ K₀) :
    {d : (tree R₀ K₀).Dart | d.fst = w}.Finite := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R₀
  haveI : Finite (R₀ ⧸ IsLocalRing.maximalIdeal R₀) := ‹Finite (IsLocalRing.ResidueField R₀)›
  haveI : Finite (R₀ ⧸ Ideal.span {ϖ}) :=
    Finite.of_equiv (R₀ ⧸ IsLocalRing.maximalIdeal R₀) (Ideal.quotEquivOfEq hϖ.maximalIdeal_eq).toEquiv
  have hball := CerednikDrinfeld.BruhatTits.finite_setOf_dist_le R₀ K₀ ϖ hϖ w 1
  refine Set.Finite.of_injOn (f := fun d : (tree R₀ K₀).Dart => d.snd) (fun d hd => ?_) (fun d₁ hd₁ d₂ hd₂ h => ?_) hball
  ·
    show (tree R₀ K₀).dist w d.snd ≤ 1
    rw [Set.mem_setOf_eq] at hd
    rw [← hd, SimpleGraph.dist_eq_one_iff_adj.2 d.adj]
  · rw [Set.mem_setOf_eq] at hd₁ hd₂
    exact SimpleGraph.Dart.ext _ _ (Prod.ext (hd₁.trans hd₂.symm) h)

theorem finite_stabilizer_vertex [Finite (IsLocalRing.ResidueField R₀)] (Δ : Subgroup PGL(2, K₀))
    (hfin : ∀ d : (tree R₀ K₀).Dart, Finite (stabilizer ↥Δ d)) (w : Vertex R₀ K₀) :
    Finite (stabilizer ↥Δ w) := by
  obtain ⟨x, hx⟩ := exists_adj w
  let d₀ : (tree R₀ K₀).Dart := ⟨(w, x), hx⟩
  let S : Subgroup ↥Δ := stabilizer ↥Δ w

  haveI hH : Finite (stabilizer ↥S d₀) := by
    haveI := hfin d₀
    refine Finite.of_injective (fun h : stabilizer ↥S d₀ => (⟨((h : ↥S) : ↥Δ), ?_⟩ : stabilizer ↥Δ d₀)) ?_
    · have := h.2
      rw [mem_stabilizer_iff] at this ⊢
      exact this
    · intro a b hab
      apply Subtype.ext; apply Subtype.ext
      exact congrArg (fun z : stabilizer ↥Δ d₀ => (z : ↥Δ)) hab

  haveI hQ : Finite (↥S ⧸ stabilizer ↥S d₀) := by
    have horb : (orbit ↥S d₀).Finite := by
      refine (finite_setOf_dart_fst_eq w).subset ?_
      rintro d ⟨s, rfl⟩
      show ((s : ↥Δ) • d₀).fst = w
      have hs := s.2
      rw [mem_stabilizer_iff] at hs
      exact hs
    haveI := horb.to_subtype
    exact Finite.of_equiv _ (orbitEquivQuotientStabilizer ↥S d₀)
  apply Nat.finite_of_card_ne_zero
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (stabilizer ↥S d₀)]
  exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'

omit [IsDomain R₀] [IsDiscreteValuationRing R₀] [IsFractionRing R₀ K₀] in

theorem natCard_stabilizer_smul (Δ : Subgroup PGL(2, K₀)) (g : ↥Δ) (w : Vertex R₀ K₀) :
    Nat.card (stabilizer ↥Δ (g • w)) = Nat.card (stabilizer ↥Δ w) := by
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

end CerednikDrinfeld.BruhatTits.StabExp

open CerednikDrinfeld.BruhatTits.StabExp in
theorem solution
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Finite (IsLocalRing.ResidueField R₀)]
    (K₀ : Type) [Field K₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    (Δ : Subgroup PGL(2, K₀))
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer ↥Δ d))
    [Finite (Mumford.QuotVert ↥Δ (LT.LatticeTree.Vertex R₀ K₀))] :
    ∃ m : ℕ, 0 < m ∧
      ∀ (w : LT.LatticeTree.Vertex R₀ K₀) (γ : ↥Δ), γ ∈ MulAction.stabilizer ↥Δ w → γ ^ m = 1 := by
  classical
  haveI : Fintype (Mumford.QuotVert ↥Δ (LT.LatticeTree.Vertex R₀ K₀)) := Fintype.ofFinite _
  have hfinV : ∀ w : LT.LatticeTree.Vertex R₀ K₀, Finite (MulAction.stabilizer ↥Δ w) :=
    finite_stabilizer_vertex Δ hfin

  let N : Mumford.QuotVert ↥Δ (LT.LatticeTree.Vertex R₀ K₀) → ℕ := fun o =>
    Nat.card (MulAction.stabilizer ↥Δ o.out)
  refine ⟨∏ o, N o, Finset.prod_pos fun o _ => ?_, fun w γ hγ => ?_⟩
  · haveI := hfinV o.out
    exact Nat.card_pos
  ·
    haveI := hfinV w
    have h1 : γ ^ Nat.card (MulAction.stabilizer ↥Δ w) = 1 := by
      have h := orderOf_dvd_natCard (⟨γ, hγ⟩ : MulAction.stabilizer ↥Δ w)
      rw [orderOf_dvd_iff_pow_eq_one] at h
      have h' := congrArg (fun z : MulAction.stabilizer ↥Δ w => (z : ↥Δ)) h
      simpa using h'

    have hrep : ∃ g : ↥Δ, g • w = (Quotient.mk (MulAction.orbitRel ↥Δ _) w : Mumford.QuotVert ↥Δ _).out :=
      MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.mk_out w))
    obtain ⟨g, hg⟩ := hrep
    have hdvd : Nat.card (MulAction.stabilizer ↥Δ w) ∣ ∏ o, N o := by
      have := Finset.dvd_prod_of_mem N (Finset.mem_univ (Quotient.mk (MulAction.orbitRel ↥Δ _) w))
      rwa [show N (Quotient.mk (MulAction.orbitRel ↥Δ _) w) = Nat.card (MulAction.stabilizer ↥Δ w) by
        simp only [N]; rw [← hg, natCard_stabilizer_smul]] at this
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, pow_mul, h1, one_pow]

end S_CerednikDrinfeld_BruhatTits_exists_pos_forall_mem_stabilizer_pow_eq_one
end P2MW
export P2MW.S_CerednikDrinfeld_BruhatTits_exists_pos_forall_mem_stabilizer_pow_eq_one (solution)
