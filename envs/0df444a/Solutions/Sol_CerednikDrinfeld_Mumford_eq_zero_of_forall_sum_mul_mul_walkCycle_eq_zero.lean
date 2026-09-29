-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.eq_zero_of_forall_sum_mul_mul_walkCycle_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/1ab624cc-59b9-5d24-b7cc-5fe8057936ed

import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Theorems.Thm_LT_LatticeTree_exists_act_stdVertex_eq
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_eq_zero_of_forall_sum_mul_mul_walkCycle_eq_zero

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

namespace Law3UQ

theorem walkCycle_copy {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    [DecidableEq (QuotEdge G 𝒯)] {E : Type} (orb : E → QuotEdge G 𝒯) {u v u' v' : W} (p : 𝒯.Walk u v)
    (hu : u = u') (hv : v = v') : walkCycle 𝒯 orb (p.copy hu hv) = walkCycle 𝒯 orb p := by
  subst hu hv; rfl

end Law3UQ

theorem solution
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    {G : Type} [Group G] [MulAction G (LT.LatticeTree.Vertex R K₀)]
    [GraphAction G (CerednikDrinfeld.BruhatTits.tree R K₀)]
    (τ : LT.LatticeTree.Vertex R K₀ → ZMod 2) (hτ : ∀ (g : G) (w : LT.LatticeTree.Vertex R K₀), τ (g • w) = τ w)
    (hadj : ∀ u w : LT.LatticeTree.Vertex R K₀, (CerednikDrinfeld.BruhatTits.tree R K₀).Adj u w → τ u ≠ τ w)
    [DecidableEq (QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀))]
    {E : Type} [Fintype E] (eE : E ≃ {e : QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀) // τ e.out.fst = 0})
    (w : E → ℤ) (hw : ∀ e : E, w e ≠ 0)
    (d : E → ℤ)
    (h : ∀ (g : GL (Fin 2) K₀)
      (p : (CerednikDrinfeld.BruhatTits.tree R K₀).Walk (LT.LatticeTree.stdVertex R K₀) (g • LT.LatticeTree.stdVertex R K₀)),
      ∑ e, w e * d e * walkCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1) p e = 0) :
    d = 0 := by
  classical
  funext e
  set d₀ : (BruhatTits.tree R K₀).Dart := (eE e).1.out with hd₀
  have hx0 : τ d₀.fst = 0 := (eE e).2
  have hy : τ d₀.snd ≠ 0 := fun h0 => hadj _ _ d₀.adj (hx0.trans h0.symm)
  obtain ⟨g₁, hg₁⟩ := LT.LatticeTree.exists_act_stdVertex_eq R K₀ d₀.fst
  obtain ⟨g₂, hg₂⟩ := LT.LatticeTree.exists_act_stdVertex_eq R K₀ d₀.snd
  have hg₁' : g₁ • LT.LatticeTree.stdVertex R K₀ = d₀.fst := hg₁
  have hg₂' : g₂ • LT.LatticeTree.stdVertex R K₀ = d₀.snd := hg₂
  obtain ⟨p⟩ := (BruhatTits.tree_connected_and_colorable_two R K₀).1.preconnected (LT.LatticeTree.stdVertex R K₀) d₀.fst
  have h1 := h g₁ (p.copy rfl hg₁'.symm)
  have h2 := h g₂ ((p.append (SimpleGraph.Walk.cons d₀.adj SimpleGraph.Walk.nil)).copy rfl hg₂'.symm)
  rw [Law3UQ.walkCycle_copy] at h1 h2
  rw [walkCycle_append] at h2
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, h1, zero_add, walkCycle_cons, walkCycle_nil,
    Pi.zero_apply, add_zero] at h2
  have hd₀eq : (⟨(d₀.fst, d₀.snd), d₀.adj⟩ : (BruhatTits.tree R K₀).Dart) = d₀ := rfl
  have hidx : ∀ e' : E, dartIndex (BruhatTits.tree R K₀) (eE e').1 d₀ = if e' = e then 1 else 0 := by
    intro e'
    unfold dartIndex
    have hmk : Quotient.mk (orbitRel G (BruhatTits.tree R K₀).Dart) d₀ = (eE e).1 := by rw [hd₀]; exact Quotient.out_eq _
    have hne : Quotient.mk (orbitRel G (BruhatTits.tree R K₀).Dart) d₀.symm ≠ (eE e').1 := by
      intro heq
      apply hy
      have hrel : (orbitRel G (BruhatTits.tree R K₀).Dart) (eE e').1.out d₀.symm := by
        rw [← Quotient.eq, Quotient.out_eq]; exact heq.symm
      obtain ⟨γ, hγ⟩ := hrel
      have : τ (eE e').1.out.fst = τ d₀.snd := by
        rw [← hγ, smul_dart_fst, hτ]; rfl
      rw [← this]; exact (eE e').2
    rw [hmk, if_neg hne, sub_zero]
    by_cases hee : e' = e
    · subst hee; simp
    · rw [if_neg (fun h' => hee (eE.injective (Subtype.ext h'.symm))), if_neg hee]
  rw [hd₀eq] at h2
  simp only [hidx, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  exact (mul_eq_zero.1 h2).resolve_left (hw e)

end S_CerednikDrinfeld_Mumford_eq_zero_of_forall_sum_mul_mul_walkCycle_eq_zero
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_eq_zero_of_forall_sum_mul_mul_walkCycle_eq_zero (solution)
