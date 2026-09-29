-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.pathCycle_mulEquiv_eq_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/ddfc2af0-55ab-5ebf-8d56-dc23fe40798f

import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Theorems.Thm_CerednikDrinfeld_Mumford_pathCycle_eq_pathCycle_of_isTree
import Mathlib.Algebra.Ring.Int.Units
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_pathCycle_mulEquiv_eq_of_iso

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Mumford P2MW.S_CerednikDrinfeld_Mumford_pathCycle_mulEquiv_eq_of_iso.CerednikDrinfeld.Mumford MulAction"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Mumford.pathCycle Mumford.GraphAction Mumford.QuotEdge Mumford.quotientReversal Mumford.pathCycle_eq_pathCycle_of_isTree"
namespace Mumford
p2m_export "CerednikDrinfeld.Mumford" "dartIndex walkCycle somePath pathCycle pathCycle_eq_walkCycle GraphAction QuotEdge quotientReversal pathCycle_eq_pathCycle_of_isTree"
namespace G7
p2m_open "CerednikDrinfeld.Mumford CerednikDrinfeld"

variable {G : Type} [Group G] {W : Type} [MulAction G W]
  (𝒯 : SimpleGraph W) [GraphAction G 𝒯]

theorem mapDart_symm (n : 𝒯 ≃g 𝒯) (d : 𝒯.Dart) :
    (n.toHom.mapDart d).symm = n.toHom.mapDart d.symm := by
  cases d with | mk p h => ?_
  cases p
  rfl

theorem mapDart_injective (n : 𝒯 ≃g 𝒯) : Function.Injective n.toHom.mapDart := by
  intro d d' h
  obtain ⟨⟨a, b⟩, hab⟩ := d
  obtain ⟨⟨a', b'⟩, hab'⟩ := d'
  have h1 : (n a, n b) = (n a', n b') := congrArg SimpleGraph.Dart.toProd h
  have h2 : n a = n a' := congrArg Prod.fst h1
  have h3 : n b = n b' := congrArg Prod.snd h1
  cases n.injective h2
  cases n.injective h3
  rfl

theorem mapDart_smul (φ : G ≃* G) (n : 𝒯 ≃g 𝒯) (hn : ∀ (g : G) (w : W), n (g • w) = φ g • n w)
    (g : G) (d : 𝒯.Dart) : n.toHom.mapDart (g • d) = φ g • n.toHom.mapDart d := by
  obtain ⟨⟨a, b⟩, hab⟩ := d
  apply SimpleGraph.Dart.ext
  show (n (g • a), n (g • b)) = (φ g • n a, φ g • n b)
  rw [hn g a, hn g b]

theorem mk_eq_of_mk_mapDart_eq (φ : G ≃* G) (n : 𝒯 ≃g 𝒯) (hn : ∀ (g : G) (w : W), n (g • w) = φ g • n w)
    (d d' : 𝒯.Dart)
    (h : (Quotient.mk (orbitRel G 𝒯.Dart) (n.toHom.mapDart d) : QuotEdge G 𝒯) =
      Quotient.mk (orbitRel G 𝒯.Dart) (n.toHom.mapDart d')) :
    (Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯) = Quotient.mk (orbitRel G 𝒯.Dart) d' := by
  obtain ⟨g, hg⟩ := Quotient.eq.mp h

  apply Quotient.sound
  refine ⟨φ.symm g, ?_⟩
  apply mapDart_injective 𝒯 n
  simp only
  rw [mapDart_smul 𝒯 φ n hn, MulEquiv.apply_symm_apply]
  exact hg

theorem quotientReversal_mk (d : 𝒯.Dart) :
    quotientReversal G 𝒯 (Quotient.mk (orbitRel G 𝒯.Dart) d) = Quotient.mk (orbitRel G 𝒯.Dart) d.symm := rfl

theorem quotientReversal_quotientReversal (q : QuotEdge G 𝒯) :
    quotientReversal G 𝒯 (quotientReversal G 𝒯 q) = q := by
  induction q using Quotient.inductionOn with | _ d => ?_
  rw [quotientReversal_mk, quotientReversal_mk, SimpleGraph.Dart.symm_symm]

variable [DecidableEq (QuotEdge G 𝒯)]

theorem dartIndex_mapDart (φ : G ≃* G) (n : 𝒯 ≃g 𝒯) (hn : ∀ (g : G) (w : W), n (g • w) = φ g • n w)
    (q q' : QuotEdge G 𝒯) (s : ℤˣ)
    (hq : ∀ d : 𝒯.Dart, Quotient.mk (orbitRel G 𝒯.Dart) d = q →
      Quotient.mk (orbitRel G 𝒯.Dart) (n.toHom.mapDart d) = (if s = 1 then q' else quotientReversal G 𝒯 q'))
    (d : 𝒯.Dart) :
    dartIndex 𝒯 q' (n.toHom.mapDart d) = (s : ℤ) * dartIndex 𝒯 q d := by

  induction q using Quotient.inductionOn with | _ d₀ => ?_
  have h0 := hq d₀ rfl

  rcases Int.units_eq_one_or s with hs | hs
  · subst hs
    simp only [if_true] at hq h0
    have key : ∀ x : 𝒯.Dart, (Quotient.mk (orbitRel G 𝒯.Dart) (n.toHom.mapDart x) = q') ↔
        (Quotient.mk (orbitRel G 𝒯.Dart) x = Quotient.mk (orbitRel G 𝒯.Dart) d₀) := by
      intro x
      constructor
      · intro hx
        exact mk_eq_of_mk_mapDart_eq 𝒯 φ n hn x d₀ (hx.trans h0.symm)
      · intro hx; exact hq x hx
    simp only [dartIndex, Units.val_one, one_mul, mapDart_symm, key]
  · subst hs
    have hne : (-1 : ℤˣ) ≠ 1 := by decide
    simp only [hne, if_false] at hq h0

    have h0' : Quotient.mk (orbitRel G 𝒯.Dart) (n.toHom.mapDart d₀.symm) = q' := by
      rw [← mapDart_symm, ← quotientReversal_mk, h0, quotientReversal_quotientReversal]
    have key : ∀ x : 𝒯.Dart, (Quotient.mk (orbitRel G 𝒯.Dart) (n.toHom.mapDart x) = q') ↔
        (Quotient.mk (orbitRel G 𝒯.Dart) x.symm = Quotient.mk (orbitRel G 𝒯.Dart) d₀) := by
      intro x
      constructor
      · intro hx
        have := mk_eq_of_mk_mapDart_eq 𝒯 φ n hn x d₀.symm (hx.trans h0'.symm)
        rw [← SimpleGraph.Dart.symm_symm d₀]
        show quotientReversal G 𝒯 (Quotient.mk (orbitRel G 𝒯.Dart) x) =
          quotientReversal G 𝒯 (Quotient.mk (orbitRel G 𝒯.Dart) d₀.symm)
        rw [this]
      · intro hx
        have := hq x.symm hx
        rw [← mapDart_symm, ← quotientReversal_mk] at this
        have := congrArg (quotientReversal G 𝒯) this
        rwa [quotientReversal_quotientReversal, quotientReversal_quotientReversal] at this
    simp only [dartIndex, Units.val_neg, Units.val_one, mapDart_symm, key, SimpleGraph.Dart.symm_symm]
    ring

theorem walkCycle_map {E : Type} (orb : E → QuotEdge G 𝒯)
    (φ : G ≃* G) (n : 𝒯 ≃g 𝒯) (hn : ∀ (g : G) (w : W), n (g • w) = φ g • n w)
    (π : E ≃ E) (s : ℤˣ)
    (hπ : ∀ (e : E) (d : 𝒯.Dart), Quotient.mk (orbitRel G 𝒯.Dart) d = orb e →
      Quotient.mk (orbitRel G 𝒯.Dart) (n.toHom.mapDart d) =
        (if s = 1 then orb (π e) else quotientReversal G 𝒯 (orb (π e))))
    {u v : W} (p : 𝒯.Walk u v) (e : E) :
    walkCycle 𝒯 orb (p.map n.toHom) (π e) = (s : ℤ) * walkCycle 𝒯 orb p e := by
  simp only [walkCycle, SimpleGraph.Walk.darts_map, List.map_map]
  induction p.darts with
  | nil => simp
  | cons d l ih =>
    simp only [List.map_cons, List.sum_cons, Function.comp_apply, ih,
      dartIndex_mapDart 𝒯 φ n hn (orb e) (orb (π e)) s (hπ e) d]
    ring

end CerednikDrinfeld.Mumford.G7

open CerednikDrinfeld.Mumford.G7 in
theorem solution
    {G : Type} [Group G] {W : Type} [MulAction G W] [DecidableEq W]
    (𝒯 : SimpleGraph W) [CerednikDrinfeld.Mumford.GraphAction G 𝒯] (hT : 𝒯.IsTree)
    (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
    [DecidableEq (CerednikDrinfeld.Mumford.QuotEdge G 𝒯)] {E : Type} [Fintype E]
    (eE : E ≃ {e : CerednikDrinfeld.Mumford.QuotEdge G 𝒯 // τ e.out.fst = 0})
    (φ : G ≃* G) (n : 𝒯 ≃g 𝒯) (hn : ∀ (g : G) (w : W), n (g • w) = φ g • n w)
    (π : E ≃ E) (s : ℤˣ)
    (hπ : ∀ (e : E) (d : 𝒯.Dart), Quotient.mk (MulAction.orbitRel G 𝒯.Dart) d = (eE e).1 →
      Quotient.mk (MulAction.orbitRel G 𝒯.Dart) (n.toHom.mapDart d) =
        (if s = 1 then (eE (π e)).1 else CerednikDrinfeld.Mumford.quotientReversal G 𝒯 (eE (π e)).1))
    (v₀ : W) (γ : G) (e : E) :
    CerednikDrinfeld.Mumford.pathCycle 𝒯 (fun e => (eE e).1) v₀ (φ γ) (π e) =
      (s : ℤ) * CerednikDrinfeld.Mumford.pathCycle 𝒯 (fun e => (eE e).1) v₀ γ e := by
  classical

  rw [← CerednikDrinfeld.Mumford.pathCycle_eq_pathCycle_of_isTree 𝒯 hT (fun e => (eE e).1) v₀ (n v₀) (φ γ)]

  have hreach : 𝒯.Reachable v₀ (γ • v₀) := hT.connected.preconnected v₀ (γ • v₀)
  let p : 𝒯.Path v₀ (γ • v₀) := somePath hreach
  have hend : n (γ • v₀) = φ γ • n v₀ := hn γ v₀
  let q : 𝒯.Walk (n v₀) (φ γ • n v₀) := ((p : 𝒯.Walk v₀ (γ • v₀)).map n.toHom).copy rfl hend
  have hq : q.IsPath := by
    simp only [q, SimpleGraph.Walk.isPath_copy]
    exact SimpleGraph.Walk.map_isPath_of_injective n.injective p.2
  rw [pathCycle_eq_walkCycle 𝒯 _ hT.isAcyclic (n v₀) (φ γ) ⟨q, hq⟩,
    pathCycle_eq_walkCycle 𝒯 _ hT.isAcyclic v₀ γ p]
  show walkCycle 𝒯 (fun e => (eE e).1) q (π e) = (s : ℤ) * walkCycle 𝒯 (fun e => (eE e).1) (p : 𝒯.Walk v₀ (γ • v₀)) e
  have hdq : walkCycle 𝒯 (fun e => (eE e).1) q =
      walkCycle 𝒯 (fun e => (eE e).1) ((p : 𝒯.Walk v₀ (γ • v₀)).map n.toHom) := by
    funext e'
    simp only [q, walkCycle, SimpleGraph.Walk.darts_copy]
  rw [hdq]
  exact walkCycle_map 𝒯 (fun e => (eE e).1) φ n hn π s hπ (p : 𝒯.Walk v₀ (γ • v₀)) e

end S_CerednikDrinfeld_Mumford_pathCycle_mulEquiv_eq_of_iso
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_pathCycle_mulEquiv_eq_of_iso (solution)
