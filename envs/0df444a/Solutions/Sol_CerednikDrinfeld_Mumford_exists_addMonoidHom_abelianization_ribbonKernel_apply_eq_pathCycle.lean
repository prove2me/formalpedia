-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.exists_addMonoidHom_abelianization_ribbonKernel_apply_eq_pathCycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/a05ed68f-a7e6-56c6-886e-f525e927285a

import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_exists_addMonoidHom_abelianization_ribbonKernel_apply_eq_pathCycle

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

namespace BS0

theorem mem_ribbonKernel_iff_fibre_sum {E V : Type*} [Fintype E] [DecidableEq V] (D : DegeneracyData E V)
    (x : E → ℤ) :
    x ∈ ribbonKernel D ↔
      (∀ v, ∑ e, (if D.a e = v then x e else 0) = 0) ∧ (∀ v, ∑ e, (if D.b e = v then x e else 0) = 0) := by
  rw [mem_ribbonKernel, Fin.forall_fin_two]
  simp only [jointDelta, Matrix.cons_val_zero, Matrix.cons_val_one, pushforward, funext_iff, Pi.zero_apply,
    Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, degeneracyMatrix, Matrix.of_apply, ite_mul, one_mul,
    zero_mul]

section Frame

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
  (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
  [DecidableEq (QuotEdge G 𝒯)]
  {E V : Type} [Fintype E] [DecidableEq E] [DecidableEq V] (D : DegeneracyData E V)
  (eE : E ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})
  (eV : V ≃ QuotVert G W)
  (ha : ∀ e : E, eV (D.a e) = Quotient.mk (orbitRel G W) (eE e).1.out.fst)
  (hb : ∀ e : E, eV (D.b e) = Quotient.mk (orbitRel G W) (eE e).1.out.snd)

omit [DecidableEq (QuotEdge G 𝒯)] in

theorem exists_smul_eq_out (d : 𝒯.Dart) : ∃ g : G, g • d = (Quotient.mk (orbitRel G 𝒯.Dart) d).out := by
  obtain ⟨g, hg⟩ := Quotient.mk_out (s := orbitRel G 𝒯.Dart) d
  exact ⟨g, hg⟩

omit [DecidableEq (QuotEdge G 𝒯)] in
include hτ in
theorem tau_out_fst (d : 𝒯.Dart) : τ (Quotient.mk (orbitRel G 𝒯.Dart) d).out.fst = τ d.fst := by
  obtain ⟨g, hg⟩ := exists_smul_eq_out (G := G) 𝒯 d
  rw [← hg]
  exact hτ g d.fst

omit [DecidableEq (QuotEdge G 𝒯)] in
theorem mk_out_fst (d : 𝒯.Dart) :
    Quotient.mk (orbitRel G W) (Quotient.mk (orbitRel G 𝒯.Dart) d).out.fst = Quotient.mk (orbitRel G W) d.fst := by
  obtain ⟨g, hg⟩ := exists_smul_eq_out (G := G) 𝒯 d
  rw [← hg]
  exact Quotient.sound ⟨g, rfl⟩

omit [DecidableEq (QuotEdge G 𝒯)] in
theorem mk_out_snd (d : 𝒯.Dart) :
    Quotient.mk (orbitRel G W) (Quotient.mk (orbitRel G 𝒯.Dart) d).out.snd = Quotient.mk (orbitRel G W) d.snd := by
  obtain ⟨g, hg⟩ := exists_smul_eq_out (G := G) 𝒯 d
  rw [← hg]
  exact Quotient.sound ⟨g, rfl⟩

def ptInd (i : ZMod 2) (z : W) (v : V) : ℤ :=
  if τ z = i ∧ eV.symm (Quotient.mk (orbitRel G W) z) = v then 1 else 0

omit [Fintype E] in
include hτ in

theorem dartIndex_eq_of_fst (d : 𝒯.Dart) (h0 : τ d.fst = 0) (hsnd : τ d.snd ≠ 0) (e : E) :
    dartIndex 𝒯 (eE e).1 d =
      if e = eE.symm ⟨Quotient.mk (orbitRel G 𝒯.Dart) d, (tau_out_fst 𝒯 τ hτ d).trans h0⟩ then 1 else 0 := by
  rw [dartIndex]
  have h2 : ¬ Quotient.mk (orbitRel G 𝒯.Dart) d.symm = (eE e).1 := by
    intro h
    apply hsnd
    have := (eE e).2
    rw [← h, tau_out_fst 𝒯 τ hτ] at this
    exact this
  have h1 : (Quotient.mk (orbitRel G 𝒯.Dart) d = (eE e).1) ↔
      e = eE.symm ⟨Quotient.mk (orbitRel G 𝒯.Dart) d, (tau_out_fst 𝒯 τ hτ d).trans h0⟩ := by
    rw [Equiv.eq_symm_apply, Subtype.ext_iff]
    exact eq_comm
  rw [if_neg h2, sub_zero]
  exact if_congr h1 rfl rfl

omit [Fintype E] in
include hτ in

theorem dartIndex_eq_of_snd (d : 𝒯.Dart) (h0 : τ d.fst ≠ 0) (hsnd : τ d.snd = 0) (e : E) :
    dartIndex 𝒯 (eE e).1 d =
      -(if e = eE.symm ⟨Quotient.mk (orbitRel G 𝒯.Dart) d.symm, (tau_out_fst 𝒯 τ hτ d.symm).trans hsnd⟩
        then 1 else 0) := by
  rw [dartIndex]
  have h1 : ¬ Quotient.mk (orbitRel G 𝒯.Dart) d = (eE e).1 := by
    intro h
    apply h0
    have := (eE e).2
    rw [← h, tau_out_fst 𝒯 τ hτ] at this
    exact this
  have h2 : (Quotient.mk (orbitRel G 𝒯.Dart) d.symm = (eE e).1) ↔
      e = eE.symm ⟨Quotient.mk (orbitRel G 𝒯.Dart) d.symm, (tau_out_fst 𝒯 τ hτ d.symm).trans hsnd⟩ := by
    rw [Equiv.eq_symm_apply, Subtype.ext_iff]
    exact eq_comm
  rw [if_neg h1, zero_sub]
  exact congrArg Neg.neg (if_congr h2 rfl rfl)

theorem sum_ite_ite_eq {f : E → V} (v : V) (e₀ : E) :
    (∑ e, if f e = v then (if e = e₀ then (1 : ℤ) else 0) else 0) = if f e₀ = v then 1 else 0 := by
  rw [Finset.sum_eq_single e₀]
  · simp
  · intro e _ hne; simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem sum_ite_neg_ite_eq {f : E → V} (v : V) (e₀ : E) :
    (∑ e, if f e = v then -(if e = e₀ then (1 : ℤ) else 0) else 0) = -(if f e₀ = v then 1 else 0) := by
  rw [Finset.sum_eq_single e₀]
  · by_cases hf : f e₀ = v <;> simp [hf]
  · intro e _ hne; simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem zmod2_eq_zero_of_ne {a b : ZMod 2} (ha0 : a ≠ 0) (hab : a ≠ b) : b = 0 := by
  revert a b; decide

include hτ hadj ha in

theorem sum_a_dartIndex (d : 𝒯.Dart) (v : V) :
    ∑ e, (if D.a e = v then dartIndex 𝒯 (eE e).1 d else 0) = ptInd τ eV 0 d.fst v - ptInd τ eV 0 d.snd v := by
  have hcol := hadj _ _ d.adj

  have hcls : ∀ (q : QuotEdge G 𝒯) (hq : τ q.out.fst = 0) (x : W),
      Quotient.mk (orbitRel G W) q.out.fst = Quotient.mk (orbitRel G W) x →
      (D.a (eE.symm ⟨q, hq⟩) = v ↔ eV.symm (Quotient.mk (orbitRel G W) x) = v) := by
    intro q hq x hx
    rw [Equiv.symm_apply_eq, ← Equiv.apply_eq_iff_eq eV (x := D.a _) (y := v), ha, Equiv.apply_symm_apply]
    exact Eq.congr_left hx
  by_cases h0 : τ d.fst = 0
  · have hsnd : τ d.snd ≠ 0 := fun h => hcol (h0.trans h.symm)
    simp_rw [dartIndex_eq_of_fst 𝒯 τ hτ eE d h0 hsnd]
    rw [sum_ite_ite_eq]
    have c₁ : (τ d.fst = 0 ∧ eV.symm (Quotient.mk (orbitRel G W) d.fst) = v) ↔
        D.a (eE.symm ⟨Quotient.mk (orbitRel G 𝒯.Dart) d, (tau_out_fst 𝒯 τ hτ d).trans h0⟩) = v := by
      rw [hcls _ _ d.fst (mk_out_fst 𝒯 d)]
      exact ⟨fun h => h.2, fun h => ⟨h0, h⟩⟩
    have c₂ : ¬ (τ d.snd = 0 ∧ eV.symm (Quotient.mk (orbitRel G W) d.snd) = v) := fun h => hsnd h.1
    unfold ptInd
    rw [if_neg c₂, sub_zero]
    exact (if_congr c₁ rfl rfl).symm
  · have hsnd : τ d.snd = 0 := zmod2_eq_zero_of_ne h0 hcol
    simp_rw [dartIndex_eq_of_snd 𝒯 τ hτ eE d h0 hsnd]
    rw [sum_ite_neg_ite_eq]
    have c₁ : ¬ (τ d.fst = 0 ∧ eV.symm (Quotient.mk (orbitRel G W) d.fst) = v) := fun h => h0 h.1
    have c₂ : (τ d.snd = 0 ∧ eV.symm (Quotient.mk (orbitRel G W) d.snd) = v) ↔
        D.a (eE.symm ⟨Quotient.mk (orbitRel G 𝒯.Dart) d.symm, (tau_out_fst 𝒯 τ hτ d.symm).trans hsnd⟩) = v := by
      rw [hcls _ _ d.snd (mk_out_fst 𝒯 d.symm)]
      exact ⟨fun h => h.2, fun h => ⟨hsnd, h⟩⟩
    unfold ptInd
    rw [if_neg c₁, zero_sub]
    exact congrArg Neg.neg (if_congr c₂ rfl rfl).symm

include hτ hadj hb in

theorem sum_b_dartIndex (d : 𝒯.Dart) (v : V) :
    ∑ e, (if D.b e = v then dartIndex 𝒯 (eE e).1 d else 0) =
      -ptInd τ eV 1 d.fst v + ptInd τ eV 1 d.snd v := by
  have hcol := hadj _ _ d.adj
  have key01 : ∀ a : ZMod 2, a ≠ 0 ↔ a = 1 := by decide
  have key10 : ∀ a : ZMod 2, a = 0 → a ≠ 1 := by decide
  have hcls : ∀ (q : QuotEdge G 𝒯) (hq : τ q.out.fst = 0) (x : W),
      Quotient.mk (orbitRel G W) q.out.snd = Quotient.mk (orbitRel G W) x →
      (D.b (eE.symm ⟨q, hq⟩) = v ↔ eV.symm (Quotient.mk (orbitRel G W) x) = v) := by
    intro q hq x hx
    rw [Equiv.symm_apply_eq, ← Equiv.apply_eq_iff_eq eV (x := D.b _) (y := v), hb, Equiv.apply_symm_apply]
    exact Eq.congr_left hx
  by_cases h0 : τ d.fst = 0
  · have hsnd : τ d.snd ≠ 0 := fun h => hcol (h0.trans h.symm)
    simp_rw [dartIndex_eq_of_fst 𝒯 τ hτ eE d h0 hsnd]
    rw [sum_ite_ite_eq]
    have c₁ : ¬ (τ d.fst = 1 ∧ eV.symm (Quotient.mk (orbitRel G W) d.fst) = v) := fun h => key10 _ h0 h.1
    have c₂ : (τ d.snd = 1 ∧ eV.symm (Quotient.mk (orbitRel G W) d.snd) = v) ↔
        D.b (eE.symm ⟨Quotient.mk (orbitRel G 𝒯.Dart) d, (tau_out_fst 𝒯 τ hτ d).trans h0⟩) = v := by
      rw [hcls _ _ d.snd (mk_out_snd 𝒯 d)]
      exact ⟨fun h => h.2, fun h => ⟨(key01 _).mp hsnd, h⟩⟩
    unfold ptInd
    rw [if_neg c₁, neg_zero, zero_add]
    exact (if_congr c₂ rfl rfl).symm
  · have hsnd : τ d.snd = 0 := zmod2_eq_zero_of_ne h0 hcol
    simp_rw [dartIndex_eq_of_snd 𝒯 τ hτ eE d h0 hsnd]
    rw [sum_ite_neg_ite_eq]
    have c₁ : (τ d.fst = 1 ∧ eV.symm (Quotient.mk (orbitRel G W) d.fst) = v) ↔
        D.b (eE.symm ⟨Quotient.mk (orbitRel G 𝒯.Dart) d.symm, (tau_out_fst 𝒯 τ hτ d.symm).trans hsnd⟩) = v := by
      rw [hcls _ _ d.fst (mk_out_snd 𝒯 d.symm)]
      exact ⟨fun h => h.2, fun h => ⟨(key01 _).mp h0, h⟩⟩
    have c₂ : ¬ (τ d.snd = 1 ∧ eV.symm (Quotient.mk (orbitRel G W) d.snd) = v) := fun h => key10 _ hsnd h.1
    unfold ptInd
    rw [if_neg c₂, add_zero]
    exact congrArg Neg.neg (if_congr c₁ rfl rfl).symm

include hτ hadj ha in

theorem sum_a_walkCycle {x y : W} (p : 𝒯.Walk x y) (v : V) :
    ∑ e, (if D.a e = v then walkCycle 𝒯 (fun e => (eE e).1) p e else 0) =
      ptInd τ eV 0 x v - ptInd τ eV 0 y v := by
  induction p with
  | nil => simp
  | @cons u w z h p ih =>
    have hsplit : ∀ e, (if D.a e = v then walkCycle 𝒯 (fun e => (eE e).1) (SimpleGraph.Walk.cons h p) e else 0) =
        (if D.a e = v then dartIndex 𝒯 (eE e).1 ⟨(u, w), h⟩ else 0) +
          (if D.a e = v then walkCycle 𝒯 (fun e => (eE e).1) p e else 0) := by
      intro e
      rw [walkCycle_cons]
      by_cases hc : D.a e = v
      · simp only [if_pos hc]
      · simp only [if_neg hc, add_zero]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib, ih, sum_a_dartIndex 𝒯 τ hτ hadj D eE eV ha]
    show ptInd τ eV 0 u v - ptInd τ eV 0 w v + (ptInd τ eV 0 w v - ptInd τ eV 0 z v) = _
    ring

include hτ hadj hb in

theorem sum_b_walkCycle {x y : W} (p : 𝒯.Walk x y) (v : V) :
    ∑ e, (if D.b e = v then walkCycle 𝒯 (fun e => (eE e).1) p e else 0) =
      -ptInd τ eV 1 x v + ptInd τ eV 1 y v := by
  induction p with
  | nil => simp
  | @cons u w z h p ih =>
    have hsplit : ∀ e, (if D.b e = v then walkCycle 𝒯 (fun e => (eE e).1) (SimpleGraph.Walk.cons h p) e else 0) =
        (if D.b e = v then dartIndex 𝒯 (eE e).1 ⟨(u, w), h⟩ else 0) +
          (if D.b e = v then walkCycle 𝒯 (fun e => (eE e).1) p e else 0) := by
      intro e
      rw [walkCycle_cons]
      by_cases hc : D.b e = v
      · simp only [if_pos hc]
      · simp only [if_neg hc, add_zero]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib, ih, sum_b_dartIndex 𝒯 τ hτ hadj D eE eV hb]
    show -ptInd τ eV 1 u v + ptInd τ eV 1 w v + (-ptInd τ eV 1 w v + ptInd τ eV 1 z v) = _
    ring

include hτ in
theorem ptInd_smul (i : ZMod 2) (g : G) (z : W) (v : V) : ptInd τ eV i (g • z) v = ptInd τ eV i z v := by
  unfold ptInd
  rw [hτ, Quotient.sound (mem_orbit z g : g • z ∈ orbit G z)]

include hτ hadj ha hb in

theorem walkCycle_mem_ribbonKernel (v₀ : W) (g : G) (p : 𝒯.Walk v₀ (g • v₀)) :
    walkCycle 𝒯 (fun e => (eE e).1) p ∈ ribbonKernel D := by
  rw [mem_ribbonKernel_iff_fibre_sum]
  refine ⟨fun v => ?_, fun v => ?_⟩
  · rw [sum_a_walkCycle 𝒯 τ hτ hadj D eE eV ha, ptInd_smul τ hτ, sub_self]
  · rw [sum_b_walkCycle 𝒯 τ hτ hadj D eE eV hb, ptInd_smul τ hτ, neg_add_cancel]

end Frame

section Tree

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
  (hT : 𝒯.IsTree) [DecidableEq (QuotEdge G 𝒯)] {E : Type} (orb : E → QuotEdge G 𝒯)

noncomputable def treePath (v₀ x : W) : 𝒯.Path v₀ x := somePath (hT.connected.preconnected v₀ x)

noncomputable def pot (v₀ x : W) : E → ℤ := walkCycle 𝒯 orb (treePath 𝒯 hT v₀ x : 𝒯.Walk v₀ x)

theorem pot_self (v₀ : W) : pot 𝒯 hT orb v₀ v₀ = 0 := by
  unfold pot
  rw [hT.isAcyclic.path_unique (treePath 𝒯 hT v₀ v₀) SimpleGraph.Path.nil]
  exact walkCycle_nil 𝒯 orb v₀

theorem pot_adj (v₀ : W) {u w : W} (h : 𝒯.Adj u w) :
    pot 𝒯 hT orb v₀ w = pot 𝒯 hT orb v₀ u +
      walkCycle 𝒯 orb (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil : 𝒯.Walk u w) := by
  classical
  unfold pot
  set P := treePath 𝒯 hT v₀ u with hP
  by_cases hw : w ∈ (P : 𝒯.Walk v₀ u).support
  · have hspec := SimpleGraph.Walk.take_spec (P : 𝒯.Walk v₀ u) hw
    have htake : (P : 𝒯.Walk v₀ u).takeUntil w hw = (treePath 𝒯 hT v₀ w : 𝒯.Walk v₀ w) :=
      congrArg Subtype.val (hT.isAcyclic.path_unique ⟨_, P.2.takeUntil hw⟩ (treePath 𝒯 hT v₀ w))
    have hdrop : (P : 𝒯.Walk v₀ u).dropUntil w hw =
        (SimpleGraph.Walk.cons h.symm SimpleGraph.Walk.nil : 𝒯.Walk w u) :=
      congrArg Subtype.val (hT.isAcyclic.path_unique ⟨_, P.2.dropUntil hw⟩ (SimpleGraph.Path.singleton h.symm))
    rw [← hspec, walkCycle_append, htake, hdrop]
    have hrev : (SimpleGraph.Walk.cons h.symm SimpleGraph.Walk.nil : 𝒯.Walk w u) =
        (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil : 𝒯.Walk u w).reverse := by
      simp
    rw [hrev, walkCycle_reverse]
    abel
  · have hpath : ((P : 𝒯.Walk v₀ u).concat h).IsPath := (SimpleGraph.Walk.concat_isPath_iff h).mpr ⟨P.2, hw⟩
    have := hT.isAcyclic.path_unique ⟨_, hpath⟩ (treePath 𝒯 hT v₀ w)
    rw [← congrArg Subtype.val this]
    show walkCycle 𝒯 orb ((P : 𝒯.Walk v₀ u).concat h) = _
    rw [SimpleGraph.Walk.concat_eq_append, walkCycle_append]

theorem walkCycle_eq_pot_sub_pot (v₀ : W) {x y : W} (p : 𝒯.Walk x y) :
    walkCycle 𝒯 orb p = pot 𝒯 hT orb v₀ y - pot 𝒯 hT orb v₀ x := by
  induction p with
  | nil => rw [walkCycle_nil, sub_self]
  | @cons u w z h p ih =>
    have : (SimpleGraph.Walk.cons h p : 𝒯.Walk u z) =
        (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil : 𝒯.Walk u w).append p := rfl
    rw [this, walkCycle_append, ih, pot_adj 𝒯 hT orb v₀ h]
    abel

theorem pathCycle_eq_pot (v₀ : W) (g : G) : pathCycle 𝒯 orb v₀ g = pot 𝒯 hT orb v₀ (g • v₀) :=
  pathCycle_eq_walkCycle 𝒯 orb hT.isAcyclic v₀ g (treePath 𝒯 hT v₀ (g • v₀))

theorem walkCycle_copy {u v u' v' : W} (p : 𝒯.Walk u v) (hu : u = u') (hv : v = v') :
    walkCycle 𝒯 orb (p.copy hu hv) = walkCycle 𝒯 orb p := by
  subst hu hv; rfl

include hT in

theorem pathCycle_mul (v₀ : W) (g h : G) :
    pathCycle 𝒯 orb v₀ (g * h) = pathCycle 𝒯 orb v₀ g + pathCycle 𝒯 orb v₀ h := by
  rw [pathCycle_eq_pot 𝒯 hT, pathCycle_eq_pot 𝒯 hT, pathCycle_eq_pot 𝒯 hT]
  have h1 := walkCycle_eq_pot_sub_pot 𝒯 hT orb v₀
    ((((treePath 𝒯 hT v₀ (h • v₀) : 𝒯.Walk v₀ (h • v₀)).map (smulHom g)).copy rfl (mul_smul g h v₀).symm))
  rw [walkCycle_copy, walkCycle_map_smulHom] at h1
  change pot 𝒯 hT orb v₀ (h • v₀) = _ at h1
  simp only [smulHom_apply] at h1
  rw [h1]
  abel

include hT in
theorem pathCycle_one (v₀ : W) : pathCycle 𝒯 orb v₀ 1 = 0 := by
  rw [pathCycle_eq_pot 𝒯 hT, one_smul, pot_self]

end Tree

end BS0

theorem solution
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hT : 𝒯.IsTree)
    (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
    [DecidableEq (QuotEdge G 𝒯)]
    {E V : Type} [Fintype E] [DecidableEq V] (D : DegeneracyData E V)
    (eE : E ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})
    (eV : V ≃ QuotVert G W)
    (ha : ∀ e : E, eV (D.a e) = Quotient.mk (orbitRel G W) (eE e).1.out.fst)
    (hb : ∀ e : E, eV (D.b e) = Quotient.mk (orbitRel G W) (eE e).1.out.snd)
    (v₀ : W) :
    ∃ φ : Additive (Abelianization G) →+ ↥(ribbonKernel D),
      ∀ g : G, (φ (Additive.ofMul (Abelianization.of g)) : E → ℤ) = pathCycle 𝒯 (fun e => (eE e).1) v₀ g := by
  classical
  have hmem : ∀ g : G, pathCycle 𝒯 (fun e => (eE e).1) v₀ g ∈ ribbonKernel D := fun g => by
    rw [BS0.pathCycle_eq_pot 𝒯 hT (fun e => (eE e).1) v₀ g]
    exact BS0.walkCycle_mem_ribbonKernel 𝒯 τ hτ hadj D eE eV ha hb v₀ g _
  let f : G →* Multiplicative ↥(ribbonKernel D) :=
    { toFun := fun g => Multiplicative.ofAdd ⟨pathCycle 𝒯 (fun e => (eE e).1) v₀ g, hmem g⟩
      map_one' := by
        change Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
        congr 1
        exact Subtype.ext (BS0.pathCycle_one 𝒯 hT (fun e => (eE e).1) v₀)
      map_mul' := fun g h => by
        change Multiplicative.ofAdd _ = Multiplicative.ofAdd (_ + _)
        congr 1
        exact Subtype.ext (BS0.pathCycle_mul 𝒯 hT (fun e => (eE e).1) v₀ g h) }
  refine ⟨MonoidHom.toAdditiveLeft (Abelianization.lift f), fun g => ?_⟩
  rw [MonoidHom.coe_toAdditiveLeft, Function.comp_apply, Function.comp_apply, toMul_ofMul,
    Abelianization.lift_apply_of]
  rfl

end S_CerednikDrinfeld_Mumford_exists_addMonoidHom_abelianization_ribbonKernel_apply_eq_pathCycle
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_exists_addMonoidHom_abelianization_ribbonKernel_apply_eq_pathCycle (solution)
