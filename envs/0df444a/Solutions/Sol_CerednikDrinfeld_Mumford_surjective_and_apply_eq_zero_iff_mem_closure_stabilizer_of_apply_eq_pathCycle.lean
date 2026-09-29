-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.surjective_and_apply_eq_zero_iff_mem_closure_stabilizer_of_apply_eq_pathCycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/6d571cf3-ede3-51c7-b3a4-660cbc7defde

import Mathlib
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_surjective_and_apply_eq_zero_iff_mem_closure_stabilizer_of_apply_eq_pathCycle

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

namespace P2mKcBassSerreH1

section Ribbon
variable {E V : Type} [Fintype E] [DecidableEq V]

theorem pushforward_apply (f : E → V) (x : E → ℤ) (v : V) :
    pushforward f x v = ∑ e : E, (if f e = v then x e else 0) := by
  simp only [pushforward, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, degeneracyMatrix, Matrix.of_apply,
    ite_mul, one_mul, zero_mul]

theorem mem_ribbonKernel_iff (D : DegeneracyData E V) (x : E → ℤ) :
    x ∈ ribbonKernel D ↔ pushforward D.a x = 0 ∧ pushforward D.b x = 0 := by
  rw [mem_ribbonKernel]
  constructor
  · intro h; exact ⟨h 0, h 1⟩
  · rintro ⟨h0, h1⟩ i
    fin_cases i
    · exact h0
    · exact h1

theorem pushforward_single [DecidableEq E] (f : E → V) (e₀ : E) (c : ℤ) :
    pushforward f (fun e => if e = e₀ then c else 0) = fun v => if f e₀ = v then c else 0 := by
  funext v
  rw [pushforward_apply]
  rw [Finset.sum_eq_single e₀ (fun e _ hne => by rw [if_neg hne, ite_self]) (fun h => absurd (Finset.mem_univ e₀) h)]
  rw [if_pos rfl]

theorem sum_zsmul_comp_eq {M : Type} [AddCommGroup M] (f : E → V) (z : E → ℤ) (P : V → M) :
    ∑ e, z e • P (f e) = ∑ v ∈ Finset.univ.image f, (pushforward f z v) • P v := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image f) (g := f)
    (fun e he => Finset.mem_image_of_mem f he)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [pushforward_apply, Finset.sum_smul, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h : f e = v
  · rw [if_pos h, if_pos h, h]
  · rw [if_neg h, if_neg h, zero_smul]

theorem sum_zsmul_comp_eq_zero {M : Type} [AddCommGroup M] (f : E → V) (z : E → ℤ) (P : V → M)
    (hz : pushforward f z = 0) : ∑ e, z e • P (f e) = 0 := by
  rw [sum_zsmul_comp_eq f z P]
  exact Finset.sum_eq_zero fun v _ => by rw [hz, Pi.zero_apply, zero_smul]

theorem sum_zsmul_single [DecidableEq E] (z : E → ℤ) :
    ∑ e, z e • (fun e' => if e' = e then (1 : ℤ) else 0) = z := by
  funext e'
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ e' z, if_pos (Finset.mem_univ _)]

end Ribbon

section Crossing
variable {W : Type} (𝒯 : SimpleGraph W)

open Classical in

noncomputable def dartSign (d₀ d : 𝒯.Dart) : ℤ :=
  (if d = d₀ then 1 else 0) - (if d = d₀.symm then 1 else 0)

noncomputable def cross (d₀ : 𝒯.Dart) {x y : W} (p : 𝒯.Walk x y) : ℤ :=
  (p.darts.map (dartSign 𝒯 d₀)).sum

open Classical in

noncomputable def side (d₀ : 𝒯.Dart) (x : W) : ℤ :=
  if (𝒯.deleteEdges {d₀.edge}).Reachable d₀.fst x then 1 else 0

theorem side_fst (d₀ : 𝒯.Dart) : side 𝒯 d₀ d₀.fst = 1 := by
  rw [side, if_pos (SimpleGraph.Reachable.refl _)]

theorem side_snd (hac : 𝒯.IsAcyclic) (d₀ : 𝒯.Dart) : side 𝒯 d₀ d₀.snd = 0 := by
  have hb := SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hac d₀.adj
  rw [SimpleGraph.isBridge_iff] at hb
  rw [side, if_neg]
  exact hb

theorem side_eq_of_adj (d₀ : 𝒯.Dart) {x x' : W} (h : 𝒯.Adj x x') (hne : s(x, x') ≠ d₀.edge) :
    side 𝒯 d₀ x = side 𝒯 d₀ x' := by
  have hadj' : (𝒯.deleteEdges {d₀.edge}).Adj x x' := by
    rw [SimpleGraph.deleteEdges_adj]
    exact ⟨h, by rwa [Set.mem_singleton_iff]⟩
  simp only [side]
  by_cases hx : (𝒯.deleteEdges {d₀.edge}).Reachable d₀.fst x
  · rw [if_pos hx, if_pos (hx.trans hadj'.reachable)]
  · rw [if_neg hx, if_neg (fun hx' => hx (hx'.trans hadj'.symm.reachable))]

theorem dartSign_eq (hac : 𝒯.IsAcyclic) (d₀ d : 𝒯.Dart) :
    dartSign 𝒯 d₀ d = side 𝒯 d₀ d.fst - side 𝒯 d₀ d.snd := by
  unfold dartSign
  by_cases h1 : d = d₀
  · subst h1
    rw [if_pos rfl, if_neg (fun h => d.symm_ne h.symm), side_fst, side_snd 𝒯 hac]
  · rw [if_neg h1]
    by_cases h2 : d = d₀.symm
    · subst h2
      rw [if_pos rfl]
      change (0 : ℤ) - 1 = side 𝒯 d₀ d₀.snd - side 𝒯 d₀ d₀.fst
      rw [side_fst, side_snd 𝒯 hac]
    · rw [if_neg h2, sub_zero]
      have hne : d.edge ≠ d₀.edge := fun h => ((SimpleGraph.dart_edge_eq_iff d d₀).mp h).elim h1 h2
      rw [side_eq_of_adj 𝒯 d₀ d.adj hne, sub_self]

theorem cross_eq (hac : 𝒯.IsAcyclic) (d₀ : 𝒯.Dart) {x y : W} (p : 𝒯.Walk x y) :
    cross 𝒯 d₀ p = side 𝒯 d₀ x - side 𝒯 d₀ y := by
  induction p with
  | nil => simp [cross]
  | cons h p ih =>
    simp only [cross, SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, dartSign_eq 𝒯 hac]
    abel

theorem cross_eq_zero_of_closed (hac : 𝒯.IsAcyclic) (d₀ : 𝒯.Dart) {x : W} (c : 𝒯.Walk x x) :
    cross 𝒯 d₀ c = 0 := by
  rw [cross_eq 𝒯 hac, sub_self]

end Crossing

section ChainInv
variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
  [DecidableEq (QuotEdge G 𝒯)]

theorem dartIndex_eq_sum (q : QuotEdge G 𝒯) (F : Finset 𝒯.Dart) (d : 𝒯.Dart) (hd : d ∈ F)
    (hds : d.symm ∈ F) :
    dartIndex 𝒯 q d
      = ∑ d₀ ∈ F, (if Quotient.mk (orbitRel G 𝒯.Dart) d₀ = q then (1 : ℤ) else 0) * dartSign 𝒯 d₀ d := by
  classical
  simp only [dartSign, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  have h1 : ∑ d₀ ∈ F, (if d = d₀ then (if Quotient.mk (orbitRel G 𝒯.Dart) d₀ = q then (1 : ℤ) else 0) else 0)
      = if Quotient.mk (orbitRel G 𝒯.Dart) d = q then 1 else 0 := by
    rw [Finset.sum_ite_eq F d, if_pos hd]
  have h2 : ∑ d₀ ∈ F,
      (if d = d₀.symm then (if Quotient.mk (orbitRel G 𝒯.Dart) d₀ = q then (1 : ℤ) else 0) else 0)
      = if Quotient.mk (orbitRel G 𝒯.Dart) d.symm = q then 1 else 0 := by
    have : ∀ d₀ : 𝒯.Dart, (d = d₀.symm) = (d.symm = d₀) := fun d₀ =>
      propext ⟨fun h => by rw [h, SimpleGraph.Dart.symm_symm], fun h => by rw [← h, SimpleGraph.Dart.symm_symm]⟩
    simp_rw [this]
    rw [Finset.sum_ite_eq F d.symm, if_pos hds]
  rw [h1, h2]
  rfl

theorem list_sum_dartIndex (q : QuotEdge G 𝒯) (L : List 𝒯.Dart) (F : Finset 𝒯.Dart)
    (hF : ∀ d ∈ L, d ∈ F ∧ d.symm ∈ F) :
    (L.map (dartIndex 𝒯 q)).sum
      = ∑ d₀ ∈ F, (if Quotient.mk (orbitRel G 𝒯.Dart) d₀ = q then (1 : ℤ) else 0) * (L.map (dartSign 𝒯 d₀)).sum := by
  induction L with
  | nil => simp
  | cons d L ih =>
    rw [List.map_cons, List.sum_cons, ih (fun d' hd' => hF d' (List.mem_cons_of_mem d hd'))]
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib]
    rw [dartIndex_eq_sum 𝒯 q F d (hF d List.mem_cons_self).1 (hF d List.mem_cons_self).2]

theorem walkCycle_eq_zero_of_closed (hac : 𝒯.IsAcyclic) {E : Type} (orb : E → QuotEdge G 𝒯) {x : W}
    (c : 𝒯.Walk x x) : walkCycle 𝒯 orb c = 0 := by
  classical
  funext e
  let F : Finset 𝒯.Dart := (c.darts ++ c.darts.map SimpleGraph.Dart.symm).toFinset
  have hF : ∀ d ∈ c.darts, d ∈ F ∧ d.symm ∈ F := fun d hd =>
    ⟨List.mem_toFinset.mpr (List.mem_append_left _ hd),
     List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_map.mpr ⟨d, hd, rfl⟩))⟩
  change (c.darts.map (dartIndex 𝒯 (orb e))).sum = 0
  rw [list_sum_dartIndex 𝒯 (orb e) c.darts F hF]
  refine Finset.sum_eq_zero fun d₀ _ => ?_
  rw [show (c.darts.map (dartSign 𝒯 d₀)).sum = cross 𝒯 d₀ c from rfl, cross_eq_zero_of_closed 𝒯 hac,
    mul_zero]

theorem walkCycle_eq_of_isAcyclic (hac : 𝒯.IsAcyclic) {E : Type} (orb : E → QuotEdge G 𝒯) {x y : W}
    (p q : 𝒯.Walk x y) : walkCycle 𝒯 orb p = walkCycle 𝒯 orb q := by
  have h := walkCycle_eq_zero_of_closed 𝒯 hac orb (p.append q.reverse)
  rw [walkCycle_append, walkCycle_reverse, ← sub_eq_add_neg, sub_eq_zero] at h
  exact h

theorem walkCycle_copy {E : Type} (orb : E → QuotEdge G 𝒯) {u v u' v' : W} (p : 𝒯.Walk u v)
    (hu : u = u') (hv : v = v') : walkCycle 𝒯 orb (p.copy hu hv) = walkCycle 𝒯 orb p := by
  subst hu hv
  rfl

theorem pathCycle_eq_walkCycle' (hT : 𝒯.IsTree) {E : Type} (orb : E → QuotEdge G 𝒯) (v₀ : W) (g : G)
    (p : 𝒯.Walk v₀ (g • v₀)) : pathCycle 𝒯 orb v₀ g = walkCycle 𝒯 orb p := by
  rw [pathCycle, dif_pos p.reachable]
  exact walkCycle_eq_of_isAcyclic 𝒯 hT.isAcyclic orb _ _

theorem pathCycle_one (hT : 𝒯.IsTree) {E : Type} (orb : E → QuotEdge G 𝒯) (v₀ : W) :
    pathCycle 𝒯 orb v₀ (1 : G) = 0 := by
  rw [pathCycle_eq_walkCycle' 𝒯 hT orb v₀ 1 ((SimpleGraph.Walk.nil : 𝒯.Walk v₀ v₀).copy rfl (one_smul G v₀).symm),
    walkCycle_copy, walkCycle_nil]

theorem pathCycle_mul (hT : 𝒯.IsTree) {E : Type} (orb : E → QuotEdge G 𝒯) (v₀ : W) (g k : G) :
    pathCycle 𝒯 orb v₀ (g * k) = pathCycle 𝒯 orb v₀ g + pathCycle 𝒯 orb v₀ k := by
  let pg : 𝒯.Walk v₀ (g • v₀) := (hT.connected.preconnected v₀ (g • v₀)).some
  let pk : 𝒯.Walk v₀ (k • v₀) := (hT.connected.preconnected v₀ (k • v₀)).some
  let pk' : 𝒯.Walk (g • v₀) (g • k • v₀) := (pk.map (smulHom g)).copy (smulHom_apply 𝒯 g v₀)
    (smulHom_apply 𝒯 g (k • v₀))
  let q : 𝒯.Walk v₀ ((g * k) • v₀) := (pg.append pk').copy rfl (mul_smul g k v₀).symm
  rw [pathCycle_eq_walkCycle' 𝒯 hT orb v₀ (g * k) q, walkCycle_copy, walkCycle_append, walkCycle_copy,
    walkCycle_map_smulHom, ← pathCycle_eq_walkCycle' 𝒯 hT orb v₀ g pg,
    ← pathCycle_eq_walkCycle' 𝒯 hT orb v₀ k pk]

end ChainInv

section Coord
variable (G : Type) [Group G] {W : Type} [MulAction G W]

theorem exists_smul_out_mk (w : W) : ∃ x : G, x • (Quotient.mk (orbitRel G W) w).out = w := by
  have h : (Quotient.mk (orbitRel G W) w).out ∈ orbit G w := orbitRel_apply.mp (Quotient.mk_out w)
  obtain ⟨k, hk⟩ := mem_orbit_iff.mp h
  exact ⟨k⁻¹, by rw [← hk, inv_smul_smul]⟩

noncomputable def coord (w : W) : G := (exists_smul_out_mk G w).choose

theorem coord_spec (w : W) : coord G w • (Quotient.mk (orbitRel G W) w).out = w :=
  (exists_smul_out_mk G w).choose_spec

variable {G}

theorem coord_unique (hfree : ∀ w : W, stabilizer G w = ⊥) {w : W} {x : G}
    (hx : x • (Quotient.mk (orbitRel G W) w).out = w) : x = coord G w := by
  have h2 := coord_spec G w
  have hmem : (coord G w)⁻¹ * x ∈ stabilizer G (Quotient.mk (orbitRel G W) w).out := by
    rw [mem_stabilizer_iff, mul_smul, hx, inv_smul_eq_iff]
    exact h2.symm
  rw [hfree, Subgroup.mem_bot] at hmem
  exact (inv_mul_eq_one.mp hmem).symm

theorem quotVert_mk_smul (k : G) (w : W) :
    Quotient.mk (orbitRel G W) (k • w) = Quotient.mk (orbitRel G W) w :=
  Quotient.sound (mem_orbit w k)

theorem coord_smul (hfree : ∀ w : W, stabilizer G w = ⊥) (k : G) (w : W) :
    coord G (k • w) = k * coord G w := by
  symm
  apply coord_unique hfree
  rw [quotVert_mk_smul, mul_smul, coord_spec]

variable (G) (𝒯 : SimpleGraph W) [GraphAction G 𝒯]

noncomputable def lab (d : 𝒯.Dart) : G := (coord G d.fst)⁻¹ * coord G d.snd

variable {G}

theorem lab_smul (hfree : ∀ w : W, stabilizer G w = ⊥) (k : G) (d : 𝒯.Dart) :
    lab G 𝒯 (k • d) = lab G 𝒯 d := by
  simp only [lab, smul_dart_fst, smul_dart_snd, coord_smul hfree, mul_inv_rev]
  rw [mul_assoc, inv_mul_cancel_left]

theorem lab_symm (d : 𝒯.Dart) : lab G 𝒯 d.symm = (lab G 𝒯 d)⁻¹ := by
  change (coord G d.snd)⁻¹ * coord G d.fst = ((coord G d.fst)⁻¹ * coord G d.snd)⁻¹
  rw [mul_inv_rev, inv_inv]

theorem lab_out_mk (hfree : ∀ w : W, stabilizer G w = ⊥) (d : 𝒯.Dart) :
    lab G 𝒯 (Quotient.mk (orbitRel G 𝒯.Dart) d).out = lab G 𝒯 d := by
  obtain ⟨k, hk⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.mk_out (s := orbitRel G 𝒯.Dart) d))
  rw [← hk, lab_smul 𝒯 hfree]

end Coord

section Datum
variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
  (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
  [DecidableEq (QuotEdge G 𝒯)]
  {E V : Type} [Fintype E] [DecidableEq V] (D : DegeneracyData E V)
  (eE : E ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})
  (eV : V ≃ QuotVert G W)

theorem zmod2_eq_zero_of_ne_of_ne_zero : ∀ a b : ZMod 2, a ≠ b → a ≠ 0 → b = 0 := by decide

include hτ in
theorem τ_out_fst_mk (d : 𝒯.Dart) : τ (Quotient.mk (orbitRel G 𝒯.Dart) d).out.fst = τ d.fst := by
  have h : (Quotient.mk (orbitRel G 𝒯.Dart) d).out ∈ orbit G d := orbitRel_apply.mp (Quotient.mk_out d)
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp h
  rw [← hg, smul_dart_fst, hτ]

include hadj in
theorem τ_snd_eq_zero (d : 𝒯.Dart) (h : τ d.fst ≠ 0) : τ d.snd = 0 :=
  zmod2_eq_zero_of_ne_of_ne_zero _ _ (hadj _ _ d.adj) h

include hadj in
theorem τ_snd_ne_zero (d : 𝒯.Dart) (h : τ d.fst = 0) : τ d.snd ≠ 0 :=
  fun h' => hadj _ _ d.adj (h.trans h'.symm)

noncomputable def eOf (d : 𝒯.Dart) (h : τ d.fst = 0) : E :=
  eE.symm ⟨Quotient.mk (orbitRel G 𝒯.Dart) d, by rw [τ_out_fst_mk 𝒯 τ hτ]; exact h⟩

theorem eE_eOf (d : 𝒯.Dart) (h : τ d.fst = 0) :
    (eE (eOf 𝒯 τ hτ eE d h)).1 = Quotient.mk (orbitRel G 𝒯.Dart) d := by
  simp [eOf]

theorem eOf_eq_iff (d : 𝒯.Dart) (h : τ d.fst = 0) (e : E) :
    eOf 𝒯 τ hτ eE d h = e ↔ Quotient.mk (orbitRel G 𝒯.Dart) d = (eE e).1 := by
  constructor
  · rintro rfl; exact (eE_eOf 𝒯 τ hτ eE d h).symm
  · intro hq
    apply eE.injective
    exact Subtype.ext ((eE_eOf 𝒯 τ hτ eE d h).trans hq)

theorem eOf_smul (k : G) (d : 𝒯.Dart) (h : τ d.fst = 0) (h' : τ (k • d).fst = 0) :
    eOf 𝒯 τ hτ eE (k • d) h' = eOf 𝒯 τ hτ eE d h := by
  unfold eOf
  congr 1
  exact Subtype.ext (quotEdge_mk_smul 𝒯 k d)

theorem eOf_out (e : E) : eOf 𝒯 τ hτ eE (eE e).1.out (eE e).2 = e := by
  apply eE.injective
  apply Subtype.ext
  rw [eE_eOf, Quotient.out_eq]

noncomputable def dartChain (d : 𝒯.Dart) : E → ℤ := fun e => dartIndex 𝒯 (eE e).1 d

theorem walkCycle_cons' {u v w : W} (h : 𝒯.Adj u v) (p : 𝒯.Walk v w) :
    walkCycle 𝒯 (fun e => (eE e).1) (SimpleGraph.Walk.cons h p)
      = dartChain 𝒯 τ eE ⟨(u, v), h⟩ + walkCycle 𝒯 (fun e => (eE e).1) p :=
  funext fun e => walkCycle_cons 𝒯 (fun e => (eE e).1) h p e

theorem dartChain_smul (k : G) (d : 𝒯.Dart) : dartChain 𝒯 τ eE (k • d) = dartChain 𝒯 τ eE d :=
  funext fun e => dartIndex_smul 𝒯 (eE e).1 k d

include hadj in

theorem dartChain_of_eq_zero [DecidableEq E] (d : 𝒯.Dart) (h0 : τ d.fst = 0) :
    dartChain 𝒯 τ eE d = fun e => if e = eOf 𝒯 τ hτ eE d h0 then 1 else 0 := by
  funext e
  unfold dartChain dartIndex
  have hne : ¬ Quotient.mk (orbitRel G 𝒯.Dart) d.symm = (eE e).1 := by
    intro hq
    have h2 := (eE e).2
    rw [← hq, τ_out_fst_mk 𝒯 τ hτ] at h2
    exact τ_snd_ne_zero 𝒯 τ hadj d h0 h2
  rw [if_neg hne, sub_zero]
  by_cases he : e = eOf 𝒯 τ hτ eE d h0
  · rw [if_pos he, if_pos (((eOf_eq_iff 𝒯 τ hτ eE d h0 e).mp he.symm))]
  · rw [if_neg he, if_neg (fun hq => he ((eOf_eq_iff 𝒯 τ hτ eE d h0 e).mpr hq).symm)]

include hadj in

theorem dartChain_of_ne_zero [DecidableEq E] (d : 𝒯.Dart) (h1 : τ d.fst ≠ 0) :
    dartChain 𝒯 τ eE d
      = fun e => if e = eOf 𝒯 τ hτ eE d.symm (τ_snd_eq_zero 𝒯 τ hadj d h1) then -1 else 0 := by
  funext e
  unfold dartChain dartIndex
  have hne : ¬ Quotient.mk (orbitRel G 𝒯.Dart) d = (eE e).1 := by
    intro hq
    have h2 := (eE e).2
    rw [← hq, τ_out_fst_mk 𝒯 τ hτ] at h2
    exact h1 h2
  rw [if_neg hne, zero_sub]
  by_cases he : e = eOf 𝒯 τ hτ eE d.symm (τ_snd_eq_zero 𝒯 τ hadj d h1)
  · rw [if_pos he, if_pos (((eOf_eq_iff 𝒯 τ hτ eE d.symm _ e).mp he.symm))]
  · rw [if_neg he, if_neg (fun hq => he ((eOf_eq_iff 𝒯 τ hτ eE d.symm _ e).mpr hq).symm), neg_zero]

variable (ha : ∀ e : E, eV (D.a e) = Quotient.mk (orbitRel G W) (eE e).1.out.fst)
  (hb : ∀ e : E, eV (D.b e) = Quotient.mk (orbitRel G W) (eE e).1.out.snd)

theorem quotVert_mk_out_fst (d : 𝒯.Dart) :
    Quotient.mk (orbitRel G W) (Quotient.mk (orbitRel G 𝒯.Dart) d).out.fst = Quotient.mk (orbitRel G W) d.fst := by
  obtain ⟨k, hk⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.mk_out (s := orbitRel G 𝒯.Dart) d))
  rw [← hk, smul_dart_fst]
  exact Quotient.sound (mem_orbit _ k)

theorem quotVert_mk_out_snd (d : 𝒯.Dart) :
    Quotient.mk (orbitRel G W) (Quotient.mk (orbitRel G 𝒯.Dart) d).out.snd = Quotient.mk (orbitRel G W) d.snd := by
  obtain ⟨k, hk⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.mk_out (s := orbitRel G 𝒯.Dart) d))
  rw [← hk, smul_dart_snd]
  exact Quotient.sound (mem_orbit _ k)

include ha in
theorem a_eOf_eq_iff (d : 𝒯.Dart) (h0 : τ d.fst = 0) (v : V) :
    D.a (eOf 𝒯 τ hτ eE d h0) = v ↔ eV v = Quotient.mk (orbitRel G W) d.fst := by
  rw [← eV.apply_eq_iff_eq, ha, eE_eOf, quotVert_mk_out_fst]
  exact eq_comm

include hb in
theorem b_eOf_eq_iff (d : 𝒯.Dart) (h0 : τ d.fst = 0) (v : V) :
    D.b (eOf 𝒯 τ hτ eE d h0) = v ↔ eV v = Quotient.mk (orbitRel G W) d.snd := by
  rw [← eV.apply_eq_iff_eq, hb, eE_eOf, quotVert_mk_out_snd]
  exact eq_comm

open Classical in

noncomputable def Ba (w : W) : V → ℤ :=
  fun v => if τ w = 0 ∧ eV v = Quotient.mk (orbitRel G W) w then 1 else 0

open Classical in

noncomputable def Bb (w : W) : V → ℤ :=
  fun v => if τ w ≠ 0 ∧ eV v = Quotient.mk (orbitRel G W) w then 1 else 0

include hτ in
theorem Ba_smul (k : G) (w : W) : Ba τ eV (k • w) = Ba τ eV w := by
  funext v
  unfold Ba
  rw [hτ, quotVert_mk_smul]

include hτ in
theorem Bb_smul (k : G) (w : W) : Bb τ eV (k • w) = Bb τ eV w := by
  funext v
  unfold Bb
  rw [hτ, quotVert_mk_smul]

include hτ hadj ha in
theorem pushforward_a_dartChain (d : 𝒯.Dart) :
    pushforward D.a (dartChain 𝒯 τ eE d) = Ba τ eV d.fst - Ba τ eV d.snd := by
  classical
  funext v
  by_cases h0 : τ d.fst = 0
  · have h1 : τ d.snd ≠ 0 := τ_snd_ne_zero 𝒯 τ hadj d h0
    rw [dartChain_of_eq_zero 𝒯 τ hτ hadj eE d h0, pushforward_single]
    simp only [Ba, Pi.sub_apply, h0, h1, true_and, false_and, if_false, sub_zero]
    by_cases hv : eV v = Quotient.mk (orbitRel G W) d.fst
    · rw [if_pos ((a_eOf_eq_iff 𝒯 τ hτ D eE eV ha d h0 v).mpr hv), if_pos hv]
    · rw [if_neg (fun h => hv ((a_eOf_eq_iff 𝒯 τ hτ D eE eV ha d h0 v).mp h)), if_neg hv]
  · have h1 : τ d.snd = 0 := τ_snd_eq_zero 𝒯 τ hadj d h0
    rw [dartChain_of_ne_zero 𝒯 τ hτ hadj eE d h0, pushforward_single]
    simp only [Ba, Pi.sub_apply, h0, h1, true_and, false_and, if_false, zero_sub]
    by_cases hv : eV v = Quotient.mk (orbitRel G W) d.snd
    · rw [if_pos ((a_eOf_eq_iff 𝒯 τ hτ D eE eV ha d.symm h1 v).mpr hv), if_pos hv]
    · rw [if_neg (fun h => hv ((a_eOf_eq_iff 𝒯 τ hτ D eE eV ha d.symm h1 v).mp h)), if_neg hv, neg_zero]

include hτ hadj hb in
theorem pushforward_b_dartChain (d : 𝒯.Dart) :
    pushforward D.b (dartChain 𝒯 τ eE d) = Bb τ eV d.snd - Bb τ eV d.fst := by
  classical
  funext v
  by_cases h0 : τ d.fst = 0
  · have h1 : τ d.snd ≠ 0 := τ_snd_ne_zero 𝒯 τ hadj d h0
    rw [dartChain_of_eq_zero 𝒯 τ hτ hadj eE d h0, pushforward_single]
    simp only [Bb, Pi.sub_apply, h0, h1, ne_eq, not_true_eq_false, not_false_eq_true, true_and, false_and,
      if_false, sub_zero]
    by_cases hv : eV v = Quotient.mk (orbitRel G W) d.snd
    · rw [if_pos ((b_eOf_eq_iff 𝒯 τ hτ D eE eV hb d h0 v).mpr hv), if_pos hv]
    · rw [if_neg (fun h => hv ((b_eOf_eq_iff 𝒯 τ hτ D eE eV hb d h0 v).mp h)), if_neg hv]
  · have h1 : τ d.snd = 0 := τ_snd_eq_zero 𝒯 τ hadj d h0
    rw [dartChain_of_ne_zero 𝒯 τ hτ hadj eE d h0, pushforward_single]
    simp only [Bb, Pi.sub_apply, h0, h1, ne_eq, not_true_eq_false, not_false_eq_true, true_and, false_and,
      if_false, zero_sub]
    by_cases hv : eV v = Quotient.mk (orbitRel G W) d.fst
    · rw [if_pos ((b_eOf_eq_iff 𝒯 τ hτ D eE eV hb d.symm h1 v).mpr hv), if_pos hv]
    · rw [if_neg (fun h => hv ((b_eOf_eq_iff 𝒯 τ hτ D eE eV hb d.symm h1 v).mp h)), if_neg hv, neg_zero]

include hτ hadj ha in

theorem pushforward_a_walkCycle {x y : W} (p : 𝒯.Walk x y) :
    pushforward D.a (walkCycle 𝒯 (fun e => (eE e).1) p) = Ba τ eV x - Ba τ eV y := by
  induction p with
  | nil => rw [walkCycle_nil, map_zero, sub_self]
  | cons h p ih =>
    rw [walkCycle_cons' 𝒯 τ eE, map_add, ih, pushforward_a_dartChain 𝒯 τ hτ hadj D eE eV ha]
    exact sub_add_sub_cancel _ _ _

include hτ hadj hb in

theorem pushforward_b_walkCycle {x y : W} (p : 𝒯.Walk x y) :
    pushforward D.b (walkCycle 𝒯 (fun e => (eE e).1) p) = Bb τ eV y - Bb τ eV x := by
  induction p with
  | nil => rw [walkCycle_nil, map_zero, sub_self]
  | cons h p ih =>
    rw [walkCycle_cons' 𝒯 τ eE, map_add, ih, pushforward_b_dartChain 𝒯 τ hτ hadj D eE eV hb]
    abel

include hτ hadj ha hb in

theorem pathCycle_mem (v₀ : W) (g : G) : pathCycle 𝒯 (fun e => (eE e).1) v₀ g ∈ ribbonKernel D := by
  unfold pathCycle
  by_cases hr : 𝒯.Reachable v₀ (g • v₀)
  · rw [dif_pos hr, mem_ribbonKernel_iff]
    constructor
    · rw [pushforward_a_walkCycle 𝒯 τ hτ hadj D eE eV ha, Ba_smul τ hτ, sub_self]
    · rw [pushforward_b_walkCycle 𝒯 τ hτ hadj D eE eV hb, Bb_smul τ hτ, sub_self]
  · rw [dif_neg hr]
    exact zero_mem _

end Datum

section Theta
variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
  (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
  [DecidableEq (QuotEdge G 𝒯)]
  {E V : Type} [Fintype E] [DecidableEq V] (D : DegeneracyData E V)
  (eE : E ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})
  (eV : V ≃ QuotVert G W)

noncomputable def gen (e : E) : G := lab G 𝒯 (eE e).1.out

noncomputable def γ (e : E) : Additive (Abelianization G) := Additive.ofMul (Abelianization.of (gen 𝒯 τ eE e))

noncomputable def Theta : (E → ℤ) →+ Additive (Abelianization G) where
  toFun x := ∑ e, x e • γ 𝒯 τ eE e
  map_zero' := by simp
  map_add' x y := by
    simp only [Pi.add_apply, add_zsmul]
    exact Finset.sum_add_distrib

theorem Theta_apply (x : E → ℤ) : Theta 𝒯 τ eE x = ∑ e, x e • γ 𝒯 τ eE e := rfl

theorem Theta_single [DecidableEq E] (e₀ : E) (c : ℤ) :
    Theta 𝒯 τ eE (fun e => if e = e₀ then c else 0) = c • γ 𝒯 τ eE e₀ := by
  rw [Theta_apply]
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

include hτ hadj in

theorem Theta_dartChain (hfree : ∀ w : W, stabilizer G w = ⊥) (d : 𝒯.Dart) :
    Theta 𝒯 τ eE (dartChain 𝒯 τ eE d) = Additive.ofMul (Abelianization.of (lab G 𝒯 d)) := by
  classical
  by_cases h0 : τ d.fst = 0
  · rw [dartChain_of_eq_zero 𝒯 τ hτ hadj eE d h0, Theta_single, one_zsmul]
    unfold γ gen
    rw [eE_eOf, lab_out_mk 𝒯 hfree]
  · rw [dartChain_of_ne_zero 𝒯 τ hτ hadj eE d h0, Theta_single, neg_one_zsmul]
    unfold γ gen
    rw [eE_eOf, lab_out_mk 𝒯 hfree, lab_symm, map_inv, ofMul_inv, neg_neg]

include hτ hadj in

theorem Theta_walkCycle (hfree : ∀ w : W, stabilizer G w = ⊥) {x y : W} (p : 𝒯.Walk x y) :
    Theta 𝒯 τ eE (walkCycle 𝒯 (fun e => (eE e).1) p)
      = Additive.ofMul (Abelianization.of ((coord G x)⁻¹ * coord G y)) := by
  induction p with
  | nil => rw [walkCycle_nil, map_zero, inv_mul_cancel, map_one, ofMul_one]
  | cons h p ih =>
    rw [walkCycle_cons' 𝒯 τ eE, map_add, ih, Theta_dartChain 𝒯 τ hτ hadj eE hfree, ← ofMul_mul, ← map_mul]
    unfold lab
    congr 2
    change (coord G _)⁻¹ * coord G _ * ((coord G _)⁻¹ * coord G _) = _
    rw [mul_assoc, mul_inv_cancel_left]

include hτ hadj in

theorem Theta_pathCycle (hT : 𝒯.IsTree) (hfree : ∀ w : W, stabilizer G w = ⊥) (v₀ : W) (g : G) :
    Theta 𝒯 τ eE (pathCycle 𝒯 (fun e => (eE e).1) v₀ g) = Additive.ofMul (Abelianization.of g) := by
  let p : 𝒯.Walk v₀ (g • v₀) := (hT.connected.preconnected v₀ (g • v₀)).some
  rw [pathCycle_eq_walkCycle' 𝒯 hT _ v₀ g p, Theta_walkCycle 𝒯 τ hτ hadj eE hfree, coord_smul hfree]
  congr 1
  rw [map_mul, map_mul, map_inv, mul_comm (Abelianization.of g), inv_mul_cancel_left]

variable (ha : ∀ e : E, eV (D.a e) = Quotient.mk (orbitRel G W) (eE e).1.out.fst)
  (hb : ∀ e : E, eV (D.b e) = Quotient.mk (orbitRel G W) (eE e).1.out.snd)

include hτ hadj ha hb in

theorem pathCycle_gen_aux [DecidableEq E] (hT : 𝒯.IsTree) (v₀ : W) (e : E)
    (P₁ : 𝒯.Walk v₀ (eV (D.a e)).out) (P₂ : 𝒯.Walk v₀ (eV (D.b e)).out) :
    pathCycle 𝒯 (fun e => (eE e).1) v₀ (gen 𝒯 τ eE e)
      = (fun e' => if e' = e then 1 else 0) + walkCycle 𝒯 (fun e => (eE e).1) P₁
          - walkCycle 𝒯 (fun e => (eE e).1) P₂ := by

  set d : 𝒯.Dart := (eE e).1.out with hd
  set x : G := coord G d.fst with hxdef
  set y : G := coord G d.snd with hydef
  have hgen : gen 𝒯 τ eE e = x⁻¹ * y := rfl
  set g : G := gen 𝒯 τ eE e with hgdef
  set so : W := (Quotient.mk (orbitRel G W) d.fst).out with hso_def
  set st : W := (Quotient.mk (orbitRel G W) d.snd).out with hst_def
  have hx : x • so = d.fst := coord_spec G d.fst
  have hy : y • st = d.snd := coord_spec G d.snd
  have hso : so = x⁻¹ • d.fst := by rw [← hx, inv_smul_smul]
  have hst : g • st = x⁻¹ • d.snd := by rw [hgen, mul_smul, hy]

  have hadj' : 𝒯.Adj so (g • st) := by rw [hso, hst]; exact GraphAction.smul_adj x⁻¹ d.adj
  have hd' : (⟨(so, g • st), hadj'⟩ : 𝒯.Dart) = x⁻¹ • d :=
    SimpleGraph.Dart.ext _ _ (Prod.ext hso hst)

  have ho : (eV (D.a e)).out = so := by rw [hso_def, ha e]
  have ht : (eV (D.b e)).out = st := by rw [hst_def, hb e]
  rw [pathCycle_eq_walkCycle' 𝒯 hT _ v₀ g
      ((P₁.copy rfl ho).append (SimpleGraph.Walk.cons hadj'
        (((P₂.copy rfl ht).reverse.map (smulHom g)).copy (smulHom_apply 𝒯 g st) (smulHom_apply 𝒯 g v₀)))),
    walkCycle_append, walkCycle_cons' 𝒯 τ eE, hd', dartChain_smul, walkCycle_copy, walkCycle_copy,
    walkCycle_map_smulHom, walkCycle_reverse, walkCycle_copy, dartChain_of_eq_zero 𝒯 τ hτ hadj eE d (eE e).2,
    eOf_out]
  abel

noncomputable def Pv (hT : 𝒯.IsTree) (v₀ : W) (v : V) : E → ℤ :=
  walkCycle 𝒯 (fun e => (eE e).1) ((hT.connected.preconnected v₀ (eV v).out).some)

include hτ hadj ha hb in

theorem pathCycle_gen [DecidableEq E] (hT : 𝒯.IsTree) (v₀ : W) (e : E) :
    pathCycle 𝒯 (fun e => (eE e).1) v₀ (gen 𝒯 τ eE e)
      = (fun e' => if e' = e then 1 else 0) + Pv 𝒯 τ eE eV hT v₀ (D.a e) - Pv 𝒯 τ eE eV hT v₀ (D.b e) :=
  pathCycle_gen_aux 𝒯 τ hτ hadj D eE eV ha hb hT v₀ e _ _

include hτ hadj ha hb in

theorem sum_zsmul_pathCycle_gen (hT : 𝒯.IsTree) (v₀ : W) (z : E → ℤ) (hz : z ∈ ribbonKernel D) :
    ∑ e, z e • pathCycle 𝒯 (fun e => (eE e).1) v₀ (gen 𝒯 τ eE e) = z := by
  classical
  obtain ⟨hza, hzb⟩ := (mem_ribbonKernel_iff D z).mp hz
  simp_rw [pathCycle_gen 𝒯 τ hτ hadj D eE eV ha hb hT v₀]
  simp only [smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_zsmul_comp_eq_zero D.a z (Pv 𝒯 τ eE eV hT v₀) hza, sum_zsmul_comp_eq_zero D.b z (Pv 𝒯 τ eE eV hT v₀) hzb,
    add_zero, sub_zero]
  exact sum_zsmul_single z

end Theta

section ModS
variable {G : Type} [Group G] {W : Type} [MulAction G W]
  {A : Type} [AddCommGroup A] (π : Additive (Abelianization G) →+ A)
  (hπ : ∀ (w : W) (g : G), g ∈ stabilizer G w → π (Additive.ofMul (Abelianization.of g)) = 0)

theorem cl_mul (g k : G) :
    π (Additive.ofMul (Abelianization.of (g * k)))
      = π (Additive.ofMul (Abelianization.of g)) + π (Additive.ofMul (Abelianization.of k)) := by
  rw [map_mul, ofMul_mul, map_add]

theorem cl_inv (g : G) :
    π (Additive.ofMul (Abelianization.of g⁻¹)) = -π (Additive.ofMul (Abelianization.of g)) := by
  rw [map_inv, ofMul_inv, map_neg]

include hπ in

theorem cl_coord_smul (k : G) (w : W) :
    π (Additive.ofMul (Abelianization.of (coord G (k • w))))
      = π (Additive.ofMul (Abelianization.of k)) + π (Additive.ofMul (Abelianization.of (coord G w))) := by
  have h1 := coord_spec G (k • w)
  have h2 := coord_spec G w
  rw [quotVert_mk_smul] at h1
  set o := (Quotient.mk (orbitRel G W) w).out with ho
  set s : G := (coord G w)⁻¹ * k⁻¹ * coord G (k • w) with hs
  have hsmem : s ∈ stabilizer G o := by
    rw [mem_stabilizer_iff, hs, mul_smul, mul_smul, h1, inv_smul_smul, inv_smul_eq_iff, h2]
  have hcoord : coord G (k • w) = k * coord G w * s := by
    rw [hs]; group
  rw [hcoord, cl_mul, cl_mul, hπ o s hsmem, add_zero]

variable (𝒯 : SimpleGraph W) [GraphAction G 𝒯]

include hπ in
theorem cl_lab_smul (k : G) (d : 𝒯.Dart) :
    π (Additive.ofMul (Abelianization.of (lab G 𝒯 (k • d))))
      = π (Additive.ofMul (Abelianization.of (lab G 𝒯 d))) := by
  simp only [lab, smul_dart_fst, smul_dart_snd, cl_mul, cl_inv, cl_coord_smul π hπ]
  abel

include hπ in
theorem cl_lab_out_mk (d : 𝒯.Dart) :
    π (Additive.ofMul (Abelianization.of (lab G 𝒯 (Quotient.mk (orbitRel G 𝒯.Dart) d).out)))
      = π (Additive.ofMul (Abelianization.of (lab G 𝒯 d))) := by
  obtain ⟨k, hk⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.mk_out (s := orbitRel G 𝒯.Dart) d))
  rw [← hk, cl_lab_smul π hπ]

variable (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
  [DecidableEq (QuotEdge G 𝒯)]
  {E : Type} [Fintype E]
  (eE : E ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})

include hτ hadj hπ in

theorem cl_Theta_dartChain (d : 𝒯.Dart) :
    π (Theta 𝒯 τ eE (dartChain 𝒯 τ eE d)) = π (Additive.ofMul (Abelianization.of (lab G 𝒯 d))) := by
  classical
  by_cases h0 : τ d.fst = 0
  · rw [dartChain_of_eq_zero 𝒯 τ hτ hadj eE d h0, Theta_single, one_zsmul]
    unfold γ gen
    rw [eE_eOf, cl_lab_out_mk π hπ]
  · rw [dartChain_of_ne_zero 𝒯 τ hτ hadj eE d h0, Theta_single, neg_one_zsmul, map_neg]
    unfold γ gen
    rw [eE_eOf, cl_lab_out_mk π hπ, lab_symm, cl_inv, neg_neg]

include hτ hadj hπ in

theorem cl_Theta_walkCycle {x y : W} (p : 𝒯.Walk x y) :
    π (Theta 𝒯 τ eE (walkCycle 𝒯 (fun e => (eE e).1) p))
      = -π (Additive.ofMul (Abelianization.of (coord G x)))
        + π (Additive.ofMul (Abelianization.of (coord G y))) := by
  induction p with
  | nil => rw [walkCycle_nil, map_zero, map_zero, neg_add_cancel]
  | cons h p ih =>
    rw [walkCycle_cons' 𝒯 τ eE, map_add, map_add, ih, cl_Theta_dartChain π hπ 𝒯 τ hτ hadj eE]
    unfold lab
    rw [cl_mul, cl_inv]
    abel

include hτ hadj hπ in

theorem cl_Theta_pathCycle (hT : 𝒯.IsTree) (v₀ : W) (g : G) :
    π (Theta 𝒯 τ eE (pathCycle 𝒯 (fun e => (eE e).1) v₀ g)) = π (Additive.ofMul (Abelianization.of g)) := by
  let p : 𝒯.Walk v₀ (g • v₀) := (hT.connected.preconnected v₀ (g • v₀)).some
  rw [pathCycle_eq_walkCycle' 𝒯 hT _ v₀ g p, cl_Theta_walkCycle π hπ 𝒯 τ hτ hadj eE, cl_coord_smul π hπ]
  abel

end ModS

section FixZero
variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
  [DecidableEq (QuotEdge G 𝒯)]

theorem pathCycle_eq_zero_of_smul_eq (hT : 𝒯.IsTree) {E : Type} (orb : E → QuotEdge G 𝒯) (v₀ : W)
    (g : G) (w : W) (hw : g • w = w) : pathCycle 𝒯 orb v₀ g = 0 := by
  let q : 𝒯.Walk v₀ w := (hT.connected.preconnected v₀ w).some
  let r : 𝒯.Walk w (g • v₀) :=
    (q.reverse.map (smulHom g)).copy ((smulHom_apply 𝒯 g w).trans hw) (smulHom_apply 𝒯 g v₀)
  rw [pathCycle_eq_walkCycle' 𝒯 hT orb v₀ g (q.append r), walkCycle_append, walkCycle_copy,
    walkCycle_map_smulHom, walkCycle_reverse, add_neg_cancel]

end FixZero

end P2mKcBassSerreH1

open P2mKcBassSerreH1 in

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
    (v₀ : W)
    (Φ : Additive (Abelianization G) →+ ↥(ribbonKernel D))
    (hΦ : ∀ g : G, (Φ (Additive.ofMul (Abelianization.of g)) : E → ℤ) = pathCycle 𝒯 (fun e => (eE e).1) v₀ g) :
    Function.Surjective Φ ∧
      ∀ x : Additive (Abelianization G), Φ x = 0 ↔
        x ∈ AddSubgroup.closure
          ((fun g : G => Additive.ofMul (Abelianization.of g)) '' (⋃ w : W, (stabilizer G w : Set G))) := by
  classical

  set Sset : Set (Additive (Abelianization G)) :=
    (fun g : G => Additive.ofMul (Abelianization.of g)) '' (⋃ w : W, (stabilizer G w : Set G)) with hSset

  have hkill : ∀ y ∈ Sset, Φ y = 0 := by
    rintro y ⟨g, hg, rfl⟩
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hg
    apply Subtype.ext
    rw [hΦ g, Submodule.coe_zero]
    exact pathCycle_eq_zero_of_smul_eq 𝒯 hT _ v₀ g w (mem_stabilizer_iff.mp hw)
  refine ⟨?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  ·
    intro z
    refine ⟨Theta 𝒯 τ eE (z : E → ℤ), ?_⟩
    apply Subtype.ext
    rw [Theta_apply, map_sum, Submodule.coe_sum]
    simp only [map_zsmul, Submodule.coe_smul]
    have hγ : ∀ e, (Φ (γ 𝒯 τ eE e) : E → ℤ) = pathCycle 𝒯 (fun e => (eE e).1) v₀ (gen 𝒯 τ eE e) :=
      fun e => hΦ _
    simp only [hγ]
    exact sum_zsmul_pathCycle_gen 𝒯 τ hτ hadj D eE eV ha hb hT v₀ z z.2
  ·
    let π : Additive (Abelianization G) →+ Additive (Abelianization G) ⧸ AddSubgroup.closure Sset :=
      QuotientAddGroup.mk' _
    have hπ : ∀ (w : W) (g : G), g ∈ stabilizer G w → π (Additive.ofMul (Abelianization.of g)) = 0 := by
      intro w g hg
      apply (QuotientAddGroup.eq_zero_iff _).mpr
      exact AddSubgroup.subset_closure ⟨g, Set.mem_iUnion.mpr ⟨w, hg⟩, rfl⟩
    apply (QuotientAddGroup.eq_zero_iff _).mp
    change π x = 0
    induction x using QuotientGroup.induction_on with
    | H g =>
      have h0 : pathCycle 𝒯 (fun e => (eE e).1) v₀ g = 0 := by
        rw [← hΦ g]
        have hx' : Φ (Additive.ofMul (Abelianization.of g)) = 0 := hx
        change ((Φ (Additive.ofMul (Abelianization.of g)) : ↥(ribbonKernel D)) : E → ℤ) = 0
        rw [hx', Submodule.coe_zero]
      have := cl_Theta_pathCycle π hπ 𝒯 τ hτ hadj eE hT v₀ g
      rw [h0, map_zero, map_zero] at this
      exact this.symm
  ·
    exact (AddSubgroup.closure_le (AddMonoidHom.ker Φ)).mpr (fun y hy => (AddMonoidHom.mem_ker).mpr (hkill y hy)) hx

end S_CerednikDrinfeld_Mumford_surjective_and_apply_eq_zero_iff_mem_closure_stabilizer_of_apply_eq_pathCycle
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_surjective_and_apply_eq_zero_iff_mem_closure_stabilizer_of_apply_eq_pathCycle (solution)
