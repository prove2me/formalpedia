-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.exists_mem_ribbonKernel_and_sub_eq_sum_stabWidth_mul_walkCycle_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/54b37a17-3df9-5d04-9dff-d7c8a68d13d3

import Mathlib
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_exists_mem_ribbonKernel_and_sub_eq_sum_stabWidth_mul_walkCycle_of_dvd

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

namespace PotW

variable {G : Type} [Group G] {W : Type} [MulAction G W] {𝒯 : SimpleGraph W} [GraphAction G 𝒯]

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

theorem quotEdge_eq_iff (d d' : 𝒯.Dart) :
    (Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯) = Quotient.mk _ d' ↔ ∃ g : G, g • d' = d := by
  rw [Quotient.eq]; exact MulAction.orbitRel_apply.trans MulAction.mem_orbit_iff

theorem quotVert_eq_iff (a b : W) :
    (Quotient.mk (orbitRel G W) a : QuotVert G W) = Quotient.mk _ b ↔ ∃ g : G, g • b = a := by
  rw [Quotient.eq]; exact MulAction.orbitRel_apply.trans MulAction.mem_orbit_iff

theorem exists_smul_eq_out (d : 𝒯.Dart) :
    ∃ g : G, g • d = (Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯).out := by
  have h := Quotient.out_eq (Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯)
  exact (quotEdge_eq_iff _ _).1 h

theorem exists_smul_eq_out' (q : QuotEdge G 𝒯) (d : 𝒯.Dart) (h : Quotient.mk (orbitRel G 𝒯.Dart) d = q) :
    ∃ g : G, g • d = q.out := by
  subst h; exact exists_smul_eq_out d

section Colour

variable (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
include hτ hadj

theorem colour_snd_of_fst_eq_zero (d : 𝒯.Dart) (h : τ d.fst = 0) : τ d.snd = 1 := by
  rcases zmod2_cases (τ d.snd) with h1 | h1
  · exact absurd (h.trans h1.symm) (hadj _ _ d.adj)
  · exact h1

theorem colour_fst_of_ne_zero (d : 𝒯.Dart) (h : τ d.fst ≠ 0) : τ d.fst = 1 ∧ τ d.snd = 0 := by
  rcases zmod2_cases (τ d.fst) with h0 | h1
  · exact absurd h0 h
  · rcases zmod2_cases (τ d.snd) with h2 | h2
    · exact ⟨h1, h2⟩
    · exact absurd (h1.trans h2.symm) (hadj _ _ d.adj)

theorem colour_out_fst (d : 𝒯.Dart) :
    τ (Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯).out.fst = τ d.fst := by
  obtain ⟨g, hg⟩ := exists_smul_eq_out (G := G) d
  rw [← hg, smul_dart_fst, hτ]

end Colour

section Main

variable (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
variable [DecidableEq (QuotEdge G 𝒯)]
variable {E : Type} [Fintype E] (eE : E ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})
variable (φ : W → ℤ) (hφ : ∀ g : G, ∃ n : ℤ, ∀ w : W, φ (g • w) = φ w + n)

include hφ in
theorem incr_smul (g : G) (a b : W) : φ (g • a) - φ (g • b) = φ a - φ b := by
  obtain ⟨n, hn⟩ := hφ g
  rw [hn, hn]; ring

theorem sum_ite_eq_select (c : QuotEdge G 𝒯) (F : E → ℤ) :
    (∑ e : E, F e * (if Quotient.mk (orbitRel G 𝒯.Dart) c.out = (eE e).1 then (1 : ℤ) else 0)) =
      if h : τ c.out.fst = 0 then F (eE.symm ⟨c, h⟩) else 0 := by
  have hc : ∀ e : E, (Quotient.mk (orbitRel G 𝒯.Dart) c.out = (eE e).1) ↔ (eE e).1 = c := fun e => by
    rw [Quotient.out_eq]; exact eq_comm
  simp_rw [hc]
  split_ifs with h
  · rw [Finset.sum_eq_single (eE.symm ⟨c, h⟩)]
    · simp
    · intro b _ hb
      rw [if_neg, mul_zero]
      intro hb'
      apply hb
      apply eE.injective
      rw [Equiv.apply_symm_apply]
      exact Subtype.ext hb'
    · intro hb; exact absurd (Finset.mem_univ _) hb
  · refine Finset.sum_eq_zero fun e _ => ?_
    rw [if_neg, mul_zero]
    intro he
    apply h
    rw [← he]
    exact (eE e).2

include hτ hadj hφ in

theorem sum_mul_dartIndex (d : 𝒯.Dart) :
    (∑ e : E, (φ (eE e).1.out.snd - φ (eE e).1.out.fst) * dartIndex 𝒯 (eE e).1 d) = φ d.snd - φ d.fst := by

  have hsplit : ∀ e : E, (φ (eE e).1.out.snd - φ (eE e).1.out.fst) * dartIndex 𝒯 (eE e).1 d =
      (φ (eE e).1.out.snd - φ (eE e).1.out.fst) *
          (if Quotient.mk (orbitRel G 𝒯.Dart)
              (Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯).out = (eE e).1 then (1 : ℤ) else 0) -
        (φ (eE e).1.out.snd - φ (eE e).1.out.fst) *
          (if Quotient.mk (orbitRel G 𝒯.Dart)
              (Quotient.mk (orbitRel G 𝒯.Dart) d.symm : QuotEdge G 𝒯).out = (eE e).1 then (1 : ℤ) else 0) := by
    intro e
    rw [dartIndex, Quotient.out_eq, Quotient.out_eq, mul_sub]
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib, sum_ite_eq_select τ eE, sum_ite_eq_select τ eE]
  rcases zmod2_cases (τ d.fst) with h0 | h1
  ·
    have h0' : τ (Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯).out.fst = 0 := by
      rw [colour_out_fst τ hτ hadj]; exact h0
    have h1' : ¬ τ (Quotient.mk (orbitRel G 𝒯.Dart) d.symm : QuotEdge G 𝒯).out.fst = 0 := by
      rw [colour_out_fst τ hτ hadj, SimpleGraph.Dart.symm_toProd]
      show ¬ τ d.snd = 0
      rw [colour_snd_of_fst_eq_zero τ hτ hadj d h0]; decide
    rw [dif_pos h0', dif_neg h1', sub_zero, Equiv.apply_symm_apply]
    obtain ⟨g, hg⟩ := exists_smul_eq_out (G := G) d
    simp only [← hg, smul_dart_snd, smul_dart_fst]
    exact incr_smul φ hφ g _ _
  ·
    have hne : τ d.fst ≠ 0 := by rw [h1]; decide
    obtain ⟨-, h2⟩ := colour_fst_of_ne_zero τ hτ hadj d hne
    have h0' : ¬ τ (Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯).out.fst = 0 := by
      rw [colour_out_fst τ hτ hadj]; exact hne
    have h1' : τ (Quotient.mk (orbitRel G 𝒯.Dart) d.symm : QuotEdge G 𝒯).out.fst = 0 := by
      rw [colour_out_fst τ hτ hadj, SimpleGraph.Dart.symm_toProd]; exact h2
    rw [dif_neg h0', dif_pos h1', zero_sub, Equiv.apply_symm_apply]
    obtain ⟨g, hg⟩ := exists_smul_eq_out (G := G) d.symm
    simp only [← hg, smul_dart_snd, smul_dart_fst, SimpleGraph.Dart.symm_toProd]
    rw [incr_smul φ hφ g]
    show -(φ d.fst - φ d.snd) = φ d.snd - φ d.fst
    ring

include hτ hadj hφ in

theorem sub_eq_sum_mul_walkCycle {u u' : W} (p : 𝒯.Walk u u') :
    φ u' - φ u = ∑ e : E, (φ (eE e).1.out.snd - φ (eE e).1.out.fst) * walkCycle 𝒯 (fun e => (eE e).1) p e := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    simp_rw [walkCycle_cons, mul_add]
    rw [Finset.sum_add_distrib, sum_mul_dartIndex τ hτ hadj eE φ hφ ⟨(a, b), h⟩, ← ih]
    show φ c - φ a = φ b - φ a + (φ c - φ b)
    ring

theorem pushforward_apply {V : Type} [DecidableEq V] (f : E → V) (x : E → ℤ) (v : V) :
    pushforward f x v = ∑ e ∈ Finset.univ.filter (fun e => f e = v), x e := by
  simp only [pushforward, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, degeneracyMatrix, Matrix.of_apply]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp

variable {V : Type} [DecidableEq V] (D : DegeneracyData E V) (eV : V ≃ QuotVert G W)
variable (ha : ∀ e : E, eV (D.a e) = Quotient.mk (orbitRel G W) (eE e).1.out.fst)
variable (hb : ∀ e : E, eV (D.b e) = Quotient.mk (orbitRel G W) (eE e).1.out.snd)
variable (hharm : ∀ (u : W) (S : Finset W), (∀ x, x ∈ S ↔ 𝒯.Adj u x) → ∑ x ∈ S, (φ x - φ u) = 0)
variable (hfin : ∀ w : W, Finite (MulAction.stabilizer G w))
variable (c : E → ℤ)
variable (hc : ∀ e : E, φ (eE e).1.out.snd - φ (eE e).1.out.fst = ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) * c e)

omit hφ in
include hfin in

theorem finite_stabilizer_dart (d : 𝒯.Dart) : Finite (MulAction.stabilizer G d) := by
  haveI := hfin d.fst
  have hle : ∀ s : G, s ∈ MulAction.stabilizer G d → s ∈ MulAction.stabilizer G d.fst := by
    intro s hs
    rw [MulAction.mem_stabilizer_iff] at hs ⊢
    rw [← smul_dart_fst, hs]
  exact Finite.of_injective (fun s : MulAction.stabilizer G d => (⟨s.1, hle s.1 s.2⟩ : MulAction.stabilizer G d.fst))
    (fun s t h => Subtype.ext (by have := congrArg (fun x : MulAction.stabilizer G d.fst => (x : G)) h; exact this))

omit hφ in
include hfin in

theorem stabWidth_coe_eq (d : 𝒯.Dart) (q : QuotEdge G 𝒯) (hq : Quotient.mk (orbitRel G 𝒯.Dart) d = q) :
    ((stabWidth G 𝒯 q : ℕ) : ℤ) = (Nat.card (MulAction.stabilizer G d) : ℤ) := by
  haveI := finite_stabilizer_dart hfin d
  have h1 : stabWidth G 𝒯 q = Nat.toPNat' (Nat.card (MulAction.stabilizer G d)) := by
    rw [← hq]; exact stabWidth_mk 𝒯 d
  have h2 : ((Nat.toPNat' (Nat.card (MulAction.stabilizer G d)) : ℕ+) : ℕ) = Nat.card (MulAction.stabilizer G d) := by
    rw [Nat.toPNat'_coe, if_pos Nat.card_pos]
  rw [h1, h2]

theorem card_filter_smul_eq {H : Subgroup G} [Fintype H] {X : Type} [MulAction G X] [DecidableEq X]
    (x : X) (h₀ : H) :
    (Finset.univ.filter fun h : H => (h : G) • x = (h₀ : G) • x).card = Fintype.card {s : H // (s : G) • x = x} := by
  classical
  rw [← Fintype.card_subtype]
  refine Fintype.card_congr ?_
  refine
    { toFun := fun h => ⟨h₀⁻¹ * h.1, ?_⟩
      invFun := fun s => ⟨h₀ * s.1, ?_⟩
      left_inv := fun h => Subtype.ext (by simp)
      right_inv := fun s => Subtype.ext (by simp) }
  · show ((h₀⁻¹ * h.1 : H) : G) • x = x
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, h.2, inv_smul_smul]
  · show ((h₀ * s.1 : H) : G) • x = (h₀ : G) • x
    rw [Subgroup.coe_mul, mul_smul, s.2]

include hτ hadj hφ ha hharm hfin hc in

theorem sum_filter_a_eq_zero_w (v : V) :
    (∑ e ∈ Finset.univ.filter (fun e => D.a e = v), c e) = 0 := by
  classical
  by_cases hem : (Finset.univ.filter (fun e => D.a e = v)).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.1 hem, Finset.sum_empty]
  obtain ⟨e₁, he₁⟩ := hem
  have he₁' : D.a e₁ = v := (Finset.mem_filter.1 he₁).2
  set w : W := (eE e₁).1.out.fst with hw
  have hvw : eV v = Quotient.mk (orbitRel G W) w := by rw [← he₁', ha]
  have hτw : τ w = 0 := (eE e₁).2
  haveI : Finite (MulAction.stabilizer G w) := hfin w
  haveI : Fintype (MulAction.stabilizer G w) := Fintype.ofFinite _

  have hex : ∀ e : E, D.a e = v → ∃ g : G, g • (eE e).1.out.fst = w := by
    intro e he
    have h1 : Quotient.mk (orbitRel G W) w = Quotient.mk (orbitRel G W) (eE e).1.out.fst := by
      rw [← hvw, ← he, ha]
    exact (quotVert_eq_iff _ _).1 h1
  choose! gg hgg using hex
  obtain ⟨δ, hδfst, hδcls, hδx⟩ : ∃ δ : E → 𝒯.Dart, (∀ e, D.a e = v → (δ e).fst = w) ∧
      (∀ e, Quotient.mk (orbitRel G 𝒯.Dart) (δ e) = (eE e).1) ∧
      (∀ e, φ (δ e).snd - φ (δ e).fst = ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) * c e) := by
    refine ⟨fun e => gg e • (eE e).1.out, fun e he => ?_, fun e => ?_, fun e => ?_⟩
    · rw [smul_dart_fst, hgg e he]
    · rw [← Quotient.out_eq (eE e).1]
      exact (quotEdge_eq_iff _ _).2 ⟨gg e, rfl⟩
    · rw [smul_dart_snd, smul_dart_fst, incr_smul φ hφ, hc]
  have hwidth : ∀ e, ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) = (Nat.card (MulAction.stabilizer G (δ e)) : ℤ) :=
    fun e => stabWidth_coe_eq hfin (δ e) _ (hδcls e)

  have hidx : ∀ (y : W) (hy : 𝒯.Adj w y),
      ∃ e : E, D.a e = v ∧ ∃ h : MulAction.stabilizer G w, (h : G) • δ e = (⟨(w, y), hy⟩ : 𝒯.Dart) := by
    intro y hy
    set d : 𝒯.Dart := ⟨(w, y), hy⟩ with hd
    have hq : τ (Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯).out.fst = 0 := by
      rw [colour_out_fst τ hτ hadj]; exact hτw
    set e : E := eE.symm ⟨Quotient.mk (orbitRel G 𝒯.Dart) d, hq⟩ with he
    have heE : (eE e).1 = Quotient.mk (orbitRel G 𝒯.Dart) d := by
      rw [he, Equiv.apply_symm_apply]

    have hcl : Quotient.mk (orbitRel G 𝒯.Dart) (δ e) = Quotient.mk (orbitRel G 𝒯.Dart) d := by rw [hδcls, heE]
    obtain ⟨g, hg⟩ := (quotEdge_eq_iff _ _).1 hcl

    have he2 : D.a e = v := by
      obtain ⟨g', hg'⟩ := exists_smul_eq_out (G := G) d
      have hout : (eE e).1.out = g' • d := by rw [heE]; exact hg'.symm
      apply eV.injective
      rw [ha, hvw, hout, smul_dart_fst]
      exact ((quotVert_eq_iff _ _).2 ⟨g', rfl⟩)
    refine ⟨e, he2, ⟨g⁻¹, ?_⟩, ?_⟩
    · rw [MulAction.mem_stabilizer_iff, inv_smul_eq_iff]
      have := hδfst e he2
      rw [← hg, smul_dart_fst] at this
      exact this.symm
    · show g⁻¹ • δ e = d
      rw [← hg, inv_smul_smul]

  set T : Finset (E × MulAction.stabilizer G w) := (Finset.univ.filter (fun e => D.a e = v)) ×ˢ Finset.univ with hT
  set f : E × MulAction.stabilizer G w → W := fun t => ((t.2 : G) • δ t.1).snd with hf
  have hTmem : ∀ t : E × MulAction.stabilizer G w, t ∈ T ↔ D.a t.1 = v := by
    intro t; rw [hT, Finset.mem_product, Finset.mem_filter]; simp
  have hfst : ∀ t ∈ T, ((t.2 : G) • δ t.1).fst = w := by
    intro t ht; rw [smul_dart_fst, hδfst t.1 ((hTmem t).1 ht)]; exact t.2.2
  set S : Finset W := T.image f with hSdef
  have hS' : ∀ y, y ∈ S ↔ 𝒯.Adj w y := by
    intro y
    constructor
    · intro hy
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
      have hadj' := ((t.2 : G) • δ t.1).adj
      rw [hfst t ht] at hadj'
      exact hadj'
    · intro hy
      obtain ⟨e, he2, h, hh⟩ := hidx y hy
      refine Finset.mem_image.2 ⟨(e, h), (hTmem _).2 he2, ?_⟩
      rw [hf]; show ((h : G) • δ e).snd = y
      rw [hh]

  have hfib_idx : ∀ t ∈ T, ∀ t' ∈ T, f t = f t' → t.1 = t'.1 := by
    intro t ht t' ht' hff
    have hdd : (t.2 : G) • δ t.1 = (t'.2 : G) • δ t'.1 :=
      SimpleGraph.Dart.ext _ _ (Prod.ext ((hfst t ht).trans (hfst t' ht').symm) (by rw [hf] at hff; exact hff))
    have hcls : (eE t.1).1 = (eE t'.1).1 := by
      rw [← hδcls t.1, ← hδcls t'.1]
      apply (quotEdge_eq_iff _ _).2
      exact ⟨(t.2 : G)⁻¹ * t'.2, by rw [mul_smul, ← hdd, inv_smul_smul]⟩
    exact eE.injective (Subtype.ext hcls)
  have hfib_card : ∀ t ∈ T,
      ((T.filter fun t' => f t' = f t).card : ℤ) = Nat.card (MulAction.stabilizer G (δ t.1)) := by
    intro t ht
    have he2 : D.a t.1 = v := (hTmem t).1 ht
    have hset : (T.filter fun t' => f t' = f t) =
        (({t.1} : Finset E) ×ˢ (Finset.univ.filter fun h : MulAction.stabilizer G w =>
          (h : G) • δ t.1 = (t.2 : G) • δ t.1)) := by
      ext t'
      constructor
      · intro hmem
        rw [Finset.mem_filter] at hmem
        obtain ⟨ht', hff⟩ := hmem
        have hee : t'.1 = t.1 := hfib_idx t' ht' t ht hff
        rw [Finset.mem_product, Finset.mem_singleton, Finset.mem_filter]
        refine ⟨hee, Finset.mem_univ _, ?_⟩
        have hdd : (t'.2 : G) • δ t'.1 = (t.2 : G) • δ t.1 :=
          SimpleGraph.Dart.ext _ _ (Prod.ext ((hfst t' ht').trans (hfst t ht).symm) hff)
        rw [hee] at hdd
        exact hdd
      · intro hmem
        rw [Finset.mem_product, Finset.mem_singleton, Finset.mem_filter] at hmem
        obtain ⟨hee, -, hh⟩ := hmem
        rw [Finset.mem_filter]
        refine ⟨(hTmem t').2 (by rw [hee]; exact he2), ?_⟩
        show ((t'.2 : G) • δ t'.1).snd = ((t.2 : G) • δ t.1).snd
        rw [hee, hh]
    rw [hset, Finset.card_product, Finset.card_singleton, one_mul, card_filter_smul_eq (δ t.1) t.2]
    haveI := finite_stabilizer_dart hfin (δ t.1)
    rw [← Nat.card_eq_fintype_card]
    congr 1
    refine Nat.card_congr ?_
    refine
      { toFun := fun s => ⟨(s.1 : G), by rw [MulAction.mem_stabilizer_iff]; exact s.2⟩
        invFun := fun s => ⟨⟨s.1, ?_⟩, s.2⟩
        left_inv := fun s => rfl
        right_inv := fun s => rfl }
    rw [MulAction.mem_stabilizer_iff]
    have h1 := congrArg (fun d : 𝒯.Dart => d.fst) s.2
    rw [smul_dart_fst, hδfst t.1 he2] at h1
    exact h1

  have hA : ∑ t ∈ T, c t.1 = (Fintype.card (MulAction.stabilizer G w) : ℤ) *
      ∑ e ∈ Finset.univ.filter (fun e => D.a e = v), c e := by
    rw [hT, Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hB : ∑ t ∈ T, c t.1 = ∑ y ∈ S, (φ y - φ w) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := T) (t := S) (g := f) (fun t ht => Finset.mem_image_of_mem f ht)]
    refine Finset.sum_congr rfl fun y hy => ?_
    obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.1 hy
    have h1 : ∑ t ∈ T.filter (fun t => f t = f t₀), c t.1 = ∑ t ∈ T.filter (fun t => f t = f t₀), c t₀.1 := by
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Finset.mem_filter] at ht
      rw [hfib_idx t ht.1 t₀ ht₀ ht.2]
    rw [h1, Finset.sum_const, nsmul_eq_mul, hfib_card t₀ ht₀, ← hwidth, ← hδx]

    have h2 : f t₀ = (t₀.2 : G) • (δ t₀.1).snd := by rw [hf]; rfl
    have h3 : w = (t₀.2 : G) • (δ t₀.1).fst := by rw [← smul_dart_fst, hfst t₀ ht₀]
    have h4 : φ w = φ ((t₀.2 : G) • (δ t₀.1).fst) := by rw [← h3]
    rw [h2, h4, incr_smul φ hφ]
  have hcard : (Fintype.card (MulAction.stabilizer G w) : ℤ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have := hA.symm.trans (hB.trans (hharm w S hS'))
  exact (mul_eq_zero.mp this).resolve_left hcard

include hτ hadj hφ hb hharm hfin hc in

theorem sum_filter_b_eq_zero_w (v : V) :
    (∑ e ∈ Finset.univ.filter (fun e => D.b e = v), c e) = 0 := by
  classical
  by_cases hem : (Finset.univ.filter (fun e => D.b e = v)).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.1 hem, Finset.sum_empty]
  obtain ⟨e₁, he₁⟩ := hem
  have he₁' : D.b e₁ = v := (Finset.mem_filter.1 he₁).2
  set w : W := (eE e₁).1.out.snd with hw
  have hvw : eV v = Quotient.mk (orbitRel G W) w := by rw [← he₁', hb]
  have hτw : τ w = 1 := colour_snd_of_fst_eq_zero τ hτ hadj _ (eE e₁).2
  haveI : Finite (MulAction.stabilizer G w) := hfin w
  haveI : Fintype (MulAction.stabilizer G w) := Fintype.ofFinite _

  have hex : ∀ e : E, D.b e = v → ∃ g : G, g • (eE e).1.out.snd = w := by
    intro e he
    have h1 : Quotient.mk (orbitRel G W) w = Quotient.mk (orbitRel G W) (eE e).1.out.snd := by
      rw [← hvw, ← he, hb]
    exact (quotVert_eq_iff _ _).1 h1
  choose! gg hgg using hex
  obtain ⟨δ, hδsnd, hδcls, hδx⟩ : ∃ δ : E → 𝒯.Dart, (∀ e, D.b e = v → (δ e).snd = w) ∧
      (∀ e, Quotient.mk (orbitRel G 𝒯.Dart) (δ e) = (eE e).1) ∧
      (∀ e, φ (δ e).snd - φ (δ e).fst = ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) * c e) := by
    refine ⟨fun e => gg e • (eE e).1.out, fun e he => ?_, fun e => ?_, fun e => ?_⟩
    · rw [smul_dart_snd, hgg e he]
    · rw [← Quotient.out_eq (eE e).1]
      exact (quotEdge_eq_iff _ _).2 ⟨gg e, rfl⟩
    · rw [smul_dart_snd, smul_dart_fst, incr_smul φ hφ, hc]
  have hwidth : ∀ e, ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) = (Nat.card (MulAction.stabilizer G (δ e)) : ℤ) :=
    fun e => stabWidth_coe_eq hfin (δ e) _ (hδcls e)

  have hidx : ∀ (y : W) (hy : 𝒯.Adj w y),
      ∃ e : E, D.b e = v ∧ ∃ h : MulAction.stabilizer G w, (h : G) • δ e = (⟨(y, w), hy.symm⟩ : 𝒯.Dart) := by
    intro y hy
    set d : 𝒯.Dart := ⟨(y, w), hy.symm⟩ with hd
    have hy0 : τ y = 0 := by
      rcases zmod2_cases (τ y) with h | h
      · exact h
      · exact absurd (hτw.trans h.symm) (hadj _ _ hy)
    have hq : τ (Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯).out.fst = 0 := by
      rw [colour_out_fst τ hτ hadj]; exact hy0
    set e : E := eE.symm ⟨Quotient.mk (orbitRel G 𝒯.Dart) d, hq⟩ with he
    have heE : (eE e).1 = Quotient.mk (orbitRel G 𝒯.Dart) d := by
      rw [he, Equiv.apply_symm_apply]

    have hcl : Quotient.mk (orbitRel G 𝒯.Dart) (δ e) = Quotient.mk (orbitRel G 𝒯.Dart) d := by rw [hδcls, heE]
    obtain ⟨g, hg⟩ := (quotEdge_eq_iff _ _).1 hcl

    have he2 : D.b e = v := by
      obtain ⟨g', hg'⟩ := exists_smul_eq_out (G := G) d
      have hout : (eE e).1.out = g' • d := by rw [heE]; exact hg'.symm
      apply eV.injective
      rw [hb, hvw, hout, smul_dart_snd]
      exact ((quotVert_eq_iff _ _).2 ⟨g', rfl⟩)
    refine ⟨e, he2, ⟨g⁻¹, ?_⟩, ?_⟩
    · rw [MulAction.mem_stabilizer_iff, inv_smul_eq_iff]
      have := hδsnd e he2
      rw [← hg, smul_dart_snd] at this
      exact this.symm
    · show g⁻¹ • δ e = d
      rw [← hg, inv_smul_smul]

  set T : Finset (E × MulAction.stabilizer G w) := (Finset.univ.filter (fun e => D.b e = v)) ×ˢ Finset.univ with hT
  set f : E × MulAction.stabilizer G w → W := fun t => ((t.2 : G) • δ t.1).fst with hf
  have hTmem : ∀ t : E × MulAction.stabilizer G w, t ∈ T ↔ D.b t.1 = v := by
    intro t; rw [hT, Finset.mem_product, Finset.mem_filter]; simp
  have hsnd : ∀ t ∈ T, ((t.2 : G) • δ t.1).snd = w := by
    intro t ht; rw [smul_dart_snd, hδsnd t.1 ((hTmem t).1 ht)]; exact t.2.2
  set S : Finset W := T.image f with hSdef
  have hS' : ∀ y, y ∈ S ↔ 𝒯.Adj w y := by
    intro y
    constructor
    · intro hy
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
      have hadj' := ((t.2 : G) • δ t.1).adj
      rw [hsnd t ht] at hadj'
      exact hadj'.symm
    · intro hy
      obtain ⟨e, he2, h, hh⟩ := hidx y hy
      refine Finset.mem_image.2 ⟨(e, h), (hTmem _).2 he2, ?_⟩
      rw [hf]; show ((h : G) • δ e).fst = y
      rw [hh]

  have hfib_idx : ∀ t ∈ T, ∀ t' ∈ T, f t = f t' → t.1 = t'.1 := by
    intro t ht t' ht' hff
    have hdd : (t.2 : G) • δ t.1 = (t'.2 : G) • δ t'.1 :=
      SimpleGraph.Dart.ext _ _ (Prod.ext (by rw [hf] at hff; exact hff) ((hsnd t ht).trans (hsnd t' ht').symm))
    have hcls : (eE t.1).1 = (eE t'.1).1 := by
      rw [← hδcls t.1, ← hδcls t'.1]
      apply (quotEdge_eq_iff _ _).2
      exact ⟨(t.2 : G)⁻¹ * t'.2, by rw [mul_smul, ← hdd, inv_smul_smul]⟩
    exact eE.injective (Subtype.ext hcls)
  have hfib_card : ∀ t ∈ T,
      ((T.filter fun t' => f t' = f t).card : ℤ) = Nat.card (MulAction.stabilizer G (δ t.1)) := by
    intro t ht
    have he2 : D.b t.1 = v := (hTmem t).1 ht
    have hset : (T.filter fun t' => f t' = f t) =
        (({t.1} : Finset E) ×ˢ (Finset.univ.filter fun h : MulAction.stabilizer G w =>
          (h : G) • δ t.1 = (t.2 : G) • δ t.1)) := by
      ext t'
      constructor
      · intro hmem
        rw [Finset.mem_filter] at hmem
        obtain ⟨ht', hff⟩ := hmem
        have hee : t'.1 = t.1 := hfib_idx t' ht' t ht hff
        rw [Finset.mem_product, Finset.mem_singleton, Finset.mem_filter]
        refine ⟨hee, Finset.mem_univ _, ?_⟩
        have hdd : (t'.2 : G) • δ t'.1 = (t.2 : G) • δ t.1 :=
          SimpleGraph.Dart.ext _ _ (Prod.ext hff ((hsnd t' ht').trans (hsnd t ht).symm))
        rw [hee] at hdd
        exact hdd
      · intro hmem
        rw [Finset.mem_product, Finset.mem_singleton, Finset.mem_filter] at hmem
        obtain ⟨hee, -, hh⟩ := hmem
        rw [Finset.mem_filter]
        refine ⟨(hTmem t').2 (by rw [hee]; exact he2), ?_⟩
        show ((t'.2 : G) • δ t'.1).fst = ((t.2 : G) • δ t.1).fst
        rw [hee, hh]
    rw [hset, Finset.card_product, Finset.card_singleton, one_mul, card_filter_smul_eq (δ t.1) t.2]
    haveI := finite_stabilizer_dart hfin (δ t.1)
    rw [← Nat.card_eq_fintype_card]
    congr 1
    refine Nat.card_congr ?_
    refine
      { toFun := fun s => ⟨(s.1 : G), by rw [MulAction.mem_stabilizer_iff]; exact s.2⟩
        invFun := fun s => ⟨⟨s.1, ?_⟩, s.2⟩
        left_inv := fun s => rfl
        right_inv := fun s => rfl }
    rw [MulAction.mem_stabilizer_iff]
    have h1 := congrArg (fun d : 𝒯.Dart => d.snd) s.2
    rw [smul_dart_snd, hδsnd t.1 he2] at h1
    exact h1

  have hA : ∑ t ∈ T, c t.1 = (Fintype.card (MulAction.stabilizer G w) : ℤ) *
      ∑ e ∈ Finset.univ.filter (fun e => D.b e = v), c e := by
    rw [hT, Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hB : ∑ t ∈ T, c t.1 = ∑ y ∈ S, -(φ y - φ w) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := T) (t := S) (g := f) (fun t ht => Finset.mem_image_of_mem f ht)]
    refine Finset.sum_congr rfl fun y hy => ?_
    obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.1 hy
    have h1 : ∑ t ∈ T.filter (fun t => f t = f t₀), c t.1 = ∑ t ∈ T.filter (fun t => f t = f t₀), c t₀.1 := by
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Finset.mem_filter] at ht
      rw [hfib_idx t ht.1 t₀ ht₀ ht.2]
    rw [h1, Finset.sum_const, nsmul_eq_mul, hfib_card t₀ ht₀, ← hwidth, ← hδx]

    have h2 : f t₀ = (t₀.2 : G) • (δ t₀.1).fst := by rw [hf]; rfl
    have h3 : w = (t₀.2 : G) • (δ t₀.1).snd := by rw [← smul_dart_snd, hsnd t₀ ht₀]
    have h4 : φ w = φ ((t₀.2 : G) • (δ t₀.1).snd) := by rw [← h3]
    rw [h2, h4, incr_smul φ hφ]
    ring
  have hcard : (Fintype.card (MulAction.stabilizer G w) : ℤ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hB' : ∑ t ∈ T, c t.1 = 0 := by rw [hB, Finset.sum_neg_distrib, hharm w S hS', neg_zero]
  have := hA.symm.trans hB'
  exact (mul_eq_zero.mp this).resolve_left hcard

end Main

end PotW

open PotW in
theorem solution
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hfin : ∀ w : W, Finite (MulAction.stabilizer G w))
    (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
    [DecidableEq (QuotEdge G 𝒯)]
    {E V : Type} [Fintype E] [DecidableEq V] (D : DegeneracyData E V)
    (eE : E ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})
    (eV : V ≃ QuotVert G W)
    (ha : ∀ e : E, eV (D.a e) = Quotient.mk (orbitRel G W) (eE e).1.out.fst)
    (hb : ∀ e : E, eV (D.b e) = Quotient.mk (orbitRel G W) (eE e).1.out.snd)
    (φ : W → ℤ) (hφ : ∀ g : G, ∃ n : ℤ, ∀ w : W, φ (g • w) = φ w + n)
    (hharm : ∀ (u : W) (S : Finset W), (∀ x, x ∈ S ↔ 𝒯.Adj u x) → ∑ x ∈ S, (φ x - φ u) = 0)
    (hdiv : ∀ d : 𝒯.Dart, ((Nat.card (MulAction.stabilizer G d) : ℕ) : ℤ) ∣ φ d.snd - φ d.fst) :
    ∃ c : E → ℤ,
      (∀ e : E, φ (eE e).1.out.snd - φ (eE e).1.out.fst = ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) * c e) ∧
      c ∈ ribbonKernel D ∧
      ∀ (u u' : W) (p : 𝒯.Walk u u'),
        φ u' - φ u = ∑ e : E, ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) * c e * walkCycle 𝒯 (fun e => (eE e).1) p e := by
  classical

  have hcE : ∀ e : E, ∃ c : ℤ, φ (eE e).1.out.snd - φ (eE e).1.out.fst = ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) * c := by
    intro e
    have hw : ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) = (Nat.card (MulAction.stabilizer G (eE e).1.out) : ℤ) :=
      stabWidth_coe_eq hfin (eE e).1.out (eE e).1 (Quotient.out_eq _)
    rw [hw]
    exact hdiv (eE e).1.out
  choose c hc using hcE
  refine ⟨c, hc, ?_, ?_⟩
  · rw [mem_ribbonKernel]
    intro i
    fin_cases i
    · show pushforward D.a c = 0
      funext v
      rw [pushforward_apply]
      exact sum_filter_a_eq_zero_w τ hτ hadj eE φ hφ D eV ha hharm hfin c hc v
    · show pushforward D.b c = 0
      funext v
      rw [pushforward_apply]
      exact sum_filter_b_eq_zero_w τ hτ hadj eE φ hφ D eV hb hharm hfin c hc v
  · intro u u' p
    rw [sub_eq_sum_mul_walkCycle τ hτ hadj eE φ hφ p]
    exact Finset.sum_congr rfl fun e _ => by rw [hc e]

end S_CerednikDrinfeld_Mumford_exists_mem_ribbonKernel_and_sub_eq_sum_stabWidth_mul_walkCycle_of_dvd
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_exists_mem_ribbonKernel_and_sub_eq_sum_stabWidth_mul_walkCycle_of_dvd (solution)
