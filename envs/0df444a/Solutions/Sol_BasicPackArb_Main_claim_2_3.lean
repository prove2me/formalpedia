-- Prove2me | solution 1 for BasicPackArb.Main.claim_2_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:18:11.739432+00:00
-- url     : https://prove2.me/submissions/8d623318-496a-4b56-8ddc-a0bd27790bfa

import Mathlib
import Definitions.Def_BasicPackArb_Main_RootedDigraph
import Definitions.Def_BasicPackArb_Main_ProofObjects

open BasicPackArb.Main in
theorem solution {V Arc S : Type*} [Fintype V] [DecidableEq V] [Fintype S]
    (D : Digraph V Arc) (π : S → V) (M : Matroid S) (hM : M.E = Set.univ)
    (hind : MIndependent π M) (hconn : MConnected D π M)
    (hgood : ∀ a ∈ D.arcs, IsGoodArc D π M a) :
    IsBasicPacking D π M (fun s => Arborescence.single D (π s)) := by
  classical
  have hfin : ∀ X : Set S, M.eRk X ≠ ⊤ := fun X =>
    Matroid.eRk_ne_top_iff.mpr (M.isRkFinite_of_finite (Set.toFinite X))
  have hnotsucc : ∀ X : Set S, ¬ M.eRk X + 1 ≤ M.eRk X := by
    intro X h
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (hfin X)
    rw [← hm] at h
    norm_cast at h
    omega
  have hE : ∀ X : Set S, X ⊆ M.E := fun X => by rw [hM]; exact Set.subset_univ _
  have hSpan : ∀ Q : Set S, Span M Q ⊆ M.closure Q := by
    intro Q s hs
    by_contra hns
    have h := Matroid.eRk_insert_eq_add_one (M := M) (X := Q) (e := s)
      ⟨by rw [hM]; trivial, hns⟩
    simp only [Span, Set.mem_setOf_eq] at hs
    rw [hs] at h
    exact hnotsucc Q h.symm.le
  refine ⟨fun s => rfl, fun s s' _ => by simp [Arborescence.single], fun v => ?_⟩
  set Sv : Set S := π ⁻¹' {v} with hSv
  have hset : {s | v ∈ (Arborescence.single D (π s)).verts} = Sv := by
    ext s; simp [Arborescence.single, hSv, eq_comm]
  rw [hset]
  apply (hind v).isBase_of_ground_subset_closure
  let Y : Finset V := Finset.univ.filter (fun u => π ⁻¹' {u} ⊆ M.closure Sv)
  have hvY : v ∈ Y := by
    simp only [Y, Finset.mem_filter, Finset.mem_univ, true_and]
    exact M.subset_closure Sv (hE _)
  have hin : D.inDeg Y = 0 := by
    unfold Digraph.inDeg Digraph.enteringArcs
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro a ha ⟨htail, hhead⟩
    apply htail
    simp only [Y, Finset.mem_filter, Finset.mem_univ, true_and] at hhead ⊢
    have hg := hgood a ha
    unfold IsGoodArc Dominates at hg
    rw [Finset.coe_singleton, Finset.coe_singleton] at hg
    calc π ⁻¹' {D.tail a} ⊆ Span M (π ⁻¹' {D.head a}) := hg
      _ ⊆ M.closure (π ⁻¹' {D.head a}) := hSpan _
      _ ⊆ M.closure (M.closure Sv) := M.closure_subset_closure hhead
      _ = M.closure Sv := M.closure_closure Sv
  have hc := hconn Y ⟨v, hvY⟩
  rw [hin] at hc
  simp only [Nat.cast_zero, zero_add] at hc
  have hYsub : π ⁻¹' (Y : Set V) ⊆ M.closure Sv := by
    intro s hs
    simp only [Set.mem_preimage, Finset.mem_coe, Y, Finset.mem_filter, Finset.mem_univ,
      true_and] at hs
    exact hs (by simp)
  have hrk : M.eRk Set.univ ≤ M.eRk (M.closure Sv) := hc.trans (M.eRk_mono hYsub)
  rw [hM]
  intro s _
  by_contra hs
  have h := Matroid.eRk_insert_eq_add_one (M := M) (X := M.closure Sv) (e := s)
    ⟨by rw [hM]; trivial, by rwa [M.closure_closure]⟩
  have h2 : M.eRk (insert s (M.closure Sv)) ≤ M.eRk Set.univ := M.eRk_mono (Set.subset_univ _)
  rw [h] at h2
  exact hnotsucc _ (h2.trans hrk)
