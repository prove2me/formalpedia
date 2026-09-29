-- Prove2me | solution 1 for EveryFaceIncidentDart
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:47:17.774103+00:00
-- url     : https://prove2.me/submissions/cbc9cb4a-ca9f-47d2-835c-043e294515f9

import Definitions.Def_PlaneFaceData
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open Classical
noncomputable section

lemma aux_efid_carrier_closed (γ : PolygonalArc) : IsClosed γ.carrier := by
  rw [γ.carrier_eq]
  have hset : {p | ∃ i : ℕ, ∃ hi : i + 1 < γ.vertices.length,
        p ∈ segment ℝ γ.vertices[i] γ.vertices[i + 1]} =
      ⋃ i : Fin γ.vertices.length, ⋃ hi : i.1 + 1 < γ.vertices.length,
        segment ℝ γ.vertices[i.1] γ.vertices[i.1 + 1] := by
    ext p
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi, hp⟩
      exact ⟨⟨i, by omega⟩, hi, hp⟩
    · rintro ⟨i, hi, hp⟩
      exact ⟨i.1, hi, hp⟩
  rw [hset]
  refine isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun hi => ?_
  rw [← closure_openSegment]
  exact isClosed_closure

lemma aux_efid_image_closed {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (D : OrdinaryPolygonalDrawing G) :
    IsClosed (OrdinaryDrawingImage G D) := by
  unfold OrdinaryDrawingImage
  refine IsClosed.union (Set.finite_range _).isClosed ?_
  exact isClosed_iUnion_of_finite fun e => aux_efid_carrier_closed _

theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (hD : D.crossingSet.card = 0) (A : PlaneFaceData G D) :
    G.Connected → 3 ≤ Fintype.card V → 0 < G.edgeFinset.card →
      ∀ F : A.Face, ∃ d : G.Dart, A.leftFace d = F := by
  intro hconn hcard _ F
  have hKc : IsClosed (OrdinaryDrawingImage G D) := aux_efid_image_closed G D
  obtain ⟨hFne, hFsub, hFconn, hFmax⟩ := A.face_component F
  have hmax : ∀ C : Set (EuclideanSpace ℝ (Fin 2)), C ⊆ (OrdinaryDrawingImage G D)ᶜ →
      IsConnected C → (C ∩ A.faceSet F).Nonempty → C ⊆ A.faceSet F := by
    intro C hCK hCc hCF
    have h1 := hFmax (A.faceSet F ∪ C) (hFne.mono Set.subset_union_left)
      (Set.union_subset hFsub hCK)
      (IsConnected.union (by rw [Set.inter_comm]; exact hCF) hFconn hCc)
      Set.subset_union_left
    exact Set.subset_union_right.trans h1
  have huniq : ∀ (F' : A.Face) (z : EuclideanSpace ℝ (Fin 2)),
      z ∈ A.faceSet F → z ∈ A.faceSet F' → F' = F := by
    intro F' z hz hz'
    obtain ⟨G', _, hG'⟩ := A.complement_point_face z (hFsub hz)
    exact (hG' F' hz').trans (hG' F hz).symm
  have hVne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hVnt : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨v0⟩ := hVne
  have hne_univ : A.faceSet F ≠ Set.univ := by
    intro h
    have hv : D.vertexPlacement v0 ∈ A.faceSet F := h ▸ Set.mem_univ _
    exact hFsub hv (Or.inl ⟨v0, rfl⟩)
  obtain ⟨p, hp⟩ := nonempty_frontier_iff.mpr ⟨hFne, hne_univ⟩
  have hpcl : p ∈ closure (A.faceSet F) := frontier_subset_closure hp
  have hpK : p ∈ OrdinaryDrawingImage G D := by
    by_contra hpK
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hKc.isOpen_compl p hpK
    have hmeet : (Metric.ball p ε ∩ A.faceSet F).Nonempty :=
      mem_closure_iff.mp hpcl _ Metric.isOpen_ball (Metric.mem_ball_self hε)
    have hsub := hmax _ hball ⟨⟨p, Metric.mem_ball_self hε⟩, (convex_ball p ε).isPreconnected⟩ hmeet
    have hint : p ∈ interior (A.faceSet F) :=
      mem_interior.mpr ⟨_, hsub, Metric.isOpen_ball, Metric.mem_ball_self hε⟩
    exact hp.2 hint
  by_cases hpv : p ∈ Set.range D.vertexPlacement
  · obtain ⟨v, rfl⟩ := hpv
    obtain ⟨w, hvw⟩ := hconn.preconnected.exists_adj_of_nontrivial v
    have hex : ∃ d : G.Dart, d.toProd.2 = v := ⟨⟨(w, v), hvw.symm⟩, rfl⟩
    obtain ⟨y, hyU, hyF⟩ := mem_closure_iff.mp hpcl _ Metric.isOpen_ball
      (Metric.mem_ball_self (A.localDiskRadius_pos v))
    have hyK : y ∈ (OrdinaryDrawingImage G D)ᶜ := hFsub hyF
    have hyne : y ≠ D.vertexPlacement v := by
      rintro rfl
      exact hyK (Or.inl ⟨v, rfl⟩)
    obtain ⟨d, _, sector, hys, _, hsc, _, hsK, ⟨z, ⟨hzs, hzl⟩, _⟩, _, _⟩ :=
      A.vertex_sector_coverage v y hex hyU hyne hyK
    have hsF := hmax sector hsK hsc ⟨y, hys, hyF⟩
    exact ⟨d, huniq _ z (hsF hzs) (A.leftFace_contains d hzl)⟩
  · have hpe : p ∈ ⋃ e : G.edgeFinset, (D.edgeArc e).carrier := by
      rcases hpK with h | h
      · exact absurd h hpv
      · exact h
    simp only [Set.mem_iUnion] at hpe
    obtain ⟨e, hpe⟩ := hpe
    obtain ⟨u, v, huv, he, _⟩ := D.edgeArc_endpoints e
    let d : G.Dart := ⟨(u, v), huv⟩
    have hde : A.dartEdge d = e := Subtype.ext ((A.dartEdge_eq d).trans he.symm)
    have hpri : p ∈ (A.dartArc d).relativeInterior := by
      rw [(A.dartArc d).relativeInterior_eq, A.dartArc_carrier, hde]
      refine ⟨hpe, ?_⟩
      rintro (h | h)
      · rw [A.dartArc_source] at h
        exact hpv ⟨_, h.symm⟩
      · rw [A.dartArc_target] at h
        exact hpv ⟨_, h.symm⟩
    obtain ⟨U, hUo, hpU, hUsub⟩ := A.localComplement_subset_sideStrips d p hpri
    obtain ⟨y, hyU, hyF⟩ := mem_closure_iff.mp hpcl U hUo hpU
    rcases hUsub ⟨hyU, hFsub hyF⟩ with h | h
    · exact ⟨d, huniq _ y hyF (A.leftFace_contains d h)⟩
    · exact ⟨d.symm, huniq _ y hyF (A.leftFace_contains d.symm h)⟩
