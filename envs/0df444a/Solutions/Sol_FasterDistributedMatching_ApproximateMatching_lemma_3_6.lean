-- Prove2me | solution 1 for FasterDistributedMatching.ApproximateMatching.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T21:01:19.393211+00:00
-- url     : https://prove2.me/submissions/45391416-def4-45b5-9cec-31ba58f5febc

import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Virtual
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_StageData
import Mathlib
import Theorems.Thm_Timetabling85_ClassTeacher_prop_2_1
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Basic
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Routing

-- Solutions/Sol_local_flood.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace LocalFlood

def merge {I : Type} (own : Finset (ℕ × I)) (msgs : Multiset (Finset (ℕ × I))) : Finset (ℕ × I) :=
  own ∪ msgs.toFinset.biUnion id

section Flood
variable {V I : Type} [Fintype V] (H : SimpleGraph V) (ids : V → ℕ) (inp : V → I)

def flood : ℕ → V → Finset (ℕ × I)
  | 0,v => {(ids v,inp v)}
  | t+1,v => merge (flood t v) ((H.neighborFinset v).val.map (flood t))

lemma flood_self (t : ℕ) (v : V) : (ids v,inp v) ∈ flood H ids inp t v := by
  induction t with
  | zero => exact mem_singleton_self _
  | succ t ih => exact mem_union_left _ ih

lemma flood_mono (t : ℕ) (v : V) : flood H ids inp t v ⊆ flood H ids inp (t+1) v :=
  subset_union_left

lemma flood_neighbor (t : ℕ) (v u : V) (hvu : H.Adj v u) :
    flood H ids inp t u ⊆ flood H ids inp (t+1) v := by
  intro r hr
  apply mem_union_right
  apply mem_biUnion.mpr
  refine ⟨flood H ids inp t u,?_,hr⟩
  apply Multiset.mem_toFinset.mpr
  exact Multiset.mem_map.mpr ⟨u,(SimpleGraph.mem_neighborFinset H v u).mpr hvu,rfl⟩

lemma flood_authentic (t : ℕ) (v : V) : ∀ r ∈ flood H ids inp t v, ∃ u, r = (ids u,inp u) := by
  induction t generalizing v with
  | zero =>
    intro r hr
    exact ⟨v,mem_singleton.mp hr⟩
  | succ t ih =>
    intro r hr
    rcases mem_union.mp hr with hr|hr
    · exact ih v r hr
    · obtain ⟨S,hS,hr⟩ := mem_biUnion.mp hr
      obtain ⟨u,hu,he⟩ := Multiset.mem_map.mp (Multiset.mem_toFinset.mp hS)
      subst S
      exact ih u r hr

lemma flood_walk (t : ℕ) {v u : V} (w : H.Walk v u) (hw : w.length ≤ t) :
    (ids u,inp u) ∈ flood H ids inp t v := by
  induction t generalizing v with
  | zero =>
    have he : v = u := by
      have hz : w.length = 0 := by omega
      exact (SimpleGraph.Walk.length_eq_zero_iff.mp hz).eq
    subst u
    exact flood_self H ids inp 0 v
  | succ t ih =>
    cases w with
    | nil => exact flood_self H ids inp (t+1) _
    | @cons v u z h w =>
      exact flood_neighbor H ids inp t v u h (ih w (by simpa using hw))

lemma flood_close (t : ℕ) (v u : V) (hc : Close H t v u) :
    (ids u,inp u) ∈ flood H ids inp t v := by
  obtain ⟨w,hw⟩ := hc
  exact flood_walk H ids inp t w hw

lemma flood_unique (hi : Function.Injective ids) (t : ℕ) (v : V) :
    ∀ r ∈ flood H ids inp t v, ∀ s ∈ flood H ids inp t v, r.1 = s.1 → r = s := by
  intro r hr s hs he
  obtain ⟨u,rfl⟩ := flood_authentic H ids inp t v r hr
  obtain ⟨w,rfl⟩ := flood_authentic H ids inp t v s hs
  have huw : u = w := hi he
  rw [huw]

end Flood
end LocalFlood

-- Solutions/Sol_short_blocks.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching

noncomputable section
namespace BlockProof

lemma virtual_degree {N : ℕ} (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ)
    (q : ℝ) (p : Pairing N) (hp : ValidPairing G x q p) (a : Copy p) :
    (virtualGraph p).degree a ≤ 2 := by
  let S := (virtualGraph p).neighborFinset a
  have hinj : Set.InjOn (fun b : Copy p => b.1) (S : Set (Copy p)) := by
    intro b hb c hc hid
    have hab : (virtualGraph p).Adj a b := by simpa [S] using hb
    have hac : (virtualGraph p).Adj a c := by simpa [S] using hc
    cases b with
    | mk vb ib =>
      cases c with
      | mk vc ic =>
        change vb = vc at hid
        subst vc
        have hact := hp.2.2.1 ⟨vb,ib⟩ a.1 hab.2.2
        have huniq := (hp.2.1 vb a.1).mp hact
        have hi : ib = ic := huniq.unique hab.2.2 hac.2.2
        subst ic
        rfl
  have hsub : S.image (fun b : Copy p => b.1) ⊆ group p a := by
    intro v hv
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hv
    have h : (virtualGraph p).Adj a b := by simpa [S] using hb
    exact h.2.1
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  change S.card ≤ 2
  calc
    S.card = (S.image (fun b : Copy p => b.1)).card := (card_image_iff.mpr hinj).symm
    _ ≤ (group p a).card := card_le_card hsub
    _ ≤ 2 := by rcases hp.1 a with h | h <;> omega

section Geometry
variable {V : Type} [Fintype V] (H : SimpleGraph V)

def outside (S : Finset V) (v : V) : Finset V := H.neighborFinset v \ S

def boundary (S : Finset V) : Finset V := S.biUnion (outside H S)

lemma degree_partition (S : Finset V) (v : S) :
    (H.induce (S : Set V)).degree v + (outside H S v.val).card = H.degree v.val := by
  letI : Fintype ↥(S : Set V) := inferInstanceAs (Fintype ↥S)
  have hmap := H.map_neighborFinset_induce (s := (S : Set V)) v
  have hcard := congrArg Finset.card hmap
  have hin : (H.induce (S : Set V)).degree v = (H.neighborFinset v.val ∩ S).card := by
    simp only [card_map,SimpleGraph.card_neighborFinset_eq_degree,Finset.toFinset_coe] at hcard
    refine Eq.trans ?_ hcard
    unfold SimpleGraph.degree SimpleGraph.neighborFinset
    simp only [Set.toFinset_card,← Nat.card_eq_fintype_card]
  rw [hin]
  have h := card_sdiff_add_card_inter (H.neighborFinset v.val) S
  rw [SimpleGraph.card_neighborFinset_eq_degree] at h
  unfold outside
  omega

lemma boundary_card (S : Finset V) (hc : (H.induce (S : Set V)).Connected)
    (hD : ∀ v, H.degree v ≤ 2) : (boundary H S).card ≤ 2 := by
  letI : Fintype ↥(S : Set V) := inferInstanceAs (Fintype ↥S)
  have hsum : (∑ v : S, (H.induce (S : Set V)).degree v) +
      (∑ v : S, (outside H S v.val).card) ≤ 2*S.card := by
    rw [← sum_add_distrib]
    calc
      _ ≤ ∑ _ : S, 2 := sum_le_sum fun v _ => by rw [degree_partition]; exact hD v.val
      _ = _ := by simp [mul_comm]
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges] at hsum
  have hedge := hc.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,← SimpleGraph.edgeFinset_card] at hedge
  have hs : Fintype.card (S : Set V) = S.card := Fintype.card_coe S
  have hout : (∑ v : S, (outside H S v.val).card) ≤ 2 := by omega
  calc
    _ ≤ ∑ v ∈ S, (outside H S v).card := card_biUnion_le
    _ ≤ 2 := by rw [← sum_coe_sort]; exact hout

def ball (r : ℕ) (a : V) : Finset V := univ.filter (Close H r a)

lemma center_mem_ball (r : ℕ) (a : V) : a ∈ ball H r a :=
  mem_filter.mpr ⟨mem_univ a,.intro .nil (by simp)⟩

lemma ball_mono (a : V) {r s : ℕ} (hrs : r ≤ s) : ball H r a ⊆ ball H s a := by
  intro v hv
  obtain ⟨w,hw⟩ := (mem_filter.mp hv).2
  exact mem_filter.mpr ⟨mem_univ v,w,hw.trans hrs⟩

lemma ball_connected (r : ℕ) (a : V) : (H.induce (ball H r a : Set V)).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨a,center_mem_ball H r a⟩,?_⟩
  rintro ⟨v,hv⟩
  obtain ⟨w,hw⟩ := (mem_filter.mp hv).2
  have hall : ∀ c ∈ w.support, c ∈ (ball H r a : Set V) := by
    intro c hc
    exact mem_filter.mpr ⟨mem_univ c,w.takeUntil c hc,(w.length_takeUntil_le_length hc).trans hw⟩
  exact ⟨w.induce (ball H r a : Set V) hall⟩

lemma ball_new_boundary (r : ℕ) (a : V) :
    ball H (r+1) a \ ball H r a ⊆ boundary H (ball H r a) := by
  intro c hc
  obtain ⟨hc,hnot⟩ := mem_sdiff.mp hc
  obtain ⟨w,hw⟩ := (mem_filter.mp hc).2
  have hlen : w.reverse.length ≤ r+1 := by simpa using hw
  cases hrev : w.reverse with
  | nil => exact False.elim (hnot (center_mem_ball H r _))
  | @cons c b a h tail =>
    have ht : tail.length ≤ r := by
      rw [hrev,SimpleGraph.Walk.length_cons] at hlen
      omega
    apply mem_biUnion.mpr
    refine ⟨b,mem_filter.mpr ⟨mem_univ b,tail.reverse,by simpa using ht⟩,?_⟩
    exact mem_sdiff.mpr ⟨by simpa using h.symm,hnot⟩

lemma ball_card_linear (hD : ∀ v, H.degree v ≤ 2) (r : ℕ) (a : V) :
    (ball H r a).card ≤ 2*r+1 := by
  have hzero : ball H 0 a = {a} := by
    ext v
    constructor
    · intro hv
      obtain ⟨w,hw⟩ := (mem_filter.mp hv).2
      exact mem_singleton.mpr (w.eq_of_length_eq_zero (by omega)).symm
    · intro hv
      have hv' := mem_singleton.mp hv
      subst v
      exact center_mem_ball H 0 a
  induction r with
  | zero => simp [hzero]
  | succ r ih =>
    have hnew : (ball H (r+1) a \ ball H r a).card ≤ 2 :=
      (card_le_card (ball_new_boundary H r a)).trans (boundary_card H _ (ball_connected H r a) hD)
    have hcard := card_sdiff_add_card_eq_card (ball_mono H a (show r ≤ r+1 by omega))
    omega

def comp (a : V) : Finset V := univ.filter (H.Reachable a)

lemma ball_subset_comp (r : ℕ) (a : V) : ball H r a ⊆ comp H a := by
  intro v hv
  obtain ⟨w,_⟩ := (mem_filter.mp hv).2
  exact mem_filter.mpr ⟨mem_univ v,⟨w⟩⟩

lemma boundary_ball (r : ℕ) (a : V) : boundary H (ball H r a) = ball H (r+1) a \ ball H r a := by
  apply subset_antisymm
  · intro v hv
    obtain ⟨u,hu,huv⟩ := mem_biUnion.mp hv
    obtain ⟨hadj,hnot⟩ := mem_sdiff.mp huv
    have hadj' : H.Adj u v := by simpa using hadj
    obtain ⟨w,hw⟩ := (mem_filter.mp hu).2
    apply mem_sdiff.mpr
    refine ⟨mem_filter.mpr ⟨mem_univ v,w.append (.cons hadj' .nil),?_⟩,hnot⟩
    simp only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_cons,SimpleGraph.Walk.length_nil]
    omega
  · exact ball_new_boundary H r a

lemma comp_subset_of_boundary_empty (a : V) (S : Finset V) (ha : a ∈ S)
    (hb : boundary H S = ∅) : comp H a ⊆ S := by
  have hclosed (u v : V) (hu : u ∈ S) (huv : H.Adj u v) : v ∈ S := by
    by_contra hv
    have hmem : v ∈ boundary H S :=
      mem_biUnion.mpr ⟨u,hu,mem_sdiff.mpr ⟨by simpa using huv,hv⟩⟩
    rw [hb] at hmem
    exact notMem_empty _ hmem
  have hwalk {u v : V} (w : H.Walk u v) : u ∈ S → v ∈ S := by
    induction w with
    | nil => exact id
    | cons h w ih => intro hu; exact ih (hclosed _ _ hu h)
  intro v hv
  obtain ⟨w⟩ := (mem_filter.mp hv).2
  exact hwalk w ha

lemma ball_grows (r : ℕ) (a : V) (h : ball H r a ≠ comp H a) :
    (ball H r a).card < (ball H (r+1) a).card := by
  have hb : (boundary H (ball H r a)).Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    intro he
    apply h
    exact subset_antisymm (ball_subset_comp H r a)
      (comp_subset_of_boundary_empty H a _ (center_mem_ball H r a) he)
  rw [boundary_ball] at hb
  have hpos : 0 < (ball H (r+1) a \ ball H r a).card := card_pos.mpr hb
  have heq := card_sdiff_add_card_eq_card (ball_mono H a (show r ≤ r+1 by omega))
  omega

lemma ball_card_lower (r : ℕ) (a : V) : min (r+1) (comp H a).card ≤ (ball H r a).card := by
  induction r with
  | zero =>
    have hpos := card_pos.mpr (show (ball H 0 a).Nonempty from ⟨a,center_mem_ball H 0 a⟩)
    exact (min_le_left _ _).trans (by omega)
  | succ r ih =>
    by_cases heq : ball H r a = comp H a
    · apply le_trans (min_le_right _ _)
      rw [← heq]
      exact card_le_card (ball_mono H a (show r ≤ r+1 by omega))
    · have hgrow := ball_grows H r a heq
      have hcard : (ball H r a).card < (comp H a).card := by
        apply card_lt_card
        exact Finset.ssubset_iff_subset_ne.mpr ⟨ball_subset_comp H r a,heq⟩
      omega

lemma comp_card_dist {a b : V} (h : H.Reachable a b) : H.dist a b+1 ≤ (comp H a).card := by
  obtain ⟨w,hpath,hw⟩ := h.exists_path_of_dist
  have hsub : w.support.toFinset ⊆ comp H a := by
    intro v hv
    have hv' : v ∈ w.support := List.mem_toFinset.mp hv
    exact mem_filter.mpr ⟨mem_univ v,⟨w.takeUntil v hv'⟩⟩
  have hc := card_le_card hsub
  rw [List.toFinset_card_of_nodup hpath.support_nodup,SimpleGraph.Walk.length_support,hw] at hc
  exact hc

lemma packing_card (hD : ∀ v, H.degree v ≤ 2) (r : ℕ) (hr : 1 ≤ r)
    (a : V) (S : Finset V)
    (hsep : ∀ b ∈ S, ∀ c ∈ S, b ≠ c → ¬ Close H r b c)
    (hnear : ∀ b ∈ S, Close H (2*r) a b)
    (hlarge : ∀ b ∈ S, r/2+1 ≤ (comp H b).card) : S.card ≤ 10 := by
  have hdisj : (S : Set V).PairwiseDisjoint (fun b => ball H (r/2) b) := by
    intro b hb c hc hbc
    apply disjoint_left.mpr
    intro z hzb hzc
    obtain ⟨p,hp⟩ := (mem_filter.mp hzb).2
    obtain ⟨q,hq⟩ := (mem_filter.mp hzc).2
    apply hsep b hb c hc hbc
    exact ⟨p.append q.reverse,by simp only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_reverse]; omega⟩
  have hsub : S.biUnion (fun b => ball H (r/2) b) ⊆ ball H (2*r+r/2) a := by
    intro z hz
    obtain ⟨b,hb,hz⟩ := mem_biUnion.mp hz
    obtain ⟨p,hp⟩ := hnear b hb
    obtain ⟨q,hq⟩ := (mem_filter.mp hz).2
    exact mem_filter.mpr ⟨mem_univ z,p.append q,by rw [SimpleGraph.Walk.length_append]; omega⟩
  have hcount : S.card*(r/2+1) ≤ 2*(2*r+r/2)+1 := by
    calc
      _ = ∑ _ ∈ S, (r/2+1) := by simp
      _ ≤ ∑ b ∈ S, (ball H (r/2) b).card := by
        apply sum_le_sum
        intro b hb
        have h := ball_card_lower H (r/2) b
        rw [min_eq_left (hlarge b hb)] at h
        exact h
      _ = (S.biUnion (fun b => ball H (r/2) b)).card := (card_biUnion hdisj).symm
      _ ≤ (ball H (2*r+r/2) a).card := card_le_card hsub
      _ ≤ _ := ball_card_linear H hD _ _
  by_contra h
  have hh : 11*(r/2+1) ≤ S.card*(r/2+1) := Nat.mul_le_mul_right _ (by omega)
  omega

def filteredPower (r : ℕ) (S : Finset V) : SimpleGraph V where
  Adj a b := a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ Close H r a b
  symm := ⟨by
    intro a b h
    obtain ⟨w,hw⟩ := h.2.2.2
    exact ⟨h.2.1,h.1,h.2.2.1.symm,w.reverse,by simpa using hw⟩⟩
  loopless := ⟨by intro a h; exact h.2.2.1 rfl⟩

lemma filteredPower_degree (hD : ∀ v, H.degree v ≤ 2) (r : ℕ) (hr : 1 ≤ r)
    (S : Finset V) (hsep : ∀ b ∈ S, ∀ c ∈ S, b ≠ c → ¬ Close H r b c) (a : V) :
    (filteredPower H (2*r) S).degree a ≤ 10 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  let T := (filteredPower H (2*r) S).neighborFinset a
  have hT (b : V) (hb : b ∈ T) : a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ Close H (2*r) a b := by
    exact (SimpleGraph.mem_neighborFinset (filteredPower H (2*r) S) a b).mp hb
  have hsepT : ∀ b ∈ T, ∀ c ∈ T, b ≠ c → ¬ Close H r b c := by
    intro b hb c hc hbc
    exact hsep b (hT b hb).2.1 c (hT c hc).2.1 hbc
  have hnear : ∀ b ∈ T, Close H (2*r) a b := fun b hb => (hT b hb).2.2.2
  have hlarge : ∀ b ∈ T, r/2+1 ≤ (comp H b).card := by
    intro b hb
    obtain ⟨w,hw⟩ := (hT b hb).2.2.2
    have hreach : H.Reachable b a := ⟨w.reverse⟩
    have hnclose : ¬ Close H r b a := hsep b (hT b hb).2.1 a (hT b hb).1 (hT b hb).2.2.1.symm
    have hd : r < H.dist b a := by
      by_contra hh
      obtain ⟨q,hq⟩ := hreach.exists_walk_length_eq_dist
      exact hnclose ⟨q,by omega⟩
    have hcomp := comp_card_dist H hreach
    omega
  exact packing_card H hD r hr a T hsepT hnear hlarge

end Geometry

end BlockProof

-- Solutions/Sol_residual_geometry.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingRounding
section Residual
variable {V : Type} [Fintype V] (H : SimpleGraph V) (C : Finset V)

def residualGraph : SimpleGraph V where
  Adj a b := H.Adj a b ∧ a ∉ C ∧ b ∉ C
  symm := ⟨by rintro a b ⟨h,ha,hb⟩; exact ⟨h.symm,hb,ha⟩⟩
  loopless := ⟨by intro a h; exact h.1.ne rfl⟩

lemma residual_le : residualGraph H C ≤ H := fun _ _ h => h.1

lemma residual_reachable_uncut {a b : V} (ha : a ∉ C)
    (hab : (residualGraph H C).Reachable a b) : b ∉ C := by
  obtain ⟨w⟩ := hab
  induction w with
  | nil => exact ha
  | @cons a b c h w ih => exact ih h.2.2

lemma residual_reachable_of_walk {a b : V} (w : H.Walk a b)
    (hall : ∀ z ∈ w.support, z ∉ C) : (residualGraph H C).Reachable a b := by
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c h w ih =>
    have ha : a ∉ C := hall a (by simp)
    have hb : b ∉ C := hall b (by simp)
    have ht : ∀ z ∈ w.support, z ∉ C := fun z hz => hall z (by simp [hz])
    exact (SimpleGraph.Adj.reachable (show (residualGraph H C).Adj a b from ⟨h,ha,hb⟩)).trans (ih ht)

lemma residual_component_connected (a : V) :
    (H.induce (BlockProof.comp (residualGraph H C) a : Set V)).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  have ha : a ∈ BlockProof.comp (residualGraph H C) a := mem_filter.mpr ⟨mem_univ _,SimpleGraph.Reachable.refl _⟩
  refine ⟨⟨a,ha⟩,?_⟩
  rintro ⟨v,hv⟩
  obtain ⟨w⟩ := (mem_filter.mp hv).2
  let path := w.mapLe (residual_le H C)
  have hall : ∀ z ∈ path.support, z ∈ (BlockProof.comp (residualGraph H C) a : Set V) := by
    intro z hz
    have hz' : z ∈ w.support := by simpa only [path,SimpleGraph.Walk.support_mapLe_eq_support] using hz
    exact mem_filter.mpr ⟨mem_univ _,⟨w.takeUntil z hz'⟩⟩
  exact ⟨path.induce (BlockProof.comp (residualGraph H C) a : Set V) hall⟩

end Residual
section Cover
variable {V : Type} [Fintype V] (H : SimpleGraph V)

lemma boundary_ball_cover_card (hD : ∀ v, H.degree v ≤ 2) (S : Finset V)
    (hconn : (H.induce (S : Set V)).Connected) (r : ℕ)
    (hcover : ∀ v ∈ S, ∃ c ∈ BlockProof.boundary H S, Close H r c v) :
    S.card ≤ 2*(2*r+1) := by
  have hsub : S ⊆ (BlockProof.boundary H S).biUnion (BlockProof.ball H r) := by
    intro v hv
    obtain ⟨c,hc,hcv⟩ := hcover v hv
    exact mem_biUnion.mpr ⟨c,hc,mem_filter.mpr ⟨mem_univ _,hcv⟩⟩
  have hcard := BlockProof.boundary_card H S hconn hD
  calc
    _ ≤ ((BlockProof.boundary H S).biUnion (BlockProof.ball H r)).card := card_le_card hsub
    _ ≤ ∑ c ∈ BlockProof.boundary H S, (BlockProof.ball H r c).card := card_biUnion_le
    _ ≤ ∑ _ ∈ BlockProof.boundary H S, (2*r+1) := sum_le_sum (fun c _ => BlockProof.ball_card_linear H hD r c)
    _ = (BlockProof.boundary H S).card*(2*r+1) := by simp [nsmul_eq_mul]
    _ ≤ 2*(2*r+1) := Nat.mul_le_mul_right _ hcard

end Cover
end MatchingRounding

-- Solutions/Sol_residual_boundary.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingRounding
section Boundary
variable {V : Type} [Fintype V] (H : SimpleGraph V) (C : Finset V)

lemma path_boundary (root : V) (hr : root ∉ C) (v c : V)
    (hv : v ∈ BlockProof.comp (residualGraph H C) root) (hc : c ∈ C)
    (w : H.Walk v c) (hp : w.IsPath)
    (hinner : ∀ z ∈ w.support, z ≠ c → z ∉ C) :
    c ∈ BlockProof.boundary H (BlockProof.comp (residualGraph H C) root) := by
  let S := BlockProof.comp (residualGraph H C) root
  have hvNot : v ∉ C := residual_reachable_uncut H C hr (mem_filter.mp hv).2
  have hvc : v ≠ c := fun he => hvNot (he ▸ hc)
  have hnil : ¬w.Nil := fun h => hvc h.eq
  have hsupport := w.support_dropLast_concat hnil
  have hnodup : (w.dropLast.support++[c]).Nodup := by rw [hsupport]; exact hp.support_nodup
  have hcNot : c ∉ w.dropLast.support := fun h => List.disjoint_of_nodup_append hnodup h (by simp)
  have hleft : ∀ z ∈ w.dropLast.support, z ∉ C := by
    intro z hz
    have hzfull : z ∈ w.support := by rw [←hsupport]; exact List.mem_append.mpr (Or.inl hz)
    exact hinner z hzfull (fun he => hcNot (he ▸ hz))
  have hreach := residual_reachable_of_walk H C w.dropLast hleft
  have hlast : w.penultimate ∈ S :=
    mem_filter.mpr ⟨mem_univ _,((mem_filter.mp hv).2).trans hreach⟩
  have hcOut : c ∉ S := fun h => residual_reachable_uncut H C hr (mem_filter.mp h).2 hc
  apply mem_biUnion.mpr
  refine ⟨w.penultimate,hlast,mem_sdiff.mpr ⟨?_,hcOut⟩⟩
  exact (SimpleGraph.mem_neighborFinset H w.penultimate c).mpr (w.adj_penultimate hnil)

end Boundary
end MatchingRounding

-- Solutions/Sol_selected_copies.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingRounding
variable {N : ℕ} {p : Pairing N}

def selectedSet (B : BlockAssignment p) (s : Copy p → Copy p) : Finset (Copy p) :=
  univ.filter (fun c => ∃ a, B a = some a ∧ s a = c)

lemma mem_selectedSet (B : BlockAssignment p) (s : Copy p → Copy p) (c : Copy p) :
    c ∈ selectedSet B s ↔ ∃ a, B a = some a ∧ s a = c := by simp only [selectedSet,mem_filter,mem_univ,true_and]

lemma selected_in_block_unique (B : BlockAssignment p) (s : Copy p → Copy p) (hs : ValidCuts B s)
    (a c : Copy p) (hc : c ∈ block B a) (hsel : c ∈ selectedSet B s) : s a = c := by
  obtain ⟨b,hb,he⟩ := (mem_selectedSet B s c).mp hsel
  have hh := (mem_filter.mp (hs b hb)).2
  rw [he] at hh
  have hba : b = a := Option.some.inj (hh.symm.trans (mem_filter.mp hc).2)
  rwa [hba] at he

lemma chosen_selected (B : BlockAssignment p) (s : Copy p → Copy p) (a : Copy p) (ha : B a = some a) :
    s a ∈ selectedSet B s := (mem_selectedSet B s (s a)).mpr ⟨a,ha,rfl⟩

lemma selected_creator_count (B : BlockAssignment p) (s : Copy p → Copy p) (hs : ValidCuts B s)
    (v : Fin N) : ((selectedSet B s).filter (fun c => c.1 = v)).card = cutCount B s v := by
  unfold cutCount
  symm
  apply card_bij (fun a _ => s a)
  · intro a ha
    have h := (mem_filter.mp ha).2
    exact mem_filter.mpr ⟨chosen_selected B s a h.1,h.2⟩
  · intro a ha b hb he
    have hma := (mem_filter.mp (hs a (mem_filter.mp ha).2.1)).2
    have hmb := (mem_filter.mp (hs b (mem_filter.mp hb).2.1)).2
    rw [he] at hma
    exact Option.some.inj (hma.symm.trans hmb)
  · intro c hc
    obtain ⟨hsel,hcreator⟩ := mem_filter.mp hc
    obtain ⟨a,ha,he⟩ := (mem_selectedSet B s c).mp hsel
    refine ⟨a,mem_filter.mpr ⟨mem_univ _,ha,?_⟩,he⟩
    rw [he]
    exact hcreator

end MatchingRounding

-- Solutions/Sol_rounding_component_bound.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingRounding

lemma component_eq_of_reachable {V : Type} [Fintype V] (H : SimpleGraph V) (a b : V)
    (hab : H.Reachable a b) : BlockProof.comp H a = BlockProof.comp H b := by
  ext c
  simp only [BlockProof.comp,mem_filter,mem_univ,true_and]
  exact ⟨fun h => hab.symm.trans h,fun h => hab.trans h⟩

variable {N : ℕ} {p : Pairing N}

lemma internal_block_path (ell : ℕ) (B : BlockAssignment p) (hB : ValidBlocks ell B)
    (v a c : Copy p) (hva : B v = some a) (hc : c ∈ block B a) :
    ∃ w : (virtualGraph p).Walk v c, w.IsPath ∧ w.length ≤ 65*ell ∧
      ∀ z ∈ w.support, z ∈ block B a := by
  obtain ⟨walk,hwalk⟩ := (hB.2 v a hva).2.2.2 c hc
  let path := walk.toPath
  have hs : ∀ z ∈ path.val.support, z ∈ block B a :=
    fun z hz => hwalk z (walk.support_toPath_subset_support hz)
  have hsub : path.val.support.toFinset ⊆ block B a := fun z hz => hs z (List.mem_toFinset.mp hz)
  have hcard := card_le_card hsub
  rw [List.toFinset_card_of_nodup path.property.support_nodup,SimpleGraph.Walk.length_support] at hcard
  have hsize := (hB.2 v a hva).2.2.1
  exact ⟨path.val,path.property,by omega,hs⟩

lemma residual_component_bound (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (hp : ValidPairing G x q p) (ell : ℕ) (hell : 2 ≤ ell) (B : BlockAssignment p)
    (hB : ValidBlocks ell B) (s : Copy p → Copy p) (hs : ValidCuts B s)
    (root : Copy p) (hr : root ∉ selectedSet B s) :
    (BlockProof.comp (residualGraph (virtualGraph p) (selectedSet B s)) root).card ≤ 260*ell+2 := by
  let H := virtualGraph p
  let C := selectedSet B s
  let J := residualGraph H C
  let S := BlockProof.comp J root
  change S.card ≤ _
  have hD := BlockProof.virtual_degree G x q p hp
  have hReach (v : Copy p) (hv : v ∈ S) : H.Reachable root v := by
    have hJ : J.Reachable root v := by simpa only [S,BlockProof.comp,mem_filter,mem_univ,true_and] using hv
    obtain ⟨w⟩ := hJ
    exact ⟨w.mapLe (residual_le H C)⟩
  cases hRoot : B root with
  | none =>
    have hsmall := (hB.1 root).mp hRoot
    have hsub : S ⊆ component p root := by
      intro v hv
      exact mem_filter.mpr ⟨mem_univ _,hReach v hv⟩
    have hcard := card_le_card hsub
    omega
  | some leader =>
    have hlarge : ell ≤ (component p root).card := by
      have hn : ¬(component p root).card < ell := by
        intro h
        have he := (hB.1 root).mpr h
        rw [hRoot] at he
        cases he
      omega
    have hcover (v : Copy p) (hv : v ∈ S) :
        ∃ c ∈ BlockProof.boundary H S, Close H (65*ell) c v := by
      have hcomp : component p root = component p v := by
        ext z
        simp only [component,mem_filter,mem_univ,true_and]
        exact ⟨fun hz => (hReach v hv).symm.trans hz,fun hz => (hReach v hv).trans hz⟩
      have hvB : B v ≠ none := by
        intro he
        have hvsmall := (hB.1 v).mp he
        rw [←hcomp] at hvsmall
        omega
      obtain ⟨a,hva⟩ := Option.ne_none_iff_exists'.mp hvB
      have hleader := (hB.2 v a hva).1
      have hc : s a ∈ block B a := hs a hleader
      obtain ⟨w,hw,hLength,hSupport⟩ := internal_block_path ell B hB v a (s a) hva hc
      have hcSelected : s a ∈ C := chosen_selected B s a hleader
      have hinner : ∀ z ∈ w.support, z ≠ s a → z ∉ C := by
        intro z hz hne hsel
        have he := selected_in_block_unique B s hs a z (hSupport z hz) hsel
        exact hne he.symm
      have hboundary := path_boundary H C root hr v (s a) hv hcSelected w hw hinner
      exact ⟨s a,hboundary,w.reverse,by simpa using hLength⟩
    have hc := boundary_ball_cover_card H hD S (residual_component_connected H C root) (65*ell) hcover
    change S.card ≤ _
    nlinarith

end MatchingRounding

-- Solutions/Sol_edge_chains.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingRounding
section Chains
variable {V : Type} [Fintype V] (H : SimpleGraph V) (C : Finset V)

def edgeChain : SimpleGraph H.edgeSet where
  Adj e f := e ≠ f ∧ ∃ v, v ∉ C ∧ v ∈ (e.val:Sym2 V) ∧ v ∈ (f.val:Sym2 V)
  symm := ⟨by rintro e f ⟨hne,v,hv,he,hf⟩; exact ⟨hne.symm,v,hv,hf,he⟩⟩
  loopless := ⟨by intro e h; exact h.1 rfl⟩

lemma same_edge_residual_reachable (e : H.edgeSet) (u v : V)
    (hu : u ∈ e.val) (hv : v ∈ e.val) (huc : u ∉ C) (hvc : v ∉ C) :
    (residualGraph H C).Reachable u v := by
  by_cases huv : u = v
  · subst v
    exact SimpleGraph.Reachable.refl _
  · have he : e.val = s(u,v) := (Sym2.mem_and_mem_iff huv).mp ⟨hu,hv⟩
    have hAdj : H.Adj u v := H.mem_edgeSet.mp (show s(u,v) ∈ H.edgeSet from by rw [←he]; exact e.property)
    exact (show (residualGraph H C).Adj u v from ⟨hAdj,huc,hvc⟩).reachable

lemma chain_reachable_incident (root : V) (hr : root ∉ C) (e f : H.edgeSet)
    (he : root ∈ e.val) (hf : (edgeChain H C).Reachable e f) :
    ∃ v ∈ BlockProof.comp (residualGraph H C) root, v ∈ f.val := by
  obtain ⟨w⟩ := hf
  have hstart : ∃ v ∈ BlockProof.comp (residualGraph H C) root, v ∈ e.val :=
    ⟨root,mem_filter.mpr ⟨mem_univ _,SimpleGraph.Reachable.refl _⟩,he⟩
  clear he
  induction w with
  | nil => exact hstart
  | @cons e f g h w ih =>
    obtain ⟨u,hu,hue⟩ := hstart
    obtain ⟨hne,v,hvc,hve,hvf⟩ := h
    have huReach : (residualGraph H C).Reachable root u := by
      simpa only [BlockProof.comp,mem_filter,mem_univ,true_and] using hu
    have huc : u ∉ C := residual_reachable_uncut H C hr huReach
    have huv := same_edge_residual_reachable H C e u v hue hve huc hvc
    have hvComp : v ∈ BlockProof.comp (residualGraph H C) root :=
      mem_filter.mpr ⟨mem_univ _,huReach.trans huv⟩
    exact ih ⟨v,hvComp,hvf⟩

lemma chain_component_card (hD : ∀ v, H.degree v ≤ 2) (root : V) (hr : root ∉ C)
    (e : H.edgeSet) (he : root ∈ e.val) :
    (BlockProof.comp (edgeChain H C) e).card ≤ 2*(BlockProof.comp (residualGraph H C) root).card := by
  let S := BlockProof.comp (residualGraph H C) root
  let E := BlockProof.comp (edgeChain H C) e
  change E.card ≤ 2*S.card
  have hsub : E.image Subtype.val ⊆ S.biUnion (fun v => H.incidenceFinset v) := by
    intro edge hedge
    obtain ⟨f,hf,rfl⟩ := mem_image.mp hedge
    have hfReach : (edgeChain H C).Reachable e f := by
      simpa only [E,BlockProof.comp,mem_filter,mem_univ,true_and] using hf
    obtain ⟨v,hv,hvf⟩ := chain_reachable_incident H C root hr e f he hfReach
    exact mem_biUnion.mpr ⟨v,hv,(H.mem_incidenceFinset v f.val).mpr ⟨f.property,hvf⟩⟩
  have hcard : (E.image Subtype.val).card = E.card := card_image_of_injective _ Subtype.val_injective
  calc
    _ = (E.image Subtype.val).card := hcard.symm
    _ ≤ (S.biUnion (fun v => H.incidenceFinset v)).card := card_le_card hsub
    _ ≤ ∑ v ∈ S, (H.incidenceFinset v).card := card_biUnion_le
    _ ≤ ∑ _ ∈ S, (2:ℕ) := sum_le_sum (fun v _ => by rw [H.card_incidenceFinset_eq_degree]; exact hD v)
    _ = 2*S.card := by simp [mul_comm]

lemma chain_component_singleton (e : H.edgeSet) (hall : ∀ v ∈ e.val, v ∈ C) :
    BlockProof.comp (edgeChain H C) e = {e} := by
  ext f
  simp only [BlockProof.comp,mem_filter,mem_univ,true_and,mem_singleton]
  constructor
  · rintro ⟨w⟩
    cases w with
    | nil => rfl
    | @cons e g f h w =>
      obtain ⟨hne,v,hvc,hve,hvg⟩ := h
      exact (hvc (hall v hve)).elim
  · intro h
    subst f
    exact SimpleGraph.Reachable.refl _

end Chains

lemma edge_chain_block_bound {N : ℕ} (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (p : Pairing N) (hp : ValidPairing G x q p) (ell : ℕ) (hell : 2 ≤ ell)
    (B : BlockAssignment p) (hB : ValidBlocks ell B) (s : Copy p → Copy p) (hs : ValidCuts B s)
    (e : (virtualGraph p).edgeSet) :
    (BlockProof.comp (edgeChain (virtualGraph p) (selectedSet B s)) e).card ≤ 522*ell := by
  by_cases h : ∃ v ∈ e.val, v ∉ selectedSet B s
  · obtain ⟨v,hv,hvc⟩ := h
    have hc := chain_component_card (virtualGraph p) (selectedSet B s)
      (BlockProof.virtual_degree G x q p hp) v hvc e hv
    have hb := residual_component_bound G x q hp ell hell B hB s hs v hvc
    omega
  · have hall : ∀ v ∈ e.val, v ∈ selectedSet B s := by
      intro v hv
      by_contra hvc
      exact h ⟨v,hv,hvc⟩
    rw [chain_component_singleton (virtualGraph p) (selectedSet B s) e hall,card_singleton]
    omega

end MatchingRounding

-- Solutions/Sol_component_sums.lean

open Classical Finset
noncomputable section
namespace MatchingRounding

lemma mem_comp_iff {V : Type} [Fintype V] (H : SimpleGraph V) (a b : V) :
    b ∈ BlockProof.comp H a ↔ H.Reachable a b := by
  simp only [BlockProof.comp,mem_filter,mem_univ,true_and]

lemma comp_self {V : Type} [Fintype V] (H : SimpleGraph V) (a : V) : a ∈ BlockProof.comp H a :=
  (mem_comp_iff H a a).mpr (SimpleGraph.Reachable.refl a)

lemma sum_components_nonnegative {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (f : V → ℝ)
    (h : ∀ a, 0 ≤ ∑ b ∈ BlockProof.comp H a, f b) : 0 ≤ ∑ a, f a := by
  let P := univ.image (BlockProof.comp H)
  have hfiber (S : Finset V) (hS : S ∈ P) :
      univ.filter (fun a => BlockProof.comp H a = S) = S := by
    obtain ⟨r,hr,rfl⟩ := mem_image.mp hS
    ext a
    simp only [mem_filter,mem_univ,true_and]
    constructor
    · intro heq
      rw [←heq]
      exact comp_self H a
    · intro ha
      exact component_eq_of_reachable H a r ((mem_comp_iff H r a).mp ha).symm
  have heq := sum_fiberwise_of_maps_to (s:=univ) (t:=P) (g:=BlockProof.comp H)
    (fun a _ => mem_image.mpr ⟨a,mem_univ _,rfl⟩) f
  rw [←heq]
  apply sum_nonneg
  intro S hS
  rw [hfiber S hS]
  obtain ⟨r,hr,rfl⟩ := mem_image.mp hS
  exact h r

lemma sum_edge_subtype {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (f : Sym2 V → ℝ) :
    (∑ e : H.edgeSet, f e.val) = ∑ e ∈ H.edgeFinset, f e := by
  apply sum_bij (fun e _ => e.val)
  · intro e _
    exact H.mem_edgeFinset.mpr e.property
  · intro e _ g _ heq
    exact Subtype.ext heq
  · intro e he
    exact ⟨⟨e,H.mem_edgeFinset.mp he⟩,mem_univ _,rfl⟩
  · intro e he
    rfl

section Components
variable {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (C : Finset V)

def componentEdges (e : H.edgeSet) : Finset (Sym2 V) :=
  (BlockProof.comp (edgeChain H C) e).image Subtype.val

lemma componentEdges_subset (e : H.edgeSet) : componentEdges H C e ⊆ H.edgeFinset := by
  intro f hf
  obtain ⟨g,hg,rfl⟩ := mem_image.mp hf
  exact H.mem_edgeFinset.mpr g.property

lemma mem_componentEdges (e f : H.edgeSet) :
    f.val ∈ componentEdges H C e ↔ (edgeChain H C).Reachable e f := by
  constructor
  · intro hf
    obtain ⟨g,hg,heq⟩ := mem_image.mp hf
    have hgf : g = f := Subtype.ext heq
    subst g
    exact (mem_comp_iff _ _ _).mp hg
  · intro hf
    exact mem_image.mpr ⟨f,(mem_comp_iff _ _ _).mpr hf,rfl⟩

lemma componentEdges_eq (e f : H.edgeSet) (h : (edgeChain H C).Reachable e f) :
    componentEdges H C e = componentEdges H C f := by
  unfold componentEdges
  rw [component_eq_of_reachable _ e f h]

lemma componentEdges_self (e : H.edgeSet) : e.val ∈ componentEdges H C e :=
  (mem_componentEdges H C e e).mpr (SimpleGraph.Reachable.refl e)

lemma incident_component (e : H.edgeSet) (a : V) (ha : a ∈ e.val) (hac : a ∉ C) :
    (componentEdges H C e).filter (fun f => a ∈ f) = H.incidenceFinset a := by
  ext f
  rw [mem_filter,H.mem_incidenceFinset]
  constructor
  · rintro ⟨hf,haf⟩
    exact ⟨H.mem_edgeFinset.mp (componentEdges_subset H C e hf),haf⟩
  · rintro ⟨hf,haf⟩
    refine ⟨?_,haf⟩
    let g : H.edgeSet := ⟨f,hf⟩
    apply (mem_componentEdges H C e g).mpr
    by_cases heq : e = g
    · exact heq ▸ (SimpleGraph.Reachable.refl e : (edgeChain H C).Reachable e e)
    · exact (show (edgeChain H C).Adj e g from ⟨heq,a,hac,ha,haf⟩).reachable

end Components
end MatchingRounding

-- Solutions/Sol_named_signs.lean

open Classical Finset
noncomputable section
namespace MatchingRounding

structure NamedEdge where
  name : ℕ
  ends : Sym2 ℕ
  coefficient : ℝ

namespace NamedEdgeData

def names (D : Finset NamedEdge) : Finset ℕ := D.image NamedEdge.name

def vertices (D : Finset NamedEdge) : Finset ℕ := D.biUnion (fun e => e.ends.toFinset)

def incident (D : Finset NamedEdge) (v : ℕ) : Finset ℕ := (D.filter (fun e => v ∈ e.ends)).image NamedEdge.name

def bitSign (theta : ℕ → Bool) (i : ℕ) : ℝ := if theta i then 1 else -1

def Admissible (D : Finset NamedEdge) (theta : ℕ → Bool) : Prop :=
  ∀ v ∈ vertices D, (incident D v).card = 2 → (∑ i ∈ incident D v, bitSign theta i) = 0

def raw (D : Finset NamedEdge) : ℕ → Bool :=
  if h : ∃ theta, Admissible D theta then h.choose else fun _ => false

def score (D : Finset NamedEdge) (theta : ℕ → Bool) : ℝ := ∑ e ∈ D, e.coefficient*bitSign theta e.name

def orientation (D : Finset NamedEdge) : ℝ := if 0 ≤ score D (raw D) then 1 else -1

def sign (D : Finset NamedEdge) (i : ℕ) : ℝ :=
  if i ∈ names D then orientation D*bitSign (raw D) i else 0

lemma raw_admissible (D : Finset NamedEdge) (h : ∃ theta, Admissible D theta) : Admissible D (raw D) := by
  unfold raw
  rw [dif_pos h]
  exact h.choose_spec

lemma sign_unit (D : Finset NamedEdge) (i : ℕ) (hi : i ∈ names D) : sign D i = 1 ∨ sign D i = -1 := by
  unfold sign
  rw [if_pos hi]
  unfold orientation bitSign
  split_ifs <;> norm_num

lemma incident_subset (D : Finset NamedEdge) (v : ℕ) : incident D v ⊆ names D := by
  intro i hi
  obtain ⟨e,he,rfl⟩ := mem_image.mp hi
  exact mem_image.mpr ⟨e,(mem_filter.mp he).1,rfl⟩

lemma sign_balanced (D : Finset NamedEdge) (h : ∃ theta, Admissible D theta)
    (v : ℕ) (hv : v ∈ vertices D) (hdeg : (incident D v).card = 2) :
    (∑ i ∈ incident D v, sign D i) = 0 := by
  have hraw := raw_admissible D h v hv hdeg
  have he (i : ℕ) (hi : i ∈ incident D v) : sign D i = orientation D*bitSign (raw D) i :=
    if_pos (incident_subset D v hi)
  rw [sum_congr rfl (fun i hi => he i hi),←mul_sum,hraw,mul_zero]

lemma score_nonnegative (D : Finset NamedEdge) : 0 ≤ ∑ e ∈ D, e.coefficient*sign D e.name := by
  have he (e : NamedEdge) (he : e ∈ D) : e.coefficient*sign D e.name =
      orientation D*(e.coefficient*bitSign (raw D) e.name) := by
    unfold sign
    have hn : e.name ∈ names D := mem_image.mpr ⟨e,he,rfl⟩
    rw [if_pos hn]
    ring
  rw [sum_congr rfl (fun e he' => he e he'),←mul_sum]
  change 0 ≤ orientation D*score D (raw D)
  unfold orientation
  split_ifs with h
  · simpa only [one_mul] using h
  · simp only [neg_one_mul]
    linarith

end NamedEdgeData
end MatchingRounding

-- Solutions/Sol_named_components.lean

open Classical Finset
noncomputable section
namespace MatchingRounding

-- The query is determined entirely by a finite named dictionary.
def finiteComponent {W : Type} (D : Finset W) (J : SimpleGraph W) (name : W → ℕ) (i : ℕ) : Finset W :=
  D.filter (fun w => ∃ r ∈ D, name r = i ∧ J.Reachable r w)

section Transport
variable {V W : Type} [Fintype V] [DecidableEq V] [DecidableEq W]
    (H : SimpleGraph V) (D : Finset W) (J : SimpleGraph W) (f : V → W)
    (hauth : ∀ w ∈ D, ∃ v, f v = w)
    (hclosed : ∀ a b, J.Adj a b → a ∈ D ∧ b ∈ D)
    (hsound : ∀ a b, J.Adj (f a) (f b) → H.Adj a b)

include hauth hclosed hsound in
lemma reachable_named_sound (a : V) (w : W) (h : J.Reachable (f a) w) :
    ∃ b, f b = w ∧ H.Reachable a b := by
  have aux : ∀ {u w : W}, (walk : J.Walk u w) → ∀ a : V, f a = u →
      ∃ b, f b = w ∧ H.Reachable a b := by
    intro u w walk
    induction walk with
    | nil =>
      intro a ha
      exact ⟨a,ha,SimpleGraph.Reachable.refl a⟩
    | @cons u v w huv walk ih =>
      intro a ha
      obtain ⟨b,hb⟩ := hauth v (hclosed u v huv).2
      have hab : H.Adj a b := hsound a b (by rw [ha,hb]; exact huv)
      obtain ⟨c,hc,hr⟩ := ih b hb
      exact ⟨c,hc,hab.reachable.trans hr⟩
  obtain ⟨walk⟩ := h
  exact aux walk a rfl

end Transport

lemma finiteComponent_eq {V W : Type} [Fintype V] [DecidableEq V] [DecidableEq W]
    (H : SimpleGraph V) (D : Finset W) (J : SimpleGraph W) (f : V → W) (name : W → ℕ)
    (hauth : ∀ w ∈ D, ∃ v, f v = w)
    (hclosed : ∀ a b, J.Adj a b → a ∈ D ∧ b ∈ D)
    (hsound : ∀ a b, J.Adj (f a) (f b) → H.Adj a b)
    (hcomplete : ∀ a b, f a ∈ D → f b ∈ D → H.Adj a b → J.Adj (f a) (f b))
    (hname : Function.Injective (fun a => name (f a))) (root : V)
    (hcover : ∀ a ∈ BlockProof.comp H root, f a ∈ D) :
    finiteComponent D J name (name (f root)) = (BlockProof.comp H root).image f := by
  have hroot := hcover root (comp_self H root)
  have forward : ∀ a, H.Reachable root a → J.Reachable (f root) (f a) := by
    intro a hr
    obtain ⟨walk⟩ := hr
    have aux : ∀ {u v : V}, (walk : H.Walk u v) → H.Reachable root u → J.Reachable (f u) (f v) := by
      intro u v walk
      induction walk with
      | nil => intro _; exact SimpleGraph.Reachable.refl _
      | @cons u v w huv walk ih =>
        intro hru
        have hrv := hru.trans huv.reachable
        have hjuv := hcomplete u v (hcover u ((mem_comp_iff H root u).mpr hru))
          (hcover v ((mem_comp_iff H root v).mpr hrv)) huv
        exact hjuv.reachable.trans (ih hrv)
    exact aux walk (SimpleGraph.Reachable.refl root)
  ext w
  constructor
  · intro hw
    obtain ⟨hwD,r,hrD,hn,hrw⟩ := mem_filter.mp hw
    obtain ⟨a,ha⟩ := hauth r hrD
    have haroot : a = root := hname (by change name (f a) = name (f root); rw [ha]; exact hn)
    have hreach : J.Reachable (f root) w := by simpa only [←ha,haroot] using hrw
    obtain ⟨b,hb,hbReach⟩ := reachable_named_sound H D J f hauth hclosed hsound root w hreach
    exact mem_image.mpr ⟨b,(mem_comp_iff H root b).mpr hbReach,hb⟩
  · intro hw
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hw
    exact mem_filter.mpr ⟨hcover a ha,f root,hroot,rfl,forward a ((mem_comp_iff H root a).mp ha)⟩

end MatchingRounding

-- Solutions/Sol_two_schedule.lean

open Classical Finset
noncomputable section
namespace MatchingRounding

variable {V : Type} [Fintype V]

def TwoSchedule (R : V → V → ℕ) (X : V → V → Fin 2 → ℕ) : Prop :=
  (∀ u v, (∑ k, X u v k) = R u v) ∧
  (∀ u k, (∑ v, X u v k) ≤ 1) ∧ (∀ v k, (∑ u, X u v k) ≤ 1)

lemma two_schedule_exists (R : V → V → ℕ)
    (hrow : ∀ u, (∑ v, R u v) ≤ 2) (hcol : ∀ v, (∑ u, R u v) ≤ 2) :
    ∃ X : V → V → Fin 2 → ℕ, TwoSchedule R X := by
  let e := Fintype.equivFin V
  let matrix := fun i j => R (e.symm i) (e.symm j)
  have hr (i : Fin (Fintype.card V)) : Timetabling85.ClassTeacher.rowSum matrix i ≤ 2 := by
    change (∑ j, R (e.symm i) (e.symm j)) ≤ 2
    rw [e.symm.sum_comp (fun v => R (e.symm i) v)]
    exact hrow _
  have hc (j : Fin (Fintype.card V)) : Timetabling85.ClassTeacher.colSum matrix j ≤ 2 := by
    change (∑ i, R (e.symm i) (e.symm j)) ≤ 2
    rw [e.symm.sum_comp (fun u => R u (e.symm j))]
    exact hcol _
  obtain ⟨x,hx⟩ := (Timetabling85.ClassTeacher.prop_2_1 matrix 2).mpr ⟨hc,hr⟩
  refine ⟨fun u v k => x (e u) (e v) k,?_,?_,?_⟩
  · intro u v
    have hh := hx.1 (e u) (e v)
    simpa only [matrix,Equiv.symm_apply_apply] using hh
  · intro u k
    rw [e.sum_comp (fun j => x (e u) j k)]
    exact hx.2.1 (e u) k
  · intro v k
    rw [e.sum_comp (fun i => x i (e v) k)]
    exact hx.2.2.1 (e v) k

def scheduleSign (X : V → V → Fin 2 → ℕ) (u v : V) : ℝ := (X u v 0:ℝ)-(X u v 1:ℝ)

lemma scheduleSign_unit (R : V → V → ℕ) (X : V → V → Fin 2 → ℕ) (hX : TwoSchedule R X)
    (u v : V) (hR : R u v = 1) : scheduleSign X u v = 1 ∨ scheduleSign X u v = -1 := by
  have hs := hX.1 u v
  rw [Fin.sum_univ_two,hR] at hs
  have hcases : (X u v 0 = 1 ∧ X u v 1 = 0) ∨ (X u v 0 = 0 ∧ X u v 1 = 1) := by omega
  rcases hcases with h|h
  · left; simp only [scheduleSign,h.1,h.2,Nat.cast_one,Nat.cast_zero,sub_zero]
  · right; simp only [scheduleSign,h.1,h.2,Nat.cast_one,Nat.cast_zero,zero_sub]

lemma scheduleSign_row_balance (R : V → V → ℕ) (X : V → V → Fin 2 → ℕ) (hX : TwoSchedule R X)
    (u : V) (hR : (∑ v, R u v) = 2) : (∑ v, scheduleSign X u v) = 0 := by
  have hs : (∑ v, X u v 0)+(∑ v, X u v 1) = 2 := by
    rw [←sum_add_distrib]
    calc
      _ = ∑ v, R u v := sum_congr rfl (fun v _ => by simpa only [Fin.sum_univ_two] using hX.1 u v)
      _ = 2 := hR
  have h0 := hX.2.1 u (0:Fin 2)
  have h1 := hX.2.1 u (1:Fin 2)
  have he0 : (∑ v, X u v 0) = 1 := by omega
  have he1 : (∑ v, X u v 1) = 1 := by omega
  simp only [scheduleSign,sum_sub_distrib,←Nat.cast_sum,he0,he1,sub_self]

lemma scheduleSign_col_balance (R : V → V → ℕ) (X : V → V → Fin 2 → ℕ) (hX : TwoSchedule R X)
    (v : V) (hR : (∑ u, R u v) = 2) : (∑ u, scheduleSign X u v) = 0 := by
  have hs : (∑ u, X u v 0)+(∑ u, X u v 1) = 2 := by
    rw [←sum_add_distrib]
    calc
      _ = ∑ u, R u v := sum_congr rfl (fun u _ => by simpa only [Fin.sum_univ_two] using hX.1 u v)
      _ = 2 := hR
  have h0 := hX.2.2 v (0:Fin 2)
  have h1 := hX.2.2 v (1:Fin 2)
  have he0 : (∑ u, X u v 0) = 1 := by omega
  have he1 : (∑ u, X u v 1) = 1 := by omega
  simp only [scheduleSign,sum_sub_distrib,←Nat.cast_sum,he0,he1,sub_self]

end MatchingRounding

-- Solutions/Sol_bipartite_signs.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingRounding
section Signs
variable {V : Type} [Fintype V] (H : SimpleGraph V) (side : V → Bool)

def bipartiteMatrix (u v : V) : ℕ := if H.Adj u v ∧ side u = false ∧ side v = true then 1 else 0

lemma adjacency_sum (v : V) : (∑ w, if H.Adj v w then (1:ℕ) else 0) = H.degree v := by
  rw [Finset.sum_boole]
  have he : univ.filter (H.Adj v) = H.neighborFinset v := by ext w; simp
  rw [he,H.card_neighborFinset_eq_degree]
  simp only [Nat.cast_id]

variable (hSide : ∀ u v, H.Adj u v → side u ≠ side v)
include hSide

lemma bipartiteMatrix_row (u : V) (hu : side u = false) :
    (∑ v, bipartiteMatrix H side u v) = H.degree u := by
  have he (v : V) : bipartiteMatrix H side u v = if H.Adj u v then 1 else 0 := by
    by_cases hadj : H.Adj u v
    · have hv : side v = true := by have h := hSide u v hadj; cases hs : side v <;> simp_all
      simp only [bipartiteMatrix,hadj,hu,hv,and_self,ite_true]
    · simp only [bipartiteMatrix,hadj,false_and,ite_false]
  simp only [he]
  exact adjacency_sum H u

lemma bipartiteMatrix_col (v : V) (hv : side v = true) :
    (∑ u, bipartiteMatrix H side u v) = H.degree v := by
  have he (u : V) : bipartiteMatrix H side u v = if H.Adj v u then 1 else 0 := by
    by_cases hadj : H.Adj v u
    · have hu : side u = false := by have h := hSide v u hadj; cases hs : side u <;> simp_all
      simp only [bipartiteMatrix,hadj,hadj.symm,hu,hv,and_self,ite_true]
    · have hn : ¬H.Adj u v := fun h => hadj h.symm
      simp only [bipartiteMatrix,hadj,hn,false_and,ite_false]
  simp only [he]
  exact adjacency_sum H v

lemma graph_two_schedule (hD : ∀ v, H.degree v ≤ 2) :
    ∃ X : V → V → Fin 2 → ℕ, TwoSchedule (bipartiteMatrix H side) X := by
  apply two_schedule_exists
  · intro u
    cases hu : side u with
    | false => rw [bipartiteMatrix_row H side hSide u hu]; exact hD u
    | true => simp only [bipartiteMatrix,hu,Bool.true_eq_false,false_and,and_false,ite_false,sum_const_zero]; omega
  · intro v
    cases hv : side v with
    | false => simp only [bipartiteMatrix,hv,Bool.false_eq_true,and_false,ite_false,sum_const_zero]; omega
    | true => rw [bipartiteMatrix_col H side hSide v hv]; exact hD v

end Signs

section EdgeSigns
variable {V : Type} [Fintype V]

def signedEdge (side : V → Bool) (X : V → V → Fin 2 → ℕ) : Sym2 V → ℝ :=
  Sym2.lift ⟨(fun u v => if side u = side v then 0 else
    if side u = false then scheduleSign X u v else scheduleSign X v u),by
      intro u v
      cases hu : side u <;> cases hv : side v <;> simp only [hu,hv,ite_true,ite_false,Bool.false_eq_true,Bool.true_eq_false]⟩

lemma signedEdge_apply (side : V → Bool) (X : V → V → Fin 2 → ℕ) (u v : V) :
    signedEdge side X s(u,v) = if side u = side v then 0 else
      if side u = false then scheduleSign X u v else scheduleSign X v u := rfl

lemma scheduleSign_zero (R : V → V → ℕ) (X : V → V → Fin 2 → ℕ) (hX : TwoSchedule R X)
    (u v : V) (hR : R u v = 0) : scheduleSign X u v = 0 := by
  have hs := hX.1 u v
  rw [Fin.sum_univ_two,hR] at hs
  have h0 : X u v 0 = 0 := by omega
  have h1 : X u v 1 = 0 := by omega
  simp only [scheduleSign,h0,h1,Nat.cast_zero,sub_zero]

lemma sum_neighbors_eq_all (H : SimpleGraph V) (v : V) (f g : V → ℝ)
    (hin : ∀ w, H.Adj v w → f w = g w) (hout : ∀ w, ¬H.Adj v w → g w = 0) :
    (∑ w ∈ H.neighborFinset v, f w) = ∑ w, g w := by
  have hn : H.neighborFinset v = univ.filter (H.Adj v) := by ext w; simp
  rw [hn,sum_filter]
  apply sum_congr rfl
  intro w hw
  by_cases hadj : H.Adj v w
  · rw [if_pos hadj,hin w hadj]
  · rw [if_neg hadj,hout w hadj]

variable (H : SimpleGraph V) (side : V → Bool)
    (hSide : ∀ u v, H.Adj u v → side u ≠ side v)
    (X : V → V → Fin 2 → ℕ) (hX : TwoSchedule (bipartiteMatrix H side) X)
include hSide hX

lemma signedEdge_unit (u v : V) (hAdj : H.Adj u v) :
    signedEdge side X s(u,v) = 1 ∨ signedEdge side X s(u,v) = -1 := by
  cases hu : side u with
  | false =>
    have hv : side v = true := by have h := hSide u v hAdj; cases hs : side v <;> simp_all
    simp only [signedEdge_apply,hu,hv,Bool.false_eq_true,ite_false,ite_true]
    exact scheduleSign_unit _ X hX u v (by simp only [bipartiteMatrix,hAdj,hu,hv,and_self,ite_true])
  | true =>
    have hv : side v = false := by have h := hSide u v hAdj; cases hs : side v <;> simp_all
    simp only [signedEdge_apply,hu,hv,Bool.true_eq_false,ite_false]
    exact scheduleSign_unit _ X hX v u (by simp only [bipartiteMatrix,hAdj.symm,hv,hu,and_self,ite_true])

lemma signedEdge_balanced (v : V) (hDegree : H.degree v = 2) :
    (∑ w ∈ H.neighborFinset v, signedEdge side X s(v,w)) = 0 := by
  cases hv : side v with
  | false =>
    have he : (∑ w ∈ H.neighborFinset v, signedEdge side X s(v,w)) = ∑ w, scheduleSign X v w := by
      apply sum_neighbors_eq_all
      · intro w hadj
        have hw : side w = true := by have h := hSide v w hadj; cases hs : side w <;> simp_all
        simp only [signedEdge_apply,hv,hw,Bool.false_eq_true,ite_false,ite_true]
      · intro w hadj
        apply scheduleSign_zero _ X hX
        simp only [bipartiteMatrix,hadj,false_and,ite_false]
    rw [he]
    exact scheduleSign_row_balance _ X hX v ((bipartiteMatrix_row H side hSide v hv).trans hDegree)
  | true =>
    have he : (∑ w ∈ H.neighborFinset v, signedEdge side X s(v,w)) = ∑ w, scheduleSign X w v := by
      apply sum_neighbors_eq_all
      · intro w hadj
        have hw : side w = false := by have h := hSide v w hadj; cases hs : side w <;> simp_all
        simp only [signedEdge_apply,hv,hw,Bool.true_eq_false,ite_false]
      · intro w hadj
        apply scheduleSign_zero _ X hX
        have hn : ¬H.Adj w v := fun h => hadj h.symm
        simp only [bipartiteMatrix,hn,false_and,ite_false]
    rw [he]
    exact scheduleSign_col_balance _ X hX v ((bipartiteMatrix_col H side hSide v hv).trans hDegree)

end EdgeSigns

lemma bipartite_edge_signs {V : Type} [Fintype V] (H : SimpleGraph V)
    (side : V → Bool) (hSide : ∀ u v, H.Adj u v → side u ≠ side v) (hD : ∀ v, H.degree v ≤ 2) :
    ∃ z : Sym2 V → ℝ,
      (∀ u v, H.Adj u v → z s(u,v) = 1 ∨ z s(u,v) = -1) ∧
      (∀ v, H.degree v = 2 → (∑ w ∈ H.neighborFinset v, z s(v,w)) = 0) := by
  obtain ⟨X,hX⟩ := graph_two_schedule H side hSide hD
  exact ⟨signedEdge side X,signedEdge_unit H side hSide X hX,signedEdge_balanced H side hSide X hX⟩

end MatchingRounding

-- Solutions/Sol_restrict_edges.lean

open Classical Finset
noncomputable section
namespace MatchingRounding
section Restrict
variable {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (S : Finset (Sym2 V))

def restrictEdges : SimpleGraph V where
  Adj a b := H.Adj a b ∧ s(a,b) ∈ S
  symm := ⟨by rintro a b ⟨h,he⟩; exact ⟨h.symm,by simpa only [Sym2.eq_swap] using he⟩⟩
  loopless := ⟨by intro a h; exact h.1.ne rfl⟩

lemma restrictEdges_le : restrictEdges H S ≤ H := fun _ _ h => h.1

lemma restrictEdges_edgeFinset (hS : S ⊆ H.edgeFinset) : (restrictEdges H S).edgeFinset = S := by
  ext e
  obtain ⟨⟨u,v⟩,rfl⟩ := e.exists_rep
  change s(u,v) ∈ (restrictEdges H S).edgeFinset ↔ s(u,v) ∈ S
  rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
  change (H.Adj u v ∧ s(u,v) ∈ S) ↔ s(u,v) ∈ S
  exact ⟨And.right,fun h => ⟨H.mem_edgeSet.mp (H.mem_edgeFinset.mp (hS h)),h⟩⟩

lemma restrictEdges_incidence (hS : S ⊆ H.edgeFinset) (v : V) :
    (restrictEdges H S).incidenceFinset v = S.filter (fun e => v ∈ e) := by
  rw [SimpleGraph.incidenceFinset_eq_filter,restrictEdges_edgeFinset H S hS]

lemma sum_incidence_neighbors (f : Sym2 V → ℝ) (v : V) :
    (∑ e ∈ H.incidenceFinset v, f e) = ∑ w ∈ H.neighborFinset v, f s(v,w) := by
  symm
  apply sum_bij (fun w _ => s(v,w))
  · intro w hw
    simpa using hw
  · intro a ha b hb hab
    exact Sym2.congr_right.mp hab
  · intro e he
    have hh := (H.mem_incidenceFinset v e).mp he
    obtain ⟨w,rfl⟩ := Sym2.mem_iff_exists.mp hh.2
    exact ⟨w,by simpa using hh.1,rfl⟩
  · intro w hw
    rfl

lemma restrictEdges_signs (side : V → Bool) (hSide : ∀ u v, H.Adj u v → side u ≠ side v)
    (hD : ∀ v, H.degree v ≤ 2) (hS : S ⊆ H.edgeFinset) :
    ∃ z : Sym2 V → ℝ,
      (∀ e ∈ S, z e = 1 ∨ z e = -1) ∧
      ∀ v, (S.filter (fun e => v ∈ e)).card = 2 → (∑ e ∈ S.filter (fun e => v ∈ e), z e) = 0 := by
  let J := restrictEdges H S
  have hJSide : ∀ u v, J.Adj u v → side u ≠ side v := fun u v h => hSide u v h.1
  have hJD : ∀ v, J.degree v ≤ 2 := fun v => (J.degree_le_of_le (restrictEdges_le H S)).trans (hD v)
  obtain ⟨z,hz,hbal⟩ := bipartite_edge_signs J side hJSide hJD
  refine ⟨z,?_,?_⟩
  · intro e he
    obtain ⟨⟨u,v⟩,rfl⟩ := e.exists_rep
    have heJ : s(u,v) ∈ J.edgeFinset := by rwa [restrictEdges_edgeFinset H S hS]
    exact hz u v (J.mem_edgeSet.mp (J.mem_edgeFinset.mp heJ))
  · intro v hv
    have hd : J.degree v = 2 := by
      rw [←J.card_incidenceFinset_eq_degree,restrictEdges_incidence H S hS v]
      exact hv
    rw [←restrictEdges_incidence H S hS v,sum_incidence_neighbors]
    exact hbal v hd

end Restrict
end MatchingRounding

-- Solutions/Sol_named_edge_data.lean

open Classical Finset
noncomputable section
namespace MatchingRounding
section Data
variable {V : Type} [Fintype V] [DecidableEq V]
    (S : Finset (Sym2 V)) (edgeName : Sym2 V → ℕ) (vertexName : V → ℕ)
    (coefficient : Sym2 V → ℝ)

def edgeRecord (e : Sym2 V) : NamedEdge := ⟨edgeName e,Sym2.map vertexName e,coefficient e⟩

def namedData : Finset NamedEdge := S.image (edgeRecord edgeName vertexName coefficient)

lemma edgeRecord_injective (hi : Set.InjOn edgeName S) :
    Set.InjOn (edgeRecord edgeName vertexName coefficient) S := by
  intro e he f hf h
  exact hi he hf (congrArg NamedEdge.name h)

lemma name_mem_data (e : Sym2 V) (he : e ∈ S) :
    edgeName e ∈ NamedEdgeData.names (namedData S edgeName vertexName coefficient) := by
  exact mem_image.mpr ⟨edgeRecord edgeName vertexName coefficient e,mem_image.mpr ⟨e,he,rfl⟩,rfl⟩

lemma mapped_vertex_mem (hv : Function.Injective vertexName) (a : V) (e : Sym2 V) :
    vertexName a ∈ Sym2.map vertexName e ↔ a ∈ e := by
  rw [Sym2.mem_map]
  constructor
  · rintro ⟨b,hb,he⟩
    exact hv he ▸ hb
  · intro h
    exact ⟨a,h,rfl⟩

lemma data_incident (hv : Function.Injective vertexName) (a : V) :
    NamedEdgeData.incident (namedData S edgeName vertexName coefficient) (vertexName a) =
      (S.filter (fun e => a ∈ e)).image edgeName := by
  ext i
  constructor
  · intro hi
    obtain ⟨r,hr,he⟩ := mem_image.mp hi
    obtain ⟨hrD,hvertex⟩ := mem_filter.mp hr
    obtain ⟨e,heS,rfl⟩ := mem_image.mp hrD
    have ha : a ∈ e := (mapped_vertex_mem vertexName hv a e).mp hvertex
    exact mem_image.mpr ⟨e,mem_filter.mpr ⟨heS,ha⟩,he⟩
  · intro hi
    obtain ⟨e,he,heName⟩ := mem_image.mp hi
    exact mem_image.mpr ⟨edgeRecord edgeName vertexName coefficient e,
      mem_filter.mpr ⟨mem_image.mpr ⟨e,(mem_filter.mp he).1,rfl⟩,
        (mapped_vertex_mem vertexName hv a e).mpr (mem_filter.mp he).2⟩,heName⟩

def witnessBits (z : Sym2 V → ℝ) (i : ℕ) : Bool :=
  if h : ∃ e ∈ S, edgeName e = i then decide (z h.choose = 1) else false

lemma witnessBits_value (hi : Set.InjOn edgeName S) (z : Sym2 V → ℝ)
    (hz : ∀ e ∈ S, z e = 1 ∨ z e = -1) (e : Sym2 V) (he : e ∈ S) :
    NamedEdgeData.bitSign (witnessBits S edgeName z) (edgeName e) = z e := by
  let h : ∃ f ∈ S, edgeName f = edgeName e := ⟨e,he,rfl⟩
  have hb : witnessBits S edgeName z (edgeName e) = decide (z e = 1) := by
    unfold witnessBits
    rw [dif_pos h]
    have heq : h.choose = e := hi h.choose_spec.1 he h.choose_spec.2
    rw [heq]
  unfold NamedEdgeData.bitSign
  simp only [hb]
  rcases hz e he with hz|hz <;> norm_num [hz]

lemma data_admissible_of_signs (hi : Set.InjOn edgeName S) (hv : Function.Injective vertexName)
    (z : Sym2 V → ℝ) (hz : ∀ e ∈ S, z e = 1 ∨ z e = -1)
    (hbalance : ∀ a, (S.filter (fun e => a ∈ e)).card = 2 → (∑ e ∈ S.filter (fun e => a ∈ e), z e) = 0) :
    ∃ theta, NamedEdgeData.Admissible (namedData S edgeName vertexName coefficient) theta := by
  refine ⟨witnessBits S edgeName z,?_⟩
  intro i hiVertex hdegree
  obtain ⟨r,hr,hir⟩ := mem_biUnion.mp hiVertex
  obtain ⟨e,he,rfl⟩ := mem_image.mp hr
  have hm : i ∈ Sym2.map vertexName e := Sym2.mem_toFinset.mp hir
  obtain ⟨a,ha,hID⟩ := Sym2.mem_map.mp hm
  rw [←hID,data_incident S edgeName vertexName coefficient hv a] at hdegree ⊢
  have hname : Set.InjOn edgeName (S.filter (fun e => a ∈ e)) :=
    fun e he f hf heq => hi (mem_filter.mp he).1 (mem_filter.mp hf).1 heq
  have hcard : ((S.filter (fun e => a ∈ e)).image edgeName).card = (S.filter (fun e => a ∈ e)).card :=
    card_image_iff.mpr hname
  rw [hcard] at hdegree
  rw [sum_image hname]
  rw [sum_congr rfl (fun e he => witnessBits_value S edgeName hi z hz e (mem_filter.mp he).1)]
  exact hbalance a hdegree

lemma named_signs_score (hi : Set.InjOn edgeName S) :
    0 ≤ ∑ e ∈ S, coefficient e*NamedEdgeData.sign (namedData S edgeName vertexName coefficient) (edgeName e) := by
  have hh := NamedEdgeData.score_nonnegative (namedData S edgeName vertexName coefficient)
  change 0 ≤ ∑ r ∈ S.image (edgeRecord edgeName vertexName coefficient), r.coefficient*
    NamedEdgeData.sign (namedData S edgeName vertexName coefficient) r.name at hh
  rw [sum_image (edgeRecord_injective S edgeName vertexName coefficient hi)] at hh
  exact hh

lemma named_signs_balanced (hi : Set.InjOn edgeName S) (hv : Function.Injective vertexName)
    (hgood : ∃ theta, NamedEdgeData.Admissible (namedData S edgeName vertexName coefficient) theta)
    (a : V) (hdegree : (S.filter (fun e => a ∈ e)).card = 2) :
    (∑ e ∈ S.filter (fun e => a ∈ e),
      NamedEdgeData.sign (namedData S edgeName vertexName coefficient) (edgeName e)) = 0 := by
  have hex : (S.filter (fun e => a ∈ e)).Nonempty := card_pos.mp (by omega)
  obtain ⟨e,he⟩ := hex
  have hvertex : vertexName a ∈ NamedEdgeData.vertices (namedData S edgeName vertexName coefficient) := by
    apply mem_biUnion.mpr
    refine ⟨edgeRecord edgeName vertexName coefficient e,mem_image.mpr ⟨e,(mem_filter.mp he).1,rfl⟩,?_⟩
    apply Sym2.mem_toFinset.mpr
    exact (mapped_vertex_mem vertexName hv a e).mpr (mem_filter.mp he).2
  have hname : Set.InjOn edgeName (S.filter (fun e => a ∈ e)) :=
    fun e he f hf heq => hi (mem_filter.mp he).1 (mem_filter.mp hf).1 heq
  have hcard : (NamedEdgeData.incident (namedData S edgeName vertexName coefficient) (vertexName a)).card = 2 := by
    rw [data_incident S edgeName vertexName coefficient hv a,card_image_iff.mpr hname,hdegree]
  have hb := NamedEdgeData.sign_balanced _ hgood (vertexName a) hvertex hcard
  rw [data_incident S edgeName vertexName coefficient hv a,sum_image hname] at hb
  exact hb

end Data

lemma named_data_feasible {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (side : V → Bool) (hSide : ∀ u v, H.Adj u v → side u ≠ side v)
    (hD : ∀ v, H.degree v ≤ 2) (S : Finset (Sym2 V)) (hS : S ⊆ H.edgeFinset)
    (edgeName : Sym2 V → ℕ) (hi : Set.InjOn edgeName S)
    (vertexName : V → ℕ) (hv : Function.Injective vertexName) (coefficient : Sym2 V → ℝ) :
    ∃ theta, NamedEdgeData.Admissible (namedData S edgeName vertexName coefficient) theta := by
  obtain ⟨z,hz,hbalance⟩ := restrictEdges_signs H S side hSide hD hS
  exact data_admissible_of_signs S edgeName vertexName coefficient hi hv z hz hbalance

end MatchingRounding

-- Solutions/Sol_component_signs.lean

open Classical Finset
noncomputable section
namespace MatchingRounding
section Signs
variable {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (C : Finset V)
    (edgeName : Sym2 V → ℕ) (vertexName : V → ℕ) (coefficient : Sym2 V → ℝ)

def componentData (e : H.edgeSet) : Finset NamedEdge :=
  namedData (componentEdges H C e) edgeName vertexName coefficient

def componentSign (e : Sym2 V) : ℝ :=
  if he : e ∈ H.edgeSet then NamedEdgeData.sign (componentData H C edgeName vertexName coefficient ⟨e,he⟩) (edgeName e) else 0

lemma componentSign_on (e : H.edgeSet) : componentSign H C edgeName vertexName coefficient e.val =
    NamedEdgeData.sign (componentData H C edgeName vertexName coefficient e) (edgeName e.val) := by
  unfold componentSign
  rw [dif_pos e.property]

lemma componentData_eq (e f : H.edgeSet) (h : (edgeChain H C).Reachable e f) :
    componentData H C edgeName vertexName coefficient e = componentData H C edgeName vertexName coefficient f := by
  unfold componentData
  rw [componentEdges_eq H C e f h]

lemma componentSign_on_component (e : H.edgeSet) (f : Sym2 V) (hf : f ∈ componentEdges H C e) :
    componentSign H C edgeName vertexName coefficient f =
      NamedEdgeData.sign (componentData H C edgeName vertexName coefficient e) (edgeName f) := by
  have hfH := H.mem_edgeFinset.mp (componentEdges_subset H C e hf)
  rw [componentSign_on H C edgeName vertexName coefficient ⟨f,hfH⟩,
    ←componentData_eq H C edgeName vertexName coefficient e ⟨f,hfH⟩ ((mem_componentEdges H C e _).mp hf)]

lemma componentSign_unit (f : Sym2 V) (hf : f ∈ H.edgeFinset) :
    componentSign H C edgeName vertexName coefficient f = 1 ∨ componentSign H C edgeName vertexName coefficient f = -1 := by
  let e : H.edgeSet := ⟨f,H.mem_edgeFinset.mp hf⟩
  rw [componentSign_on H C edgeName vertexName coefficient e]
  exact NamedEdgeData.sign_unit _ _ (name_mem_data _ edgeName vertexName coefficient e.val (componentEdges_self H C e))

lemma componentSign_linear (hi : Set.InjOn edgeName H.edgeFinset) :
    0 ≤ ∑ f ∈ H.edgeFinset, coefficient f*componentSign H C edgeName vertexName coefficient f := by
  rw [←sum_edge_subtype H]
  apply sum_components_nonnegative (edgeChain H C)
  intro e
  have hiS : Set.InjOn edgeName (componentEdges H C e) :=
    fun f hf g hg h => hi (componentEdges_subset H C e hf) (componentEdges_subset H C e hg) h
  have hscore := named_signs_score (componentEdges H C e) edgeName vertexName coefficient hiS
  unfold componentEdges at hscore
  rw [sum_image (fun _ _ _ _ h => Subtype.val_injective h)] at hscore
  apply hscore.trans_eq
  apply sum_congr rfl
  intro f hf
  rw [componentSign_on_component H C edgeName vertexName coefficient e f.val
    (mem_image.mpr ⟨f,hf,rfl⟩)]
  rfl

lemma componentSign_balanced (side : V → Bool) (hSide : ∀ u v, H.Adj u v → side u ≠ side v)
    (hD : ∀ v, H.degree v ≤ 2) (hi : Set.InjOn edgeName H.edgeFinset)
    (hv : Function.Injective vertexName) (a : V) (hac : a ∉ C) (hd : H.degree a = 2) :
    (∑ b ∈ H.neighborFinset a, componentSign H C edgeName vertexName coefficient s(a,b)) = 0 := by
  have hex : (H.incidenceFinset a).Nonempty := card_pos.mp (by rw [H.card_incidenceFinset_eq_degree,hd]; omega)
  obtain ⟨f,hf⟩ := hex
  have hh := (H.mem_incidenceFinset a f).mp hf
  let e : H.edgeSet := ⟨f,hh.1⟩
  let S := componentEdges H C e
  have hiS : Set.InjOn edgeName S :=
    fun f hf g hg h => hi (componentEdges_subset H C e hf) (componentEdges_subset H C e hg) h
  have hfeas := named_data_feasible H side hSide hD S (componentEdges_subset H C e)
    edgeName hiS vertexName hv coefficient
  have hinc : S.filter (fun f => a ∈ f) = H.incidenceFinset a := incident_component H C e a hh.2 hac
  have hcard : (S.filter (fun f => a ∈ f)).card = 2 := by rw [hinc,H.card_incidenceFinset_eq_degree,hd]
  have hb := named_signs_balanced S edgeName vertexName coefficient hiS hv hfeas a hcard
  rw [hinc] at hb
  rw [←sum_incidence_neighbors H]
  calc
    _ = ∑ f ∈ H.incidenceFinset a, NamedEdgeData.sign (namedData S edgeName vertexName coefficient) (edgeName f) := by
      apply sum_congr rfl
      intro f hf
      apply componentSign_on_component H C edgeName vertexName coefficient e f
      exact (mem_filter.mp (hinc ▸ hf)).1
    _ = 0 := hb

end Signs
end MatchingRounding

-- Solutions/Sol_pairing_edges.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingRounding
section Pairing
variable {N : ℕ} (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (p : Pairing N) (hp : ValidPairing G x q p)
include hp

lemma copy_unique (a b : Copy p) (hcreator : a.1 = b.1) (v : Fin N)
    (ha : v ∈ group p a) (hb : v ∈ group p b) : a = b := by
  cases a with
  | mk u i =>
    cases b with
    | mk w j =>
      change u = w at hcreator
      subst w
      have hactive := hp.2.2.1 ⟨u,i⟩ v ha
      have huniq := (hp.2.1 u v).mp hactive
      have hij : i = j := huniq.unique ha hb
      subst j
      rfl

lemma neighbor_creators (a : Copy p) :
    ((virtualGraph p).neighborFinset a).image Sigma.fst = group p a := by
  ext v
  constructor
  · intro hv
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hv
    exact ((SimpleGraph.mem_neighborFinset (virtualGraph p) a b).mp hb).2.1
  · intro hv
    have hact := hp.2.2.1 a v hv
    have hmirror : G.Adj v a.1 ∧ x s(v,a.1) = q :=
      ⟨hact.1.symm,by simpa only [Sym2.eq_swap] using hact.2⟩
    obtain ⟨j,hj,huniq⟩ := (hp.2.1 v a.1).mp hmirror
    refine mem_image.mpr ⟨⟨v,j⟩,?_,rfl⟩
    apply (SimpleGraph.mem_neighborFinset (virtualGraph p) a ⟨v,j⟩).mpr
    exact ⟨hact.1.ne,hv,hj⟩

lemma neighbor_creator_injective (a : Copy p) :
    Set.InjOn (fun b : Copy p => b.1) ((virtualGraph p).neighborFinset a) := by
  intro b hb c hc hbc
  have hab := (SimpleGraph.mem_neighborFinset (virtualGraph p) a b).mp hb
  have hac := (SimpleGraph.mem_neighborFinset (virtualGraph p) a c).mp hc
  exact copy_unique G x q p hp b c hbc a.1 hab.2.2 hac.2.2

lemma virtual_degree_exact (a : Copy p) : (virtualGraph p).degree a = (group p a).card := by
  rw [←SimpleGraph.card_neighborFinset_eq_degree]
  have hi := card_image_iff.mpr (neighbor_creator_injective G x q p hp a)
  rw [neighbor_creators G x q p hp a] at hi
  exact hi.symm

end Pairing

variable {N : ℕ} (p : Pairing N)

def physicalEdge (e : Sym2 (Copy p)) : Sym2 (Fin N) := Sym2.map Sigma.fst e

lemma physicalEdge_apply (a b : Copy p) : physicalEdge p s(a,b) = s(a.1,b.1) := rfl

section EdgeBijection
variable (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ) (hp : ValidPairing G x q p)
include hp

lemma physicalEdge_active (e : Sym2 (Copy p)) (he : e ∈ (virtualGraph p).edgeFinset) :
    physicalEdge p e ∈ G.edgeFinset ∧ x (physicalEdge p e) = q := by
  obtain ⟨⟨a,b⟩,rfl⟩ := e.exists_rep
  have hadj := (virtualGraph p).mem_edgeSet.mp ((virtualGraph p).mem_edgeFinset.mp he)
  have ha := hp.2.2.1 a b.1 hadj.2.1
  rw [physicalEdge_apply]
  exact ⟨G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr ha.1),ha.2⟩

lemma physicalEdge_injective : Set.InjOn (physicalEdge p) ((virtualGraph p).edgeFinset) := by
  intro e he f hf heq
  obtain ⟨⟨a,b⟩,rfl⟩ := e.exists_rep
  obtain ⟨⟨c,d⟩,rfl⟩ := f.exists_rep
  have hab := (virtualGraph p).mem_edgeSet.mp ((virtualGraph p).mem_edgeFinset.mp he)
  have hcd := (virtualGraph p).mem_edgeSet.mp ((virtualGraph p).mem_edgeFinset.mp hf)
  rw [physicalEdge_apply,physicalEdge_apply] at heq
  rcases Sym2.eq_iff.mp heq with ⟨hac,hbd⟩|⟨had,hbc⟩
  · have hacopy := copy_unique G x q p hp a c hac b.1 hab.2.1 (by rw [hbd]; exact hcd.2.1)
    have hbdcopy := copy_unique G x q p hp b d hbd a.1 hab.2.2 (by rw [hac]; exact hcd.2.2)
    rw [hacopy,hbdcopy]
  · have hadcopy := copy_unique G x q p hp a d had b.1 hab.2.1 (by rw [hbc]; exact hcd.2.2)
    have hbccopy := copy_unique G x q p hp b c hbc a.1 hab.2.2 (by rw [had]; exact hcd.2.1)
    rw [hadcopy,hbccopy]
    change s(d,c) = s(c,d)
    exact Sym2.eq_swap

lemma physicalEdge_image : ((virtualGraph p).edgeFinset).image (physicalEdge p) =
    G.edgeFinset.filter (fun e => x e = q) := by
  ext e
  constructor
  · intro he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    exact mem_filter.mpr (physicalEdge_active p G x q hp f hf)
  · intro he
    obtain ⟨hG,hq⟩ := mem_filter.mp he
    obtain ⟨⟨u,v⟩,rfl⟩ := e.exists_rep
    have hAdj := G.mem_edgeSet.mp (G.mem_edgeFinset.mp hG)
    obtain ⟨i,hi,hui⟩ := (hp.2.1 u v).mp ⟨hAdj,hq⟩
    obtain ⟨j,hj,huj⟩ := (hp.2.1 v u).mp ⟨hAdj.symm,by simpa only [Sym2.eq_swap] using hq⟩
    let a : Copy p := ⟨u,i⟩
    let b : Copy p := ⟨v,j⟩
    have hvAdj : (virtualGraph p).Adj a b := ⟨hAdj.ne,hi,hj⟩
    refine mem_image.mpr ⟨s(a,b),(virtualGraph p).mem_edgeFinset.mpr
      ((virtualGraph p).mem_edgeSet.mpr hvAdj),rfl⟩

lemma sum_active_edges (f : Sym2 (Fin N) → ℝ) :
    (∑ e ∈ G.edgeFinset.filter (fun e => x e = q), f e) =
      ∑ e ∈ (virtualGraph p).edgeFinset, f (physicalEdge p e) := by
  rw [←physicalEdge_image p G x q hp]
  exact sum_image (physicalEdge_injective p G x q hp)

end EdgeBijection
end MatchingRounding

-- Solutions/Sol_potential_change.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingRounding
section Potential
variable {N : ℕ} (G : SimpleGraph (Fin N))

lemma load_as_edges (x : Sym2 (Fin N) → ℝ) (v : Fin N) :
    load G x v = ∑ e ∈ G.edgeFinset, if v ∈ e then x e else 0 := by
  unfold load RandomOrderCRS.fracDegree
  rw [G.incidenceFinset_eq_filter]
  exact sum_filter ..

lemma load_sub (x y : Sym2 (Fin N) → ℝ) (v : Fin N) :
    load G (fun e => y e-x e) v = load G y v-load G x v := by
  unfold load RandomOrderCRS.fracDegree
  simp only [Finset.sum_sub_distrib]

def endpointSum (f : Fin N → ℝ) : Sym2 (Fin N) → ℝ :=
  Sym2.lift ⟨fun u v => f u+f v,by intro u v; exact add_comm _ _⟩

lemma endpointSum_apply (f : Fin N → ℝ) (u v : Fin N) : endpointSum f s(u,v) = f u+f v := rfl

lemma weighted_loads (d : Sym2 (Fin N) → ℝ) (f : Fin N → ℝ) :
    (∑ v, f v*load G d v) = ∑ e ∈ G.edgeFinset, endpointSum f e*d e := by
  simp_rw [load_as_edges,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  obtain ⟨⟨u,w⟩,rfl⟩ := e.exists_rep
  have huw : u ≠ w := (G.mem_edgeSet.mp (G.mem_edgeFinset.mp he)).ne
  have hi (v : Fin N) : f v*(if v ∈ s(u,w) then d s(u,w) else 0) =
      (if v = u then f u*d s(u,w) else 0)+(if v = w then f w*d s(u,w) else 0) := by
    simp only [Sym2.mem_iff]
    by_cases h1 : v = u <;> by_cases h2 : v = w <;> simp_all
  simp_rw [hi,sum_add_distrib]
  simp only [sum_ite_eq',mem_univ,ite_true,endpointSum_apply]
  ring

def linearCoefficient (x : Sym2 (Fin N) → ℝ) (e : Sym2 (Fin N)) : ℝ :=
  1-4*endpointSum (load G x) e

lemma linearCoefficient_apply (x : Sym2 (Fin N) → ℝ) (u v : Fin N) :
    linearCoefficient G x s(u,v) = 1-4*load G x u-4*load G x v := by
  unfold linearCoefficient
  rw [endpointSum_apply]
  ring

lemma potential_change (x y : Sym2 (Fin N) → ℝ) :
    potential G y-potential G x =
      (∑ e ∈ G.edgeFinset, linearCoefficient G x e*(y e-x e))-
        2*(∑ v, (load G y v-load G x v)^2) := by
  have hpen : penalty G y-penalty G x =
      4*(∑ v, load G x v*(load G y v-load G x v))+
        2*(∑ v, (load G y v-load G x v)^2) := by
    unfold penalty
    simp only [mul_sum,←sum_sub_distrib,←sum_add_distrib]
    apply sum_congr rfl
    intro v hv
    ring
  have hcross := weighted_loads G (fun e => y e-x e) (load G x)
  simp_rw [load_sub] at hcross
  have hlinear : (∑ e ∈ G.edgeFinset, linearCoefficient G x e*(y e-x e)) =
      totalWeight G y-totalWeight G x-4*(∑ v, load G x v*(load G y v-load G x v)) := by
    rw [hcross]
    unfold linearCoefficient totalWeight
    simp only [sub_mul,one_mul,mul_assoc,sum_sub_distrib,←mul_sum]
  unfold potential
  linarith

end Potential
end MatchingRounding

-- Solutions/Sol_rounding_feasible.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingRounding
variable {N : ℕ} (G : SimpleGraph (Fin N))

lemma load_nonneg (x : Sym2 (Fin N) → ℝ) (hx : ∀ e, 0 ≤ x e) (v : Fin N) : 0 ≤ load G x v := by
  unfold load RandomOrderCRS.fracDegree
  exact sum_nonneg (fun e _ => hx e)

lemma load_add (x d : Sym2 (Fin N) → ℝ) (v : Fin N) :
    load G (fun e => x e+d e) v = load G x v+load G d v := by
  unfold load RandomOrderCRS.fracDegree
  simp only [sum_add_distrib]

lemma edge_le_load (x : Sym2 (Fin N) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (u v : Fin N) (hAdj : G.Adj u v) : x s(u,v) ≤ load G x u := by
  unfold load RandomOrderCRS.fracDegree
  apply single_le_sum (fun e _ => hx e)
  exact (G.mem_incidenceFinset u s(u,v)).mpr ⟨G.mem_edgeSet.mpr hAdj,by simp⟩

lemma double_load_bound (x y : Sym2 (Fin N) → ℝ) (hxy : ∀ e, y e ≤ 2*x e) (v : Fin N) :
    load G y v ≤ 2*load G x v := by
  unfold load RandomOrderCRS.fracDegree
  calc
    _ ≤ ∑ e ∈ G.incidenceFinset v, 2*x e := sum_le_sum (fun e _ => hxy e)
    _ = _ := (mul_sum ..).symm

lemma dominated_fractional (x y : Sym2 (Fin N) → ℝ) (hx : fractional G x)
    (hload : ∀ v, load G x v ≤ 1/2) (hy : ∀ e, 0 ≤ y e ∧ y e ≤ 2*x e) :
    fractional G y ∧ ∀ v, load G y v ≤ 1 := by
  have hx0 : ∀ e, 0 ≤ x e := fun e => (hx.1 e).1
  have hyload (v : Fin N) : load G y v ≤ 1 := by
    have hh := double_load_bound G x y (fun e => (hy e).2) v
    have ht := hload v
    linarith
  have hsupport (e : Sym2 (Fin N)) (he : e ∉ G.edgeSet) : y e = 0 := by
    have hxz := hx.2.1 e he
    have hh := hy e
    rw [hxz] at hh
    linarith
  have hyupper (e : Sym2 (Fin N)) : y e ≤ 1 := by
    by_cases he : e ∈ G.edgeSet
    · obtain ⟨⟨u,v⟩,rfl⟩ := e.exists_rep
      have hAdj := G.mem_edgeSet.mp he
      have hh := edge_le_load G x hx0 u v hAdj
      have ht := hload u
      have hb := (hy s(u,v)).2
      linarith
    · rw [hsupport e he]
      norm_num
  exact ⟨⟨fun e => ⟨(hy e).1,hyupper e⟩,hsupport,hyload⟩,hyload⟩

end MatchingRounding

-- Solutions/Sol_rounding_lift.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingRounding
variable {N : ℕ} (p : Pairing N)

def liftSigns (z : Sym2 (Copy p) → ℝ) (e : Sym2 (Fin N)) : ℝ :=
  ∑ f ∈ (virtualGraph p).edgeFinset, if physicalEdge p f = e then z f else 0

def increment (q : ℝ) (z : Sym2 (Copy p) → ℝ) (e : Sym2 (Fin N)) : ℝ := q*liftSigns p z e

def candidate (x : Sym2 (Fin N) → ℝ) (q : ℝ) (z : Sym2 (Copy p) → ℝ) (e : Sym2 (Fin N)) : ℝ :=
  x e+increment p q z e

section Lift
variable (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ) (hp : ValidPairing G x q p)
include hp

lemma liftSigns_on_edge (z : Sym2 (Copy p) → ℝ) (f : Sym2 (Copy p)) (hf : f ∈ (virtualGraph p).edgeFinset) :
    liftSigns p z (physicalEdge p f) = z f := by
  unfold liftSigns
  rw [sum_eq_single f]
  · rw [if_pos rfl]
  · intro g hg hgf
    rw [if_neg (fun he => hgf (physicalEdge_injective p G x q hp hg hf he))]
  · exact fun h => (h hf).elim

lemma liftSigns_off_active (z : Sym2 (Copy p) → ℝ) (e : Sym2 (Fin N))
    (he : ¬(e ∈ G.edgeFinset ∧ x e = q)) : liftSigns p z e = 0 := by
  unfold liftSigns
  apply sum_eq_zero
  intro f hf
  apply if_neg
  intro hfe
  have hact := physicalEdge_active p G x q hp f hf
  rw [hfe] at hact
  exact he hact

lemma increment_on_edge (z : Sym2 (Copy p) → ℝ) (f : Sym2 (Copy p)) (hf : f ∈ (virtualGraph p).edgeFinset) :
    increment p q z (physicalEdge p f) = q*z f := by
  unfold increment
  rw [liftSigns_on_edge p G x q hp z f hf]

lemma increment_off_active (z : Sym2 (Copy p) → ℝ) (e : Sym2 (Fin N))
    (he : ¬(e ∈ G.edgeFinset ∧ x e = q)) : increment p q z e = 0 := by
  unfold increment
  rw [liftSigns_off_active p G x q hp z e he,mul_zero]

lemma candidate_active_values (z : Sym2 (Copy p) → ℝ)
    (hz : ∀ f ∈ (virtualGraph p).edgeFinset, z f = 1 ∨ z f = -1)
    (e : Sym2 (Fin N)) (he : e ∈ G.edgeFinset) (hxe : x e = q) :
    candidate p x q z e = 0 ∨ candidate p x q z e = 2*q := by
  have hm : e ∈ ((virtualGraph p).edgeFinset).image (physicalEdge p) := by
    rw [physicalEdge_image p G x q hp]
    exact mem_filter.mpr ⟨he,hxe⟩
  obtain ⟨f,hf,rfl⟩ := mem_image.mp hm
  unfold candidate
  rw [hxe,increment_on_edge p G x q hp z f hf]
  rcases hz f hf with h|h
  · right; rw [h]; ring
  · left; rw [h]; ring

lemma candidate_dominated (hx : ∀ e, 0 ≤ x e) (hq : 0 < q) (z : Sym2 (Copy p) → ℝ)
    (hz : ∀ f ∈ (virtualGraph p).edgeFinset, z f = 1 ∨ z f = -1) :
    ∀ e, 0 ≤ candidate p x q z e ∧ candidate p x q z e ≤ 2*x e := by
  intro e
  by_cases he : e ∈ G.edgeFinset ∧ x e = q
  · have hc := candidate_active_values p G x q hp z hz e he.1 he.2
    rcases hc with hc|hc <;> rw [hc,he.2] <;> constructor <;> linarith
  · unfold candidate
    rw [increment_off_active p G x q hp z e he,add_zero]
    exact ⟨hx e,by linarith [hx e]⟩

lemma candidate_feasible (hx : fractional G x) (hload : ∀ v, load G x v ≤ 1/2)
    (hq : 0 < q) (z : Sym2 (Copy p) → ℝ)
    (hz : ∀ f ∈ (virtualGraph p).edgeFinset, z f = 1 ∨ z f = -1) :
    fractional G (candidate p x q z) ∧ ∀ v, load G (candidate p x q z) v ≤ 1 := by
  apply dominated_fractional G x (candidate p x q z) hx hload
  exact candidate_dominated p G x q hp (fun e => (hx.1 e).1) hq z hz

end Lift
end MatchingRounding

-- Solutions/Sol_pairing_partition.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingRounding
section Partition
variable {N : ℕ} (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (p : Pairing N) (hp : ValidPairing G x q p)

def activeNeighbors (v : Fin N) : Finset (Fin N) := (G.neighborFinset v).filter (fun w => x s(v,w) = q)

include hp

lemma group_membership_sum {β : Type} [AddCommMonoid β] (v w : Fin N) (f : Fin N → β) :
    (∑ i : Fin (p v).length, if w ∈ (p v).get i then f w else 0) =
      if G.Adj v w ∧ x s(v,w) = q then f w else 0 := by
  by_cases hact : G.Adj v w ∧ x s(v,w) = q
  · obtain ⟨j,hj,huniq⟩ := (hp.2.1 v w).mp hact
    rw [if_pos hact,sum_eq_single j]
    · rw [if_pos hj]
    · intro i hi hne
      exact if_neg (fun h => hne (huniq i h))
    · exact fun h => (h (mem_univ _)).elim
  · rw [if_neg hact]
    apply sum_eq_zero
    intro i hi
    apply if_neg
    intro h
    exact hact (hp.2.2.1 ⟨v,i⟩ w h)

lemma sum_groups_eq_active {β : Type} [AddCommMonoid β] (v : Fin N) (f : Fin N → β) :
    (∑ i : Fin (p v).length, ∑ w ∈ (p v).get i, f w) =
      ∑ w ∈ activeNeighbors G x q v, f w := by
  have hi (i : Fin (p v).length) : (∑ w ∈ (p v).get i, f w) =
      ∑ w, if w ∈ (p v).get i then f w else 0 := by
    rw [←sum_filter]
    congr 1
    ext w
    simp
  rw [sum_congr rfl (fun i _ => hi i),sum_comm]
  simp_rw [group_membership_sum G x q p hp v]
  have hs : univ.filter (fun w => G.Adj v w ∧ x s(v,w) = q) = activeNeighbors G x q v := by
    ext w
    simp only [activeNeighbors,mem_filter,mem_univ,true_and,SimpleGraph.mem_neighborFinset]
  rw [←sum_filter,hs]

lemma activeDegree_sum_groups (v : Fin N) :
    activeDegree G x q v = ∑ i : Fin (p v).length, ((p v).get i).card := by
  have hh := sum_groups_eq_active G x q p hp v (fun _ => (1:ℕ))
  simpa only [activeNeighbors,activeDegree,sum_const,nsmul_eq_mul,Nat.cast_id,mul_one] using hh.symm

lemma singleton_parity (v : Fin N) :
    (univ.filter (fun i : Fin (p v).length => ((p v).get i).card = 1)).card = activeDegree G x q v%2 := by
  let S := univ.filter (fun i : Fin (p v).length => ((p v).get i).card = 1)
  have hS : S.card ≤ 1 := hp.2.2.2 v
  have hSC : S.card = ∑ i : Fin (p v).length, if ((p v).get i).card = 1 then (1:ℕ) else 0 := by
    rw [card_eq_sum_ones]
    simp only [S,sum_filter]
  have he : activeDegree G x q v+S.card = 2*(p v).length := by
    rw [activeDegree_sum_groups G x q p hp v]
    rw [hSC]
    rw [←sum_add_distrib]
    calc
      _ = ∑ _ : Fin (p v).length, (2:ℕ) := by
        apply sum_congr rfl
        intro i hi
        have hg := hp.1 ⟨v,i⟩
        rcases hg with hg|hg
        · simp only [show ((p v).get i).card = 1 from hg,ite_true]
        · simp only [show ((p v).get i).card = 2 from hg,show ¬(2:ℕ) = 1 by omega,ite_false]
      _ = _ := by simp [mul_comm]
  change S.card = _
  omega

end Partition

lemma selected_local_count {N : ℕ} (p : Pairing N) (B : BlockAssignment p) (s : Copy p → Copy p)
    (hs : ValidCuts B s) (v : Fin N) :
    (univ.filter (fun i : Fin (p v).length => (⟨v,i⟩:Copy p) ∈ selectedSet B s)).card = cutCount B s v := by
  rw [←selected_creator_count B s hs v]
  apply card_bij (fun i _ => (⟨v,i⟩:Copy p))
  · intro i hi
    exact mem_filter.mpr ⟨(mem_filter.mp hi).2,rfl⟩
  · intro i hi j hj he
    apply Fin.ext
    exact congrArg (fun c : Copy p => c.2.val) he
  · intro c hc
    obtain ⟨hsel,hcv⟩ := mem_filter.mp hc
    cases c with
    | mk u i =>
      change u = v at hcv
      subst u
      exact ⟨i,mem_filter.mpr ⟨mem_univ _,hsel⟩,rfl⟩

end MatchingRounding

-- Solutions/Sol_rounding_loads.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingRounding
variable {N : ℕ} (p : Pairing N)

def copyChange (q : ℝ) (z : Sym2 (Copy p) → ℝ) (a : Copy p) : ℝ :=
  q*∑ b ∈ (virtualGraph p).neighborFinset a, z s(a,b)

section Loads
variable (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ) (hp : ValidPairing G x q p)
include hp

lemma group_virtual_sum {β : Type} [AddCommMonoid β] (a : Copy p) (f : Fin N → β) :
    (∑ w ∈ group p a, f w) = ∑ b ∈ (virtualGraph p).neighborFinset a, f b.1 := by
  rw [←neighbor_creators G x q p hp a]
  exact sum_image (neighbor_creator_injective G x q p hp a)

lemma group_increment (z : Sym2 (Copy p) → ℝ) (a : Copy p) :
    (∑ w ∈ group p a, increment p q z s(a.1,w)) = copyChange p q z a := by
  rw [group_virtual_sum p G x q hp a]
  unfold copyChange
  rw [mul_sum]
  apply sum_congr rfl
  intro b hb
  have hf : s(a,b) ∈ (virtualGraph p).edgeFinset := by
    exact (virtualGraph p).mem_edgeFinset.mpr ((virtualGraph p).mem_edgeSet.mpr
      ((SimpleGraph.mem_neighborFinset (virtualGraph p) a b).mp hb))
  change increment p q z (physicalEdge p s(a,b)) = _
  exact increment_on_edge p G x q hp z s(a,b) hf

lemma load_increment_copies (z : Sym2 (Copy p) → ℝ) (v : Fin N) :
    load G (increment p q z) v = ∑ i : Fin (p v).length, copyChange p q z ⟨v,i⟩ := by
  have hload : load G (increment p q z) v = ∑ w ∈ G.neighborFinset v, increment p q z s(v,w) := by
    unfold load RandomOrderCRS.fracDegree
    symm
    apply sum_bij (fun w _ => s(v,w))
    · intro w hw; simpa using hw
    · intro a ha b hb hab; exact Sym2.congr_right.mp hab
    · intro e he
      have hh := (G.mem_incidenceFinset v e).mp he
      obtain ⟨w,rfl⟩ := Sym2.mem_iff_exists.mp hh.2
      exact ⟨w,by simpa using hh.1,rfl⟩
    · intro w hw; rfl
  rw [hload]
  have hactive : (∑ w ∈ activeNeighbors G x q v, increment p q z s(v,w)) =
      ∑ w ∈ G.neighborFinset v, increment p q z s(v,w) := by
    apply sum_subset (filter_subset _ _)
    intro w hw hnot
    apply increment_off_active p G x q hp
    rintro ⟨he,hq⟩
    exact hnot (mem_filter.mpr ⟨hw,hq⟩)
  rw [←hactive,←sum_groups_eq_active G x q p hp v]
  apply sum_congr rfl
  intro i hi
  exact group_increment p G x q hp z ⟨v,i⟩

end Loads
end MatchingRounding

-- Solutions/Sol_rounding_linear.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingRounding
variable {N : ℕ} (p : Pairing N) (G : SimpleGraph (Fin N))
    (x : Sym2 (Fin N) → ℝ) (q : ℝ) (hp : ValidPairing G x q p)
include hp

lemma linear_lift (z : Sym2 (Copy p) → ℝ) (f : Sym2 (Fin N) → ℝ) :
    (∑ e ∈ G.edgeFinset, f e*increment p q z e) =
      q*(∑ edge ∈ (virtualGraph p).edgeFinset, f (physicalEdge p edge)*z edge) := by
  have hs : (∑ e ∈ G.edgeFinset.filter (fun e => x e = q), f e*increment p q z e) =
      ∑ e ∈ G.edgeFinset, f e*increment p q z e := by
    apply sum_subset (filter_subset _ _)
    intro e he hn
    have hnot : ¬(e ∈ G.edgeFinset ∧ x e = q) := fun h => hn (mem_filter.mpr h)
    rw [increment_off_active p G x q hp z e hnot,mul_zero]
  rw [←hs,sum_active_edges p G x q hp]
  rw [mul_sum]
  apply sum_congr rfl
  intro e he
  rw [increment_on_edge p G x q hp z e he]
  ring

lemma candidate_linear (z : Sym2 (Copy p) → ℝ) :
    (∑ e ∈ G.edgeFinset, linearCoefficient G x e*(candidate p x q z e-x e)) =
      q*(∑ edge ∈ (virtualGraph p).edgeFinset, linearCoefficient G x (physicalEdge p edge)*z edge) := by
  have he (e : Sym2 (Fin N)) : candidate p x q z e-x e = increment p q z e := by unfold candidate; ring
  simp only [he]
  exact linear_lift p G x q hp z (linearCoefficient G x)

lemma potential_from_signed_bounds (hq : 0 < q) (B : BlockAssignment p) (s : Copy p → Copy p)
    (z : Sym2 (Copy p) → ℝ)
    (hlinear : 0 ≤ ∑ edge ∈ (virtualGraph p).edgeFinset,
      linearCoefficient G x (physicalEdge p edge)*z edge)
    (hquadratic : 2*(∑ v, (load G (candidate p x q z) v-load G x v)^2) ≤ cutCost G x q B s) :
    potential G x-cutCost G x q B s ≤ potential G (candidate p x q z) := by
  have hchange := potential_change G x (candidate p x q z)
  rw [candidate_linear p G x q hp z] at hchange
  have hnonneg := mul_nonneg hq.le hlinear
  linarith

end MatchingRounding

-- Solutions/Sol_rounding_loss.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingRounding
variable {N : ℕ} (p : Pairing N) (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ)
    (q : ℝ) (hp : ValidPairing G x q p) (hq : 0 < q)
    (z : Sym2 (Copy p) → ℝ)
    (hz : ∀ e ∈ (virtualGraph p).edgeFinset, z e = 1 ∨ z e = -1)
include hp hq hz

lemma copyChange_abs (a : Copy p) : |copyChange p q z a| ≤ q*((virtualGraph p).degree a:ℝ) := by
  have he (b : Copy p) (hb : b ∈ (virtualGraph p).neighborFinset a) : |z s(a,b)| = 1 := by
    have hf : s(a,b) ∈ (virtualGraph p).edgeFinset := (virtualGraph p).mem_edgeFinset.mpr
      ((virtualGraph p).mem_edgeSet.mpr ((SimpleGraph.mem_neighborFinset (virtualGraph p) a b).mp hb))
    rcases hz s(a,b) hf with he|he <;> rw [he] <;> norm_num
  unfold copyChange
  rw [abs_mul,abs_of_pos hq]
  calc
    _ ≤ q*(∑ b ∈ (virtualGraph p).neighborFinset a, |z s(a,b)|) :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs ..) hq.le
    _ = q*((virtualGraph p).degree a:ℝ) := by
      rw [sum_congr rfl (fun b hb => he b hb)]
      simp only [sum_const,nsmul_eq_mul,mul_one,SimpleGraph.card_neighborFinset_eq_degree]

lemma copyChange_bound (B : BlockAssignment p) (s : Copy p → Copy p)
    (hbalance : ∀ a, a ∉ selectedSet B s → (group p a).card = 2 →
      (∑ b ∈ (virtualGraph p).neighborFinset a, z s(a,b)) = 0) (a : Copy p) :
    |copyChange p q z a| ≤ q*(2*(if a ∈ selectedSet B s then (1:ℝ) else 0)+
      (if (group p a).card = 1 then (1:ℝ) else 0)) := by
  have habs := copyChange_abs p G x q hp hq z hz a
  rw [virtual_degree_exact G x q p hp a] at habs
  by_cases hsel : a ∈ selectedSet B s
  · simp only [if_pos hsel]
    have hcard : (group p a).card ≤ 2 := by rcases hp.1 a with h|h <;> omega
    have hcardr : ((group p a).card:ℝ) ≤ 2 := by exact_mod_cast hcard
    have hlast : 0 ≤ (if (group p a).card = 1 then (1:ℝ) else 0) := by split_ifs <;> norm_num
    nlinarith
  · simp only [if_neg hsel]
    rcases hp.1 a with hg|hg
    · rw [if_pos hg]
      simpa only [hg,Nat.cast_one,mul_one,mul_zero,zero_add] using habs
    · rw [if_neg (show (group p a).card ≠ 1 by omega)]
      unfold copyChange
      rw [hbalance a hsel hg,mul_zero,abs_zero]
      norm_num

lemma increment_load_bound (B : BlockAssignment p) (s : Copy p → Copy p) (hs : ValidCuts B s)
    (hbalance : ∀ a, a ∉ selectedSet B s → (group p a).card = 2 →
      (∑ b ∈ (virtualGraph p).neighborFinset a, z s(a,b)) = 0) (v : Fin N) :
    |load G (increment p q z) v| ≤ q*(2*(cutCount B s v:ℝ)+(activeDegree G x q v%2:ℕ)) := by
  have hselected : (∑ i : Fin (p v).length, if (⟨v,i⟩:Copy p) ∈ selectedSet B s then (1:ℝ) else 0) =
      (cutCount B s v:ℝ) := by
    rw [←selected_local_count p B s hs v,card_eq_sum_ones,Nat.cast_sum]
    simp only [sum_filter,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  have hendpoint : (∑ i : Fin (p v).length, if ((p v).get i).card = 1 then (1:ℝ) else 0) =
      ((activeDegree G x q v%2:ℕ):ℝ) := by
    rw [←singleton_parity G x q p hp v,card_eq_sum_ones,Nat.cast_sum]
    simp only [sum_filter,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [load_increment_copies p G x q hp z v]
  calc
    _ ≤ ∑ i : Fin (p v).length, |copyChange p q z ⟨v,i⟩| := abs_sum_le_sum_abs ..
    _ ≤ ∑ i : Fin (p v).length, q*(2*(if (⟨v,i⟩:Copy p) ∈ selectedSet B s then (1:ℝ) else 0)+
        (if ((p v).get i).card = 1 then (1:ℝ) else 0)) := by
      apply sum_le_sum
      intro i hi
      exact copyChange_bound p G x q hp hq z hz B s hbalance ⟨v,i⟩
    _ = q*(2*(∑ i : Fin (p v).length, if (⟨v,i⟩:Copy p) ∈ selectedSet B s then (1:ℝ) else 0)+
        (∑ i : Fin (p v).length, if ((p v).get i).card = 1 then (1:ℝ) else 0)) := by
      simp only [mul_add,mul_assoc,sum_add_distrib,←mul_sum]
    _ = _ := by rw [hselected,hendpoint]

lemma candidate_quadratic_bound (B : BlockAssignment p) (s : Copy p → Copy p) (hs : ValidCuts B s)
    (hbalance : ∀ a, a ∉ selectedSet B s → (group p a).card = 2 →
      (∑ b ∈ (virtualGraph p).neighborFinset a, z s(a,b)) = 0) :
    2*(∑ v, (load G (candidate p x q z) v-load G x v)^2) ≤ cutCost G x q B s := by
  have hdelta (v : Fin N) : load G (candidate p x q z) v-load G x v = load G (increment p q z) v := by
    change load G (fun e => x e+increment p q z e) v-load G x v = _
    rw [load_add]
    ring
  have hsq (v : Fin N) : (load G (increment p q z) v)^2 ≤
      q^2*(2*(cutCount B s v:ℝ)+(activeDegree G x q v%2:ℕ))^2 := by
    have hb := increment_load_bound p G x q hp hq z hz B s hs hbalance v
    have hh := mul_self_le_mul_self (abs_nonneg _) hb
    nlinarith [sq_abs (load G (increment p q z) v)]
  simp only [hdelta]
  unfold cutCost
  rw [mul_sum,mul_sum]
  apply sum_le_sum
  intro v hv
  have hh := hsq v
  nlinarith

end MatchingRounding

-- Solutions/Sol_rounding_signed_correct.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingRounding

lemma signed_rounding_correct {N : ℕ} (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ)
    (hx : fractional G x) (hload : ∀ v, load G x v ≤ 1/2) (q : ℝ) (hq : 0 < q)
    (p : Pairing N) (hp : ValidPairing G x q p) (B : BlockAssignment p)
    (s : Copy p → Copy p) (hs : ValidCuts B s) (z : Sym2 (Copy p) → ℝ)
    (hz : ∀ e ∈ (virtualGraph p).edgeFinset, z e = 1 ∨ z e = -1)
    (hbalance : ∀ a, a ∉ selectedSet B s → (group p a).card = 2 →
      (∑ b ∈ (virtualGraph p).neighborFinset a, z s(a,b)) = 0)
    (hlinear : 0 ≤ ∑ edge ∈ (virtualGraph p).edgeFinset,
      linearCoefficient G x (physicalEdge p edge)*z edge) :
    fractional G (candidate p x q z) ∧ (∀ v, load G (candidate p x q z) v ≤ 1) ∧
    (∀ e ∈ G.edgeSet, (x e = q → candidate p x q z e = 0 ∨ candidate p x q z e = 2*q) ∧
      (x e ≠ q → candidate p x q z e = x e)) ∧
    potential G x-cutCost G x q B s ≤ potential G (candidate p x q z) := by
  have hfeas := candidate_feasible p G x q hp hx hload hq z hz
  refine ⟨hfeas.1,hfeas.2,?_,?_⟩
  · intro e he
    refine ⟨fun heq => candidate_active_values p G x q hp z hz e (G.mem_edgeFinset.mpr he) heq,?_⟩
    intro hneq
    unfold candidate
    rw [increment_off_active p G x q hp z e (fun h => hneq h.2),add_zero]
  · exact potential_from_signed_bounds p G x q hp hq B s z hlinear
      (candidate_quadratic_bound p G x q hp hq z hz B s hs hbalance)

end MatchingRounding

-- Solutions/Sol_cut_geometry.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace DeterministicCuts

variable {N : ℕ} {p : Pairing N}

def interaction (B : BlockAssignment p) : SimpleGraph (Copy p) where
  Adj a b := a ≠ b ∧ B a = some a ∧ B b = some b ∧
    ∃ c ∈ block B a, ∃ d ∈ block B b, c.1 = d.1
  symm := ⟨by
    rintro a b ⟨hne,ha,hb,c,hc,d,hd,he⟩
    exact ⟨hne.symm,hb,ha,d,hd,c,hc,he.symm⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

lemma virtual_walk_physical (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (hp : ValidPairing G x q p) {a b : Copy p} (w : (virtualGraph p).Walk a b) :
    ∃ u : G.Walk a.1 b.1, u.length = w.length := by
  induction w with
  | nil => exact ⟨.nil,rfl⟩
  | @cons a b c h w ih =>
    obtain ⟨u,hu⟩ := ih
    have hab := (hp.2.2.1 a b.1 h.2.1).1
    exact ⟨.cons hab u,by simp [hu]⟩

lemma internal_walk_short (B : BlockAssignment p) (ell : ℕ) (hB : ValidBlocks ell B)
    (a : Copy p) (ha : B a = some a) (c : Copy p) (hc : c ∈ block B a) :
    ∃ w : (virtualGraph p).Walk a c, w.length ≤ 65*ell := by
  obtain ⟨w,hw⟩ := (hB.2 a a ha).2.2.2 c hc
  let path := w.toPath
  have hsub : (path.val.support.toFinset : Finset (Copy p)) ⊆ block B a := by
    intro z hz
    exact hw z (w.support_toPath_subset_support (List.mem_toFinset.mp hz))
  have hcard := card_le_card hsub
  rw [List.toFinset_card_of_nodup path.property.support_nodup,SimpleGraph.Walk.length_support] at hcard
  have hbnd := (hB.2 a a ha).2.2.1
  exact ⟨path.val,by omega⟩

lemma member_close (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (hp : ValidPairing G x q p) (B : BlockAssignment p) (ell : ℕ) (hB : ValidBlocks ell B)
    (a : Copy p) (ha : B a = some a) (c : Copy p) (hc : c ∈ block B a) :
    Close G (65*ell) a.1 c.1 := by
  obtain ⟨w,hw⟩ := internal_walk_short B ell hB a ha c hc
  obtain ⟨u,hu⟩ := virtual_walk_physical G x q hp w
  exact ⟨u,hu.trans_le hw⟩

lemma interaction_close (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (hp : ValidPairing G x q p) (B : BlockAssignment p) (ell : ℕ) (hB : ValidBlocks ell B)
    (a b : Copy p) (hab : (interaction B).Adj a b) : Close G (130*ell) a.1 b.1 := by
  obtain ⟨hne,ha,hb,c,hc,d,hd,he⟩ := hab
  obtain ⟨wa,hwa⟩ := member_close G x q hp B ell hB a ha c hc
  have hbclose := member_close G x q hp B ell hB b hb d hd
  rw [←he] at hbclose
  obtain ⟨wb,hwb⟩ := hbclose
  refine ⟨wa.append wb.reverse,?_⟩
  rw [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_reverse]
  omega

lemma interaction_proper (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (hp : ValidPairing G x q p) (B : BlockAssignment p) (ell : ℕ) (hB : ValidBlocks ell B)
    (zeta : ℕ) (col : Copy p → ℕ) (hcol : ReusableColors G ell zeta col) :
    Proper (interaction B) zeta col := by
  refine ⟨hcol.1,?_⟩
  intro a b hab
  apply hcol.2 a b hab.1
  obtain ⟨w,hw⟩ := interaction_close G x q hp B ell hB a b hab
  exact ⟨w,by omega⟩

lemma copyIdentity_injective (ids : Fin N → ℕ) (hi : Function.Injective ids) :
    Function.Injective (fun a : Copy p => Nat.pair (ids a.1) a.2.val) := by
  intro a b he
  have hf := Nat.pair_eq_pair.mp he
  have hfirst := hi hf.1
  cases a with
  | mk v i =>
    cases b with
    | mk w j =>
      dsimp only at hfirst hf
      subst w
      have hij : i = j := Fin.ext hf.2
      subst j
      rfl

lemma interaction_walk (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (hp : ValidPairing G x q p) (B : BlockAssignment p) (ell : ℕ) (hB : ValidBlocks ell B)
    {a b : Copy p} (w : (interaction B).Walk a b) :
    ∃ path : G.Walk a.1 b.1, path.length ≤ 130*ell*w.length := by
  induction w with
  | nil => exact ⟨.nil,by simp⟩
  | @cons a b c h w ih =>
    obtain ⟨edge,he⟩ := interaction_close G x q hp B ell hB a b h
    obtain ⟨path,hpath⟩ := ih
    refine ⟨edge.append path,?_⟩
    rw [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_cons]
    nlinarith

lemma interaction_close_physical (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (hp : ValidPairing G x q p) (B : BlockAssignment p) (ell : ℕ) (hB : ValidBlocks ell B)
    (t : ℕ) (a b : Copy p) (hclose : Close (interaction B) t a b) :
    Close G (130*ell*t) a.1 b.1 := by
  obtain ⟨w,hw⟩ := hclose
  obtain ⟨path,hpath⟩ := interaction_walk G x q hp B ell hB w
  exact ⟨path,hpath.trans (Nat.mul_le_mul_left (130*ell) hw)⟩

end DeterministicCuts

-- Solutions/Sol_rounding_reference.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingRounding
variable {N : ℕ} (ids : Fin N → ℕ) {p : Pairing N}

def vertexName (a : Copy p) : ℕ := Nat.pair (ids a.1) a.2.val

def edgeName (e : Sym2 (Copy p)) : ℕ :=
  Sym2.lift ⟨(fun a b => Nat.pair (min (ids a.1) (ids b.1)) (max (ids a.1) (ids b.1))),
    by intro a b; simp only [min_comm,max_comm]⟩ e

lemma vertexName_injective (hi : Function.Injective ids) : Function.Injective (vertexName ids (p:=p)) :=
  DeterministicCuts.copyIdentity_injective ids hi

lemma edgeName_apply (a b : Copy p) : edgeName ids s(a,b) = Nat.pair (min (ids a.1) (ids b.1)) (max (ids a.1) (ids b.1)) := rfl

lemma edgeName_injective (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (hp : ValidPairing G x q p) (hi : Function.Injective ids) :
    Set.InjOn (edgeName ids (p:=p)) ↑((virtualGraph p).edgeFinset) := by
  intro e he f hf heq
  apply physicalEdge_injective p G x q hp he hf
  apply Sym2.map.injective hi
  obtain ⟨⟨a,b⟩,rfl⟩ := e.exists_rep
  obtain ⟨⟨c,d⟩,rfl⟩ := f.exists_rep
  rw [edgeName_apply,edgeName_apply] at heq
  have hm := congrArg (fun j : ℕ => j.unpair.1) heq
  have hx := congrArg (fun j : ℕ => j.unpair.2) heq
  simp only [Nat.unpair_pair] at hm hx
  change s(ids a.1,ids b.1) = s(ids c.1,ids d.1)
  by_cases hab : ids a.1 ≤ ids b.1 <;> by_cases hcd : ids c.1 ≤ ids d.1
  · simp only [min_eq_left hab,max_eq_right hab,min_eq_left hcd,max_eq_right hcd] at hm hx
    rw [hm,hx]
  · simp only [min_eq_left hab,max_eq_right hab,min_eq_right (le_of_not_ge hcd),max_eq_left (le_of_not_ge hcd)] at hm hx
    rw [hm,hx]
    exact Sym2.eq_swap
  · simp only [min_eq_right (le_of_not_ge hab),max_eq_left (le_of_not_ge hab),min_eq_left hcd,max_eq_right hcd] at hm hx
    rw [hm,hx]
    exact Sym2.eq_swap
  · simp only [min_eq_right (le_of_not_ge hab),max_eq_left (le_of_not_ge hab),min_eq_right (le_of_not_ge hcd),max_eq_left (le_of_not_ge hcd)] at hm hx
    rw [hm,hx]

variable (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (B : BlockAssignment p) (s : Copy p → Copy p)

def referenceSigns : Sym2 (Copy p) → ℝ :=
  componentSign (virtualGraph p) (selectedSet B s) (edgeName ids) (vertexName ids)
    (fun e => linearCoefficient G x (physicalEdge p e))

lemma reference_correct (hp : ValidPairing G x q p) (hi : Function.Injective ids)
    (side : Fin N → Bool) (hside : Bipartition G side) (hq : 0 < q)
    (hx : fractional G x) (hload : ∀ v, load G x v ≤ 1/2) (hs : ValidCuts B s) :
    let z := referenceSigns ids G x B s
    fractional G (candidate p x q z) ∧ (∀ v, load G (candidate p x q z) v ≤ 1) ∧
    (∀ e ∈ G.edgeSet, (x e = q → candidate p x q z e = 0 ∨ candidate p x q z e = 2*q) ∧
      (x e ≠ q → candidate p x q z e = x e)) ∧
    potential G x-cutCost G x q B s ≤ potential G (candidate p x q z) := by
  apply signed_rounding_correct G x hx hload q hq p hp B s hs
  · exact componentSign_unit _ _ _ _ _
  · intro a ha hd
    apply componentSign_balanced (virtualGraph p) (selectedSet B s) (edgeName ids) (vertexName ids)
      (fun e => linearCoefficient G x (physicalEdge p e)) (fun a => side a.1)
    · intro u v huv
      exact hside u.1 v.1 (hp.2.2.1 u v.1 huv.2.1).1
    · exact BlockProof.virtual_degree G x q p hp
    · exact edgeName_injective ids G x q hp hi
    · exact vertexName_injective ids hi
    · exact ha
    · rw [virtual_degree_exact G x q p hp a,hd]
  · exact componentSign_linear _ _ _ _ _ (edgeName_injective ids G x q hp hi)

end MatchingRounding

-- Solutions/Sol_rounding_snapshot.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace RoundingSnapshot
open MatchingRounding

@[ext] structure NamedCopy where
  owner : ℕ
  index : ℕ
  neighbors : Finset ℕ
  cut : Bool
  oldLoad : ℝ

def NamedCopy.name (a : NamedCopy) : ℕ := Nat.pair a.owner a.index

def inputLoad (inp : StageInput) : ℝ := ∑ j ∈ inp.neighbors, inp.edgeValue j

def copiesAt (id : ℕ) (inp : StageInput) : Finset NamedCopy :=
  (univ : Finset (Fin inp.groups.length)).image (fun i =>
    ⟨id,i.val,inp.groups.get i,inp.cut i.val,inputLoad inp⟩)

abbrev Record := ℕ × StageInput

def copies (R : Finset Record) : Finset NamedCopy := R.biUnion (fun r => copiesAt r.1 r.2)

def cutNames (R : Finset Record) : Finset ℕ := ((copies R).filter (fun a => a.cut)).image NamedCopy.name

def copiesAdjacent (a b : NamedCopy) : Prop :=
  a.owner ≠ b.owner ∧ b.owner ∈ a.neighbors ∧ a.owner ∈ b.neighbors

def copyEdge (a b : NamedCopy) : NamedEdge :=
  ⟨Nat.pair (min a.owner b.owner) (max a.owner b.owner), s(a.name,b.name),1-4*a.oldLoad-4*b.oldLoad⟩

def edges (R : Finset Record) : Finset NamedEdge :=
  (copies R).biUnion fun a => (((copies R).filter (copiesAdjacent a)).image (copyEdge a))

def chain (R : Finset Record) : SimpleGraph NamedEdge where
  Adj e f := e ≠ f ∧ e ∈ edges R ∧ f ∈ edges R ∧
    ∃ v, v ∉ cutNames R ∧ v ∈ e.ends ∧ v ∈ f.ends
  symm := ⟨by rintro e f ⟨hne,he,hf,v,hv,hve,hvf⟩; exact ⟨hne.symm,hf,he,v,hv,hvf,hve⟩⟩
  loopless := ⟨by intro e h; exact h.1 rfl⟩

def componentData (R : Finset Record) (i : ℕ) : Finset NamedEdge :=
  finiteComponent (edges R) (chain R) NamedEdge.name i

def rounded (R : Finset Record) (q : ℝ) (own : ℕ) (inp : StageInput) (j : ℕ) : ℝ :=
  if inp.edgeValue j = q then
    q*(1+NamedEdgeData.sign (componentData R (Nat.pair (min own j) (max own j)))
      (Nat.pair (min own j) (max own j)))
  else inp.edgeValue j

section Correct
variable {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (hi : Function.Injective ids)
    (x : Sym2 (Fin N) → ℝ) (p : Pairing N) (B : BlockAssignment p)
    (s : Copy p → Copy p) (side : Fin N → Bool)

abbrev input := stageInput G ids x p (some B) none (cutMarks B s) (fun v => some (side v))

def authentic (R : Finset Record) : Prop :=
  ∀ r ∈ R, ∃ v, r = (ids v,input G ids x p B s side v)

def trueCopy (a : Copy p) : NamedCopy :=
  ⟨ids a.1,a.2.val,(group p a).image ids,cutMarks B s a,load G x a.1⟩

lemma trueCopy_name (a : Copy p) : (trueCopy G ids x p B s a).name = vertexName ids a := rfl

include hi

lemma trueCopy_injective : Function.Injective (trueCopy G ids x p B s) := by
  intro a b hab
  apply vertexName_injective ids hi
  exact congrArg NamedCopy.name hab

lemma edgeValue_correct (v u : Fin N) (hu : G.Adj v u) :
    (input G ids x p B s side v).edgeValue (ids u) = x s(v,u) := by
  change (∑ w ∈ G.neighborFinset v, if ids w = ids u then x s(v,w) else 0) = _
  rw [sum_eq_single u]
  · rw [if_pos rfl]
  · intro w hw hwu
    rw [if_neg (fun h => hwu (hi h))]
  · exact fun h => (h ((SimpleGraph.mem_neighborFinset G v u).mpr hu)).elim

lemma inputLoad_correct (v : Fin N) : inputLoad (input G ids x p B s side v) = load G x v := by
  unfold inputLoad
  change (∑ j ∈ (G.neighborFinset v).image ids, (input G ids x p B s side v).edgeValue j) = _
  rw [sum_image (fun _ _ _ _ he => hi he)]
  change _ = ∑ e ∈ G.incidenceFinset v, x e
  rw [sum_incidence_neighbors G]
  apply sum_congr rfl
  intro u hu
  exact edgeValue_correct G ids hi x p B s side v u ((SimpleGraph.mem_neighborFinset G v u).mp hu)

lemma copiesAt_correct (v : Fin N) :
    copiesAt (ids v) (input G ids x p B s side v) =
      (univ : Finset (Fin (p v).length)).image (fun i => trueCopy G ids x p B s ⟨v,i⟩) := by
  unfold copiesAt
  apply Finset.ext
  intro c
  constructor
  · rintro hc
    obtain ⟨i,hi',rfl⟩ := mem_image.mp hc
    have hlen : i.val < (p v).length := by simpa only [input,stageInput,List.length_map] using i.isLt
    refine mem_image.mpr ⟨⟨i.val,hlen⟩,mem_univ _,?_⟩
    apply NamedCopy.ext
    · rfl
    · rfl
    · change ((p v).get ⟨i.val,hlen⟩).image ids =
        ((p v).map (image ids)).get ⟨i.val,by simpa only [input,stageInput] using i.isLt⟩
      simp only [List.get_eq_getElem,List.getElem_map]
    · simp only [trueCopy,input,stageInput,dif_pos hlen]
    · exact (inputLoad_correct G ids hi x p B s side v).symm

  · rintro hc
    obtain ⟨i,hi',rfl⟩ := mem_image.mp hc
    have hlen : i.val < (input G ids x p B s side v).groups.length := by
      simpa only [input,stageInput,List.length_map] using i.isLt
    refine mem_image.mpr ⟨⟨i.val,hlen⟩,mem_univ _,?_⟩
    apply NamedCopy.ext
    · rfl
    · rfl
    · simp [trueCopy,group,input,stageInput,List.get_eq_getElem]
    · simp only [trueCopy,input,stageInput,dif_pos i.isLt]
    · exact inputLoad_correct G ids hi x p B s side v

lemma copies_authentic (R : Finset Record) (hauth : authentic G ids x p B s side R)
    (c : NamedCopy) (hc : c ∈ copies R) :
    ∃ a : Copy p, trueCopy G ids x p B s a = c ∧ (ids a.1,input G ids x p B s side a.1) ∈ R := by
  obtain ⟨r,hr,hc⟩ := mem_biUnion.mp hc
  obtain ⟨v,rfl⟩ := hauth r hr
  rw [copiesAt_correct G ids hi x p B s side v] at hc
  obtain ⟨i,hi',heq⟩ := mem_image.mp hc
  exact ⟨⟨v,i⟩,heq,hr⟩

lemma copy_mem (R : Finset Record) (a : Copy p)
    (ha : (ids a.1,input G ids x p B s side a.1) ∈ R) : trueCopy G ids x p B s a ∈ copies R := by
  apply mem_biUnion.mpr
  refine ⟨_,ha,?_⟩
  rw [copiesAt_correct G ids hi x p B s side a.1]
  exact mem_image.mpr ⟨a.2,mem_univ _,rfl⟩

end Correct
end RoundingSnapshot

-- Solutions/Sol_rounding_snapshot_edges.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace RoundingSnapshot
open MatchingRounding
section Edges
variable {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (hi : Function.Injective ids)
    (x : Sym2 (Fin N) → ℝ) (p : Pairing N) (B : BlockAssignment p)
    (s : Copy p → Copy p) (side : Fin N → Bool)

def trueEdge (e : Sym2 (Copy p)) : NamedEdge :=
  edgeRecord (edgeName ids) (vertexName ids) (fun e => linearCoefficient G x (physicalEdge p e)) e

lemma trueEdge_apply (a b : Copy p) : trueEdge G ids x p s(a,b) =
    copyEdge (trueCopy G ids x p B s a) (trueCopy G ids x p B s b) := by
  unfold trueEdge edgeRecord
  dsimp only
  rw [physicalEdge_apply,linearCoefficient_apply]
  rfl

include hi

lemma copies_adjacent (a b : Copy p) :
    copiesAdjacent (trueCopy G ids x p B s a) (trueCopy G ids x p B s b) ↔ (virtualGraph p).Adj a b := by
  change (ids a.1 ≠ ids b.1 ∧ ids b.1 ∈ (group p a).image ids ∧ ids a.1 ∈ (group p b).image ids) ↔ _
  simp only [mem_image,hi.eq_iff,exists_eq_right]
  exact ⟨fun h => ⟨fun hab => h.1 (congrArg ids hab),h.2⟩,
    fun h => ⟨fun hab => h.1 (hi hab),h.2⟩⟩

lemma edges_authentic (R : Finset Record) (hauth : authentic G ids x p B s side R)
    (e : NamedEdge) (he : e ∈ edges R) :
    ∃ f : (virtualGraph p).edgeSet, trueEdge G ids x p f.val = e := by
  obtain ⟨c,hc,he⟩ := mem_biUnion.mp he
  obtain ⟨d,hd,heq⟩ := mem_image.mp he
  obtain ⟨hd,hcd⟩ := mem_filter.mp hd
  obtain ⟨a,ha,har⟩ := copies_authentic G ids hi x p B s side R hauth c hc
  obtain ⟨b,hb,hbr⟩ := copies_authentic G ids hi x p B s side R hauth d hd
  have hab : (virtualGraph p).Adj a b := (copies_adjacent G ids hi x p B s a b).mp (by rw [ha,hb]; exact hcd)
  refine ⟨⟨s(a,b),(virtualGraph p).mem_edgeSet.mpr hab⟩,?_⟩
  rw [trueEdge_apply G ids x p B s a b,ha,hb,heq]

lemma edge_mem (R : Finset Record) (a b : Copy p) (hab : (virtualGraph p).Adj a b)
    (ha : (ids a.1,input G ids x p B s side a.1) ∈ R)
    (hb : (ids b.1,input G ids x p B s side b.1) ∈ R) :
    trueEdge G ids x p s(a,b) ∈ edges R := by
  rw [trueEdge_apply G ids x p B s a b]
  apply mem_biUnion.mpr
  refine ⟨_,copy_mem G ids hi x p B s side R a ha,?_⟩
  exact mem_image.mpr ⟨_,mem_filter.mpr ⟨copy_mem G ids hi x p B s side R b hb,
    (copies_adjacent G ids hi x p B s a b).mpr hab⟩,rfl⟩

lemma cutNames_sound (R : Finset Record) (hauth : authentic G ids x p B s side R)
    (a : Copy p) (ha : vertexName ids a ∈ cutNames R) : a ∈ selectedSet B s := by
  obtain ⟨c,hc,heq⟩ := mem_image.mp ha
  obtain ⟨hc,hcut⟩ := mem_filter.mp hc
  obtain ⟨b,hb,hbr⟩ := copies_authentic G ids hi x p B s side R hauth c hc
  have hba : b = a := vertexName_injective ids hi (by change (trueCopy G ids x p B s b).name = _; rw [hb]; exact heq)
  subst b
  rw [←hb] at hcut
  exact (mem_selectedSet B s a).mpr (of_decide_eq_true hcut)

lemma cutNames_complete (R : Finset Record) (a : Copy p)
    (ha : (ids a.1,input G ids x p B s side a.1) ∈ R) (hsel : a ∈ selectedSet B s) :
    vertexName ids a ∈ cutNames R := by
  refine mem_image.mpr ⟨_,mem_filter.mpr ⟨copy_mem G ids hi x p B s side R a ha,?_⟩,rfl⟩
  change decide (∃ b, B b = some b ∧ s b = a) = true
  exact decide_eq_true ((mem_selectedSet B s a).mp hsel)

end Edges
end RoundingSnapshot

-- Solutions/Sol_rounding_snapshot_chain.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace RoundingSnapshot
open MatchingRounding
section Chain
variable {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (hi : Function.Injective ids)
    (x : Sym2 (Fin N) → ℝ) (q : ℝ) (p : Pairing N) (hp : ValidPairing G x q p)
    (B : BlockAssignment p) (s : Copy p → Copy p) (side : Fin N → Bool)
include hi hp

lemma trueEdge_name_injective : Function.Injective (fun e : (virtualGraph p).edgeSet => (trueEdge G ids x p e.val).name) := by
  intro e f heq
  apply Subtype.ext
  exact edgeName_injective ids G x q hp hi ((virtualGraph p).mem_edgeFinset.mpr e.property)
    ((virtualGraph p).mem_edgeFinset.mpr f.property) heq

lemma trueEdge_injective : Function.Injective (fun e : (virtualGraph p).edgeSet => trueEdge G ids x p e.val) := by
  intro e f heq
  exact trueEdge_name_injective G ids hi x q p hp (congrArg NamedEdge.name heq)

lemma edge_creator_present (R : Finset Record) (hauth : authentic G ids x p B s side R)
    (e : (virtualGraph p).edgeSet) (he : trueEdge G ids x p e.val ∈ edges R)
    (a : Copy p) (ha : a ∈ e.val) : (ids a.1,input G ids x p B s side a.1) ∈ R := by
  obtain ⟨c,hc,he⟩ := mem_biUnion.mp he
  obtain ⟨d,hd,heq⟩ := mem_image.mp he
  obtain ⟨hd,hcd⟩ := mem_filter.mp hd
  obtain ⟨u,hu,hur⟩ := copies_authentic G ids hi x p B s side R hauth c hc
  obtain ⟨v,hv,hvr⟩ := copies_authentic G ids hi x p B s side R hauth d hd
  have huv := (copies_adjacent G ids hi x p B s u v).mp (by rw [hu,hv]; exact hcd)
  have hrecord : trueEdge G ids x p s(u,v) = trueEdge G ids x p e.val := by
    rw [trueEdge_apply G ids x p B s u v,hu,hv,heq]
  have heq' : s(u,v) = e.val := congrArg Subtype.val (trueEdge_injective G ids hi x q p hp
    (a₁:=⟨s(u,v),(virtualGraph p).mem_edgeSet.mpr huv⟩) (a₂:=e) hrecord)
  rw [←heq'] at ha
  rcases Sym2.mem_iff.mp ha with rfl|rfl
  · exact hur
  · exact hvr

lemma chain_sound (R : Finset Record) (hauth : authentic G ids x p B s side R)
    (e f : (virtualGraph p).edgeSet)
    (h : (chain R).Adj (trueEdge G ids x p e.val) (trueEdge G ids x p f.val)) :
    (edgeChain (virtualGraph p) (selectedSet B s)).Adj e f := by
  obtain ⟨hne,he,hf,v,hvc,hve,hvf⟩ := h
  have hve' : v ∈ Sym2.map (vertexName ids) e.val := hve
  obtain ⟨a,ha,hav⟩ := Sym2.mem_map.mp hve'
  have haf : a ∈ f.val := (mapped_vertex_mem (vertexName ids) (vertexName_injective ids hi) a f.val).mp (by rw [hav]; exact hvf)
  refine ⟨fun hef => hne (congrArg (fun e => trueEdge G ids x p e.val) hef),a,?_,ha,haf⟩
  intro hsel
  apply hvc
  rw [←hav]
  exact cutNames_complete G ids hi x p B s side R a
    (edge_creator_present G ids hi x q p hp B s side R hauth e he a ha) hsel

lemma chain_complete (R : Finset Record) (hauth : authentic G ids x p B s side R)
    (e f : (virtualGraph p).edgeSet)
    (he : trueEdge G ids x p e.val ∈ edges R) (hf : trueEdge G ids x p f.val ∈ edges R)
    (h : (edgeChain (virtualGraph p) (selectedSet B s)).Adj e f) :
    (chain R).Adj (trueEdge G ids x p e.val) (trueEdge G ids x p f.val) := by
  obtain ⟨hne,a,hac,hae,haf⟩ := h
  refine ⟨fun heq => hne (trueEdge_injective G ids hi x q p hp heq),he,hf,vertexName ids a,?_,?_,?_⟩
  · exact fun hcut => hac (cutNames_sound G ids hi x p B s side R hauth a hcut)
  · exact Sym2.mem_map.mpr ⟨a,hae,rfl⟩
  · exact Sym2.mem_map.mpr ⟨a,haf,rfl⟩

lemma componentData_correct (R : Finset Record) (hauth : authentic G ids x p B s side R)
    (e : (virtualGraph p).edgeSet)
    (hcover : ∀ f ∈ BlockProof.comp (edgeChain (virtualGraph p) (selectedSet B s)) e,
      trueEdge G ids x p f.val ∈ edges R) :
    componentData R (edgeName ids e.val) =
      MatchingRounding.componentData (virtualGraph p) (selectedSet B s)
        (edgeName ids) (vertexName ids) (fun f => linearCoefficient G x (physicalEdge p f)) e := by
  have heq := finiteComponent_eq (edgeChain (virtualGraph p) (selectedSet B s)) (edges R) (chain R)
    (fun f => trueEdge G ids x p f.val) NamedEdge.name
    (edges_authentic G ids hi x p B s side R hauth)
    (fun a b h => ⟨h.2.1,h.2.2.1⟩)
    (chain_sound G ids hi x q p hp B s side R hauth)
    (chain_complete G ids hi x q p hp B s side R hauth)
    (trueEdge_name_injective G ids hi x q p hp) e hcover
  change finiteComponent (edges R) (chain R) NamedEdge.name (edgeName ids e.val) = _ at heq
  change finiteComponent _ _ _ _ = _
  rw [heq]
  simp only [MatchingRounding.componentData,namedData,componentEdges,image_image,trueEdge,Function.comp_def]

end Chain
end RoundingSnapshot

-- Solutions/Sol_rounding_radius.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingRounding
section Radius
variable {N : ℕ} (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (p : Pairing N) (hp : ValidPairing G x q p)
include hp

lemma physical_edge_close (e : (virtualGraph p).edgeSet) (a b : Copy p)
    (ha : a ∈ e.val) (hb : b ∈ e.val) : Close G 1 a.1 b.1 := by
  by_cases hab : a = b
  · subst b
    exact ⟨.nil,by simp⟩
  · have he : e.val = s(a,b) := (Sym2.mem_and_mem_iff hab).mp ⟨ha,hb⟩
    have hadj : (virtualGraph p).Adj a b := (virtualGraph p).mem_edgeSet.mp (by rw [←he]; exact e.property)
    exact ⟨(hp.2.2.1 a b.1 hadj.2.1).1.toWalk,by simp⟩

lemma chain_walk_physical (C : Finset (Copy p)) {e f : (virtualGraph p).edgeSet}
    (w : (edgeChain (virtualGraph p) C).Walk e f) (a b : Copy p)
    (ha : a ∈ e.val) (hb : b ∈ f.val) :
    ∃ u : G.Walk a.1 b.1, u.length ≤ w.length+1 := by
  have aux : ∀ {e f : (virtualGraph p).edgeSet}, (w : (edgeChain (virtualGraph p) C).Walk e f) →
      ∀ a b : Copy p, a ∈ e.val → b ∈ f.val → ∃ u : G.Walk a.1 b.1, u.length ≤ w.length+1 := by
    intro e f w
    induction w with
    | nil => intro a b ha hb; exact physical_edge_close G x q p hp _ a b ha hb
    | @cons e f g hef w ih =>
      intro a b ha hb
      obtain ⟨hne,c,hc,hce,hcf⟩ := hef
      obtain ⟨u,hu⟩ := physical_edge_close G x q p hp e a c ha hce
      obtain ⟨v,hv⟩ := ih c b hcf hb
      refine ⟨u.append v,?_⟩
      rw [SimpleGraph.Walk.length_append]
      change u.length+v.length ≤ (w.length+1)+1
      omega
  exact aux w a b ha hb

lemma chain_component_physical (ell : ℕ) (hell : 2 ≤ ell) (B : BlockAssignment p)
    (hB : ValidBlocks ell B) (s : Copy p → Copy p) (hs : ValidCuts B s)
    (e f : (virtualGraph p).edgeSet) (hf : f ∈ BlockProof.comp (edgeChain (virtualGraph p) (selectedSet B s)) e)
    (a b : Copy p) (ha : a ∈ e.val) (hb : b ∈ f.val) : Close G (522*ell) a.1 b.1 := by
  have hr : (edgeChain (virtualGraph p) (selectedSet B s)).Reachable e f := (mem_comp_iff _ _ _).mp hf
  obtain ⟨w,hw⟩ := hr.exists_walk_length_eq_dist
  obtain ⟨u,hu⟩ := chain_walk_physical G x q p hp _ w a b ha hb
  have hd := BlockProof.comp_card_dist (edgeChain (virtualGraph p) (selectedSet B s)) hr
  have hc := edge_chain_block_bound G x q p hp ell hell B hB s hs e
  exact ⟨u,by omega⟩

end Radius
end MatchingRounding

-- Solutions/Sol_rounding_snapshot_radius.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace RoundingSnapshot
open MatchingRounding

lemma flood_component_data {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
    (hi : Function.Injective ids) (x : Sym2 (Fin N) → ℝ) (q : ℝ) (p : Pairing N)
    (hp : ValidPairing G x q p) (ell : ℕ) (hell : 2 ≤ ell) (B : BlockAssignment p)
    (hB : ValidBlocks ell B) (s : Copy p → Copy p) (hs : ValidCuts B s)
    (side : Fin N → Bool) (e : (virtualGraph p).edgeSet) (a : Copy p) (ha : a ∈ e.val) :
    let R := LocalFlood.flood G ids (input G ids x p B s side) (522*ell) a.1
    componentData R (edgeName ids e.val) =
      MatchingRounding.componentData (virtualGraph p) (selectedSet B s)
        (edgeName ids) (vertexName ids) (fun f => linearCoefficient G x (physicalEdge p f)) e := by
  dsimp only
  apply componentData_correct G ids hi x q p hp B s side
  · exact LocalFlood.flood_authentic G ids (input G ids x p B s side) (522*ell) a.1
  · intro f hf
    obtain ⟨⟨c,d⟩,heq⟩ := f.val.exists_rep
    change s(c,d) = f.val at heq
    have hc : c ∈ f.val := by rw [←heq]; exact Sym2.mem_mk_left _ _
    have hd : d ∈ f.val := by rw [←heq]; exact Sym2.mem_mk_right _ _
    have hAdj : (virtualGraph p).Adj c d := (virtualGraph p).mem_edgeSet.mp (by rw [heq]; exact f.property)
    have hclosec := chain_component_physical G x q p hp ell hell B hB s hs e f hf a c ha hc
    have hclosed := chain_component_physical G x q p hp ell hell B hB s hs e f hf a d ha hd
    rw [←heq]
    apply edge_mem G ids hi x p B s side _ c d hAdj
    · exact LocalFlood.flood_close G ids (input G ids x p B s side) _ a.1 c.1 hclosec
    · exact LocalFlood.flood_close G ids (input G ids x p B s side) _ a.1 d.1 hclosed

end RoundingSnapshot

-- Solutions/Sol_rounding_protocol.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace RoundingSnapshot

def physicalRounds (k : StageParameters) : ℕ := 522*k.ell

structure RoundingState where
  parameters : StageParameters
  ownID : ℕ
  original : StageInput
  elapsed : ℕ
  snapshot : Finset Record

def protocol : Deterministic StageParameters StageInput (ℕ → ℝ) where
  program := {
    State := RoundingState
    Msg := Finset Record
    rounds := physicalRounds
    init := fun k id inp _ => ⟨k,id,inp,0,{(id,inp)}⟩
    send := RoundingState.snapshot
    step := fun st msgs => {st with elapsed := st.elapsed+1, snapshot := LocalFlood.merge st.snapshot msgs}
    out := fun st => if st.elapsed < physicalRounds st.parameters then st.original.edgeValue
      else rounded st.snapshot st.parameters.q st.ownID st.original }
  tape_independent := by intros; rfl

lemma protocol_run {V : Type} [Fintype V] (G : SimpleGraph V) (k : StageParameters)
    (ids : V → ℕ) (inp : V → StageInput) (t : ℕ) : ∀ v,
    protocol.program.run G k ids inp (fun _ _ => false) t v =
      ⟨k,ids v,inp v,t,LocalFlood.flood G ids inp t v⟩ := by
  induction t with
  | zero => intro v; rfl
  | succ t ih =>
    intro v
    rw [SmoothedMIS.LocalAlg.run]
    simp only [ih]
    have hn : univ.filter (G.Adj v) = G.neighborFinset v := by ext u; simp
    change RoundingState.mk k (ids v) (inp v) (t+1)
      (LocalFlood.merge (LocalFlood.flood G ids inp t v)
        ((univ.filter (G.Adj v)).val.map (LocalFlood.flood G ids inp t))) = _
    rw [hn]
    rfl

lemma protocol_before {V : Type} [Fintype V] (G : SimpleGraph V) (k : StageParameters)
    (ids : V → ℕ) (inp : V → StageInput) (t : ℕ) (ht : t < physicalRounds k) (v : V) :
    protocol.program.out (protocol.program.run G k ids inp (fun _ _ => false) t v) = (inp v).edgeValue := by
  rw [protocol_run]
  change (if t < physicalRounds k then _ else _) = _
  exact if_pos ht

lemma protocol_final {V : Type} [Fintype V] (G : SimpleGraph V) (k : StageParameters)
    (ids : V → ℕ) (inp : V → StageInput) (v : V) :
    protocol.program.out (protocol.program.run G k ids inp (fun _ _ => false) (physicalRounds k) v) =
      rounded (LocalFlood.flood G ids inp (physicalRounds k) v) k.q (ids v) (inp v) := by
  rw [protocol_run]
  change (if physicalRounds k < physicalRounds k then _ else _) = _
  exact if_neg (lt_irrefl _)

lemma protocol_output {V : Type} [Fintype V] (G : SimpleGraph V) (k : StageParameters)
    (ids : V → ℕ) (inp : V → StageInput) (v : V) :
    protocol.program.output G k ids inp (fun _ _ => false) v =
      rounded (LocalFlood.flood G ids inp (physicalRounds k) v) k.q (ids v) (inp v) :=
  protocol_final G k ids inp v

lemma protocol_budget (k : StageParameters) : protocol.program.rounds k ≤ budget 522 k.ell := by
  change 522*k.ell ≤ ⌈(522:ℝ)*(k.ell:ℝ)⌉₊
  exact_mod_cast (Nat.le_ceil ((522:ℝ)*(k.ell:ℝ)))

end RoundingSnapshot

-- Solutions/Sol_rounding_reports.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace RoundingSnapshot
open MatchingRounding
section Reports
variable {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (hi : Function.Injective ids)
    (x : Sym2 (Fin N) → ℝ) (k : StageParameters) (p : Pairing N)
    (hp : ValidPairing G x k.q p) (hell : 2 ≤ k.ell) (B : BlockAssignment p)
    (hB : ValidBlocks k.ell B) (s : Copy p → Copy p) (hs : ValidCuts B s) (side : Fin N → Bool)
include hi hp hell hB hs

lemma edgeName_physical (e : Sym2 (Copy p)) : edgeName ids e = edgeIdentity ids (physicalEdge p e) := by
  obtain ⟨⟨a,b⟩,rfl⟩ := e.exists_rep
  rfl

lemma rounded_on_neighbor (u v : Fin N) (huv : G.Adj u v) :
    rounded (LocalFlood.flood G ids (input G ids x p B s side) (physicalRounds k) u) k.q (ids u)
      (input G ids x p B s side u) (ids v) =
      candidate p x k.q (referenceSigns ids G x B s) s(u,v) := by
  unfold rounded
  rw [edgeValue_correct G ids hi x p B s side u v huv]
  by_cases hactive : x s(u,v) = k.q
  · rw [if_pos hactive]
    have hm : s(u,v) ∈ ((virtualGraph p).edgeFinset).image (physicalEdge p) := by
      rw [physicalEdge_image p G x k.q hp]
      exact mem_filter.mpr ⟨G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr huv),hactive⟩
    obtain ⟨f,hf,hphys⟩ := mem_image.mp hm
    let e : (virtualGraph p).edgeSet := ⟨f,(virtualGraph p).mem_edgeFinset.mp hf⟩
    have hu : u ∈ physicalEdge p f := by rw [hphys]; exact Sym2.mem_mk_left _ _
    obtain ⟨a,ha,hau⟩ := Sym2.mem_map.mp hu
    have hd := flood_component_data G ids hi x k.q p hp k.ell hell B hB s hs side e a ha
    dsimp only at hd
    rw [hau] at hd
    have hname : edgeName ids f = Nat.pair (min (ids u) (ids v)) (max (ids u) (ids v)) := by
      rw [edgeName_physical G ids hi x k p hp hell B hB s hs f,hphys]
      rfl
    change componentData (LocalFlood.flood G ids (input G ids x p B s side) (physicalRounds k) u)
      (edgeName ids f) = _ at hd
    rw [←hname,hd]
    have hz : referenceSigns ids G x B s f =
        NamedEdgeData.sign (MatchingRounding.componentData (virtualGraph p) (selectedSet B s)
          (edgeName ids) (vertexName ids) (fun f => linearCoefficient G x (physicalEdge p f)) e) (edgeName ids f) :=
      componentSign_on _ _ _ _ _ e
    rw [←hz,←hphys]
    unfold candidate
    rw [increment_on_edge p G x k.q hp _ f hf]
    have hxf : x (physicalEdge p f) = k.q := by rw [hphys]; exact hactive
    rw [hxf]
    ring
  · rw [if_neg hactive]
    symm
    unfold candidate
    rw [increment_off_active p G x k.q hp _ s(u,v) (fun h => hactive h.2),add_zero]

lemma protocol_reports (hx : fractional G x) :
    ReportsWeights G ids (execute protocol G k ids (input G ids x p B s side))
      (candidate p x k.q (referenceSigns ids G x B s)) := by
  refine ⟨?_,?_⟩
  · intro e he
    unfold candidate
    rw [increment_off_active p G x k.q hp _ e (fun h => he (G.mem_edgeFinset.mp h.1)),add_zero]
    exact hx.2.1 e he
  · intro u v huv
    constructor
    · rw [execute,protocol_output]
      exact rounded_on_neighbor G ids hi x k p hp hell B hB s hs side u v huv
    · rw [execute,protocol_output]
      simpa only [Sym2.eq_swap] using rounded_on_neighbor G ids hi x k p hp hell B hB s hs side v u huv.symm

end Reports
end RoundingSnapshot

-- Solutions/Sol_rounding_trace.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace RoundingSnapshot

lemma input_reports {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
    (hi : Function.Injective ids) (x : Sym2 (Fin N) → ℝ) (hx : fractional G x)
    (p : Pairing N) (B : BlockAssignment p) (s : Copy p → Copy p) (side : Fin N → Bool) :
    ReportsWeights G ids (fun v => (input G ids x p B s side v).edgeValue) x := by
  refine ⟨hx.2.1,?_⟩
  intro u v huv
  exact ⟨edgeValue_correct G ids hi x p B s side u v huv,
    by simpa only [Sym2.eq_swap] using edgeValue_correct G ids hi x p B s side v u huv.symm⟩

lemma protocol_trace {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
    (k : StageParameters) (hell : 2 ≤ k.ell) (inp : Fin N → StageInput)
    (x y : Sym2 (Fin N) → ℝ) (hx : fractional G x) (hy : fractional G y)
    (hinitial : ReportsWeights G ids (fun v => (inp v).edgeValue) x)
    (hfinal : ReportsWeights G ids (execute protocol G k ids inp) y) :
    ∃ trace : ℕ → Sym2 (Fin N) → ℝ,
      trace 0 = x ∧ trace (protocol.program.rounds k) = y ∧
      ∀ t, t ≤ protocol.program.rounds k → fractional G (trace t) ∧
        ReportsWeights G ids (fun v => protocol.program.out
          (protocol.program.run G k ids inp (fun _ _ => false) t v)) (trace t) := by
  let trace : ℕ → Sym2 (Fin N) → ℝ := fun t => if t < physicalRounds k then x else y
  have hzero : 0 < physicalRounds k := by unfold physicalRounds; omega
  have htrzero : trace 0 = x := if_pos hzero
  have htrfinal : trace (physicalRounds k) = y := if_neg (lt_irrefl _)
  refine ⟨trace,htrzero,htrfinal,?_⟩
  intro t ht
  by_cases hbefore : t < physicalRounds k
  · have htr : trace t = x := if_pos hbefore
    rw [htr]
    refine ⟨hx,?_⟩
    have hout : (fun v => protocol.program.out (protocol.program.run G k ids inp (fun _ _ => false) t v)) =
        (fun v => (inp v).edgeValue) := funext (protocol_before G k ids inp t hbefore)
    rw [hout]
    exact hinitial
  · have heq : t = physicalRounds k := by change t ≤ physicalRounds k at ht; omega
    subst t
    rw [htrfinal]
    exact ⟨hy,hfinal⟩

end RoundingSnapshot

-- Solutions/Sol_rounding_stage.lean
open FasterDistributedMatching.ApproximateMatching
open MatchingRounding RoundingSnapshot

/- Lemma 3.6, printed p.12 / PDF p.14. This section's bipartition is retained;
odd cycles are not silently admitted. Intermediate feasibility refers to the protocol's
edge readout at every physical round, including initialization and termination. -/
theorem solution :
    ∃ (A : Deterministic StageParameters StageInput (ℕ → ℝ)) (C : ℝ), 0 < C ∧
      (∀ k, 2 ≤ k.ell → A.program.rounds k ≤ budget C k.ell) ∧
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (k : StageParameters),
        2 ≤ k.ell → 0 < k.q → boundedGraph G k.n k.degree →
        ∀ side : Fin N → Bool, Bipartition G side →
          ∀ (x : Sym2 (Fin N) → ℝ), fractional G x → (∀ v, load G x v ≤ 1 / 2) →
            ∀ p : Pairing N, ValidPairing G x k.q p →
              ∀ B : BlockAssignment p, ValidBlocks k.ell B →
                ∀ s : Copy p → Copy p, ValidCuts B s →
                  ∀ ids : Fin N → ℕ, Function.Injective ids →
                    let inp := stageInput G ids x p (some B) none (cutMarks B s) (fun v => some (side v))
                    ∃ (x' : Sym2 (Fin N) → ℝ) (trace : ℕ → Sym2 (Fin N) → ℝ),
                      ReportsWeights G ids (execute A G k ids inp) x' ∧
                      fractional G x' ∧ (∀ v, load G x' v ≤ 1) ∧
                      (∀ e ∈ G.edgeSet, (x e = k.q → x' e = 0 ∨ x' e = 2 * k.q) ∧
                        (x e ≠ k.q → x' e = x e)) ∧
                      potential G x - cutCost G x k.q B s ≤ potential G x' ∧
                      trace 0 = x ∧ trace (A.program.rounds k) = x' ∧
                      ∀ t, t ≤ A.program.rounds k → fractional G (trace t) ∧
                        ReportsWeights G ids (fun v => A.program.out
                          (A.program.run G k ids inp (fun _ _ => false) t v)) (trace t)  := by
  refine ⟨protocol,522,by norm_num,?_,?_⟩
  · intro k _
    exact protocol_budget k
  · intro N G k hell hq hb side hside x hx hload p hp B hB s hs ids hi
    dsimp only
    let z := referenceSigns ids G x B s
    let y := candidate p x k.q z
    have hgood := reference_correct ids G x k.q B s hp hi side hside hq hx hload hs
    have hout : ReportsWeights G ids (execute protocol G k ids (input G ids x p B s side)) y :=
      protocol_reports G ids hi x k p hp hell B hB s hs side hx
    obtain ⟨trace,hzero,hfinal,htrace⟩ := protocol_trace G ids k hell (input G ids x p B s side) x y hx hgood.1
      (input_reports G ids hi x hx p B s side) hout
    exact ⟨y,trace,hout,hgood.1,hgood.2.1,hgood.2.2.1,hgood.2.2.2,hzero,hfinal,htrace⟩

