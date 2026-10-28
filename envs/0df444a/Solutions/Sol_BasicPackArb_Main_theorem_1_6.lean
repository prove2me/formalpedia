-- Prove2me | solution 1 for BasicPackArb.Main.theorem_1_6
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-27T07:18:14.885057+00:00
-- url     : https://prove2.me/submissions/d41b3346-7406-443d-bff0-0d89692ec51a

/- SPDX-License-Identifier: Apache-2.0 -/
import Mathlib
import Definitions.Def_BasicPackArb_Main_RootedDigraph


-- Complete module: BPProof.FiniteRank

open Set

namespace BasicPackArb.Main.BPFresh

variable {S : Type*} [Fintype S]

noncomputable def rankNat (M : Matroid S) (X : Set S) : ℕ := (M.eRk X).toNat

lemma rank_finite (M : Matroid S) (X : Set S) : M.eRk X ≠ ⊤ := by
  exact Matroid.eRk_ne_top_iff.mpr (Matroid.RankFinite.isRkFinite X)

lemma cast_rankNat (M : Matroid S) (X : Set S) :
    (rankNat M X : ℕ∞) = M.eRk X :=
  ENat.natCast_toNat (rank_finite M X)

lemma rankNat_mono (M : Matroid S) {X Y : Set S} (h : X ⊆ Y) :
    rankNat M X ≤ rankNat M Y := by
  have hh := M.eRk_mono h
  rw [← cast_rankNat M X, ← cast_rankNat M Y] at hh
  exact_mod_cast hh

lemma rankNat_submod (M : Matroid S) (X Y : Set S) :
    rankNat M (X ∩ Y) + rankNat M (X ∪ Y) ≤ rankNat M X + rankNat M Y := by
  have hh := M.eRk_submod X Y
  simp only [← cast_rankNat M] at hh
  exact_mod_cast hh

lemma span_eq_closure (M : Matroid S) (hM : M.E = univ) (X : Set S) :
    Span M X = M.closure X := by
  ext s
  constructor
  · intro hs
    by_contra hn
    have he := M.eRk_insert_eq_add_one (e := s) (X := X) ⟨by simp [hM], hn⟩
    have hh : M.eRk (insert s X) = M.eRk X := hs
    rw [hh, ← cast_rankNat M X] at he
    have hh' : rankNat M X = rankNat M X + 1 := by exact_mod_cast he
    omega
  · intro hs
    change M.eRk (insert s X) = M.eRk X
    apply le_antisymm
    · calc
        M.eRk (insert s X) ≤ M.eRk (M.closure X) :=
          M.eRk_mono (insert_subset hs (M.subset_closure X (by simp [hM])))
        _ = M.eRk X := M.eRk_closure_eq X
    · exact M.eRk_mono (subset_insert s X)

omit [Fintype S] in
lemma rankNat_closure (M : Matroid S) (X : Set S) :
    rankNat M (M.closure X) = rankNat M X := by
  unfold rankNat
  rw [M.eRk_closure_eq]

lemma closure_eq_of_subset_rank (M : Matroid S) {X Y : Set S}
    (hXY : X ⊆ Y) (hr : rankNat M Y ≤ rankNat M X) : M.closure X = M.closure Y := by
  apply (Matroid.RankFinite.isRkFinite X).closure_eq_closure_of_subset_of_eRk_ge_eRk hXY
  rw [← cast_rankNat M X, ← cast_rankNat M Y]
  exact_mod_cast hr

end BasicPackArb.Main.BPFresh

-- Complete module: BPProof.Necessity

namespace BasicPackArb.Main.BPFresh
open Set

variable {V Arc S : Type*} [DecidableEq V]

theorem path_crossing (D : Digraph V Arc) (A : Finset Arc) (X : Finset V)
    {u v : V} (hu : u ∉ X) (hv : v ∈ X)
    (hp : Relation.ReflTransGen (fun x y => ∃ a ∈ A, D.tail a = x ∧ D.head a = y) u v) :
    ∃ a ∈ A, D.tail a ∉ X ∧ D.head a ∈ X := by
  induction hp with
  | refl => exact (hu hv).elim
  | @tail w z hp hwz ih =>
    by_cases hw : w ∈ X
    · exact ih hw
    · obtain ⟨a, ha, hat, hah⟩ := hwz
      exact ⟨a, ha, hat ▸ hw, hah ▸ hv⟩

theorem packing_necessity [Fintype S] (D : Digraph V Arc) (π : S → V)
    (M : Matroid S) (hM : M.E = univ) (T : S → Arborescence D)
    (hT : IsBasicPacking D π M T) : MIndependent π M ∧ MConnected D π M := by
  classical
  constructor
  · intro v
    apply (hT.2.2 v).indep.subset
    intro s hs
    have hr := (T s).root_mem
    simpa [hT.1 s, show π s = v from hs] using hr
  · intro X hX
    obtain ⟨v, hv⟩ := hX
    let B : Finset S := Finset.univ.filter (fun s => v ∈ (T s).verts)
    let I : Finset S := B.filter (fun s => π s ∈ X)
    let O : Finset S := B.filter (fun s => π s ∉ X)
    have hB : M.IsBase (B : Set S) := by simpa [B] using hT.2.2 v
    have hBc : B.card = rankNat M univ := by
      have he := hB.isBasis_ground.encard_eq_eRk
      rw [hM, ← cast_rankNat] at he
      simpa using he
    have hI : M.Indep (I : Set S) :=
      hB.indep.subset (by intro s hs; exact (Finset.mem_filter.mp hs).1)
    have hIc : I.card ≤ rankNat M (π ⁻¹' (X : Set V)) := by
      have hh := M.eRk_mono (a := (I : Set S)) (b := π ⁻¹' (X : Set V))
        (by intro s hs; exact (Finset.mem_filter.mp hs).2)
      rw [hI.eRk_eq_encard, ← cast_rankNat] at hh
      simpa using hh
    have hchoice : ∀ s ∈ O, ∃ a ∈ (T s).arcs, D.tail a ∉ X ∧ D.head a ∈ X := by
      intro s hs
      obtain ⟨hsB, hsX⟩ := Finset.mem_filter.mp hs
      have hsv : v ∈ (T s).verts := (Finset.mem_filter.mp hsB).2
      exact path_crossing D (T s).arcs X (by simpa [hT.1 s] using hsX) hv ((T s).reach v hsv)
    choose f hf using hchoice
    have hOc : O.card ≤ (D.enteringArcs X).card := by
      by_cases ho : O.Nonempty
      · obtain ⟨q, hq⟩ := ho
        apply Finset.card_le_card_of_injOn (fun s => if hs : s ∈ O then f s hs else f q hq)
        · intro s hs
          change s ∈ O at hs
          change (if hs : s ∈ O then f s hs else f q hq) ∈ D.enteringArcs X
          rw [dif_pos hs]
          exact Finset.mem_filter.mpr ⟨(T s).arcs_subset (hf s hs).1, (hf s hs).2⟩
        · intro s hs t ht he
          change s ∈ O at hs
          change t ∈ O at ht
          change (if hs : s ∈ O then f s hs else f q hq) =
            (if ht : t ∈ O then f t ht else f q hq) at he
          rw [dif_pos hs, dif_pos ht] at he
          by_contra hst
          exact Finset.disjoint_left.mp (hT.2.1 s t hst) (hf s hs).1 (he ▸ (hf t ht).1)
      · simp [Finset.not_nonempty_iff_eq_empty.mp ho]
    have hsplit : I.card + O.card = B.card := by
      simpa [I, O] using Finset.card_filter_add_card_filter_not (s := B) (p := fun s => π s ∈ X)
    have hn : rankNat M univ ≤ (D.enteringArcs X).card + rankNat M (π ⁻¹' (X : Set V)) := by omega
    rw [← cast_rankNat, ← cast_rankNat]
    exact_mod_cast hn

end BasicPackArb.Main.BPFresh

-- Complete module: BPProof.CutBasics

open Set

namespace BasicPackArb.Main.BPFresh

variable {V Arc S : Type*} [Fintype V] [DecidableEq V] [Fintype S]

def rootSet (π : S → V) (X : Finset V) : Set S := π ⁻¹' (X : Set V)

def Tight (D : Digraph V Arc) (π : S → V) (M : Matroid S) (X : Finset V) : Prop :=
  D.inDeg X + rankNat M (rootSet π X) = rankNat M univ

def Dominates (π : S → V) (M : Matroid S) (X Y : Finset V) : Prop :=
  rootSet π X ⊆ M.closure (rootSet π Y)

def GoodArc (D : Digraph V Arc) (π : S → V) (M : Matroid S) (a : Arc) : Prop :=
  π ⁻¹' {D.tail a} ⊆ M.closure (π ⁻¹' {D.head a})

open Classical in
def CutExtension (D : Digraph V Arc) (π : S → V) (M : Matroid S) (a : Arc) (s : S) : Prop :=
  ∀ X : Finset V, X.Nonempty →
    M.eRk univ ≤ ((D.deleteArc a).inDeg X : ℕ∞) +
      M.eRk (if D.head a ∈ X then insert s (rootSet π X) else rootSet π X)

omit [Fintype V] in
lemma connected_rankNat (D : Digraph V Arc) (π : S → V) (M : Matroid S)
    (hc : MConnected D π M) (X : Finset V) (hX : X.Nonempty) :
    rankNat M univ ≤ D.inDeg X + rankNat M (rootSet π X) := by
  have hh := hc X hX
  change M.eRk univ ≤ (D.inDeg X : ℕ∞) + M.eRk (rootSet π X) at hh
  rw [← cast_rankNat M univ, ← cast_rankNat M (rootSet π X)] at hh
  exact_mod_cast hh

omit [Fintype V] [DecidableEq V] [Fintype S] in
lemma rootSet_mono (π : S → V) {X Y : Finset V} (h : X ⊆ Y) :
    rootSet π X ⊆ rootSet π Y := fun _ hx => h hx

omit [Fintype V] [Fintype S] in
lemma rootSet_union (π : S → V) (X Y : Finset V) :
    rootSet π (X ∪ Y) = rootSet π X ∪ rootSet π Y := by
  ext s
  simp [rootSet]

omit [Fintype V] [Fintype S] in
lemma rootSet_inter (π : S → V) (X Y : Finset V) :
    rootSet π (X ∩ Y) = rootSet π X ∩ rootSet π Y := by
  ext s
  simp [rootSet]

omit [Fintype V] in
lemma entering_submod (D : Digraph V Arc) (X Y : Finset V) :
    D.inDeg (X ∩ Y) + D.inDeg (X ∪ Y) ≤ D.inDeg X + D.inDeg Y := by
  classical
  unfold Digraph.inDeg Digraph.enteringArcs
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a ha
  simp only [Finset.mem_inter, Finset.mem_union]
  by_cases htX : D.tail a ∈ X <;> by_cases htY : D.tail a ∈ Y <;>
    by_cases hhX : D.head a ∈ X <;> by_cases hhY : D.head a ∈ Y <;> simp_all

end BasicPackArb.Main.BPFresh

-- Complete module: BPProof.FailedExtension

open Set

namespace BasicPackArb.Main.BPFresh

variable {V Arc S : Type*} [Fintype V] [DecidableEq V] [Fintype S]

omit [Fintype V] in
lemma delete_inDeg (D : Digraph V Arc) [DecidableEq Arc] {a : Arc} (ha : a ∈ D.arcs)
    (X : Finset V) :
    D.inDeg X = (D.deleteArc a).inDeg X +
      if D.tail a ∉ X ∧ D.head a ∈ X then 1 else 0 := by
  classical
  have he : (D.deleteArc a).enteringArcs X = (D.enteringArcs X).erase a := by
    change (D.arcs.erase a).filter (fun e => D.tail e ∉ X ∧ D.head e ∈ X) =
      (D.arcs.filter (fun e => D.tail e ∉ X ∧ D.head e ∈ X)).erase a
    ext e
    simp only [Finset.mem_filter, Finset.mem_erase]
    tauto
  unfold Digraph.inDeg
  rw [he]
  by_cases h : D.tail a ∉ X ∧ D.head a ∈ X
  · have hm : a ∈ D.enteringArcs X := Finset.mem_filter.mpr ⟨ha,h⟩
    rw [if_pos h, Finset.card_erase_of_mem hm]
    have hp : 0 < (D.enteringArcs X).card := Finset.card_pos.mpr ⟨a,hm⟩
    omega
  · rw [if_neg h, Finset.erase_eq_of_notMem]
    · omega
    · simpa [Digraph.enteringArcs, ha] using h

omit [Fintype V] in
lemma failed_extension_witness (D : Digraph V Arc) (π : S → V) (M : Matroid S)
    (hM : M.E = univ) (hc : MConnected D π M) {a : Arc} (ha : a ∈ D.arcs)
    {s : S} (hf : ¬ CutExtension D π M a s) :
    ∃ X : Finset V, X.Nonempty ∧ D.tail a ∉ X ∧ D.head a ∈ X ∧
      Tight D π M X ∧ s ∈ M.closure (rootSet π X) := by
  classical
  unfold CutExtension at hf
  push Not at hf
  obtain ⟨X, hX, hfail⟩ := hf
  have hfail' : (D.deleteArc a).inDeg X +
      rankNat M (if D.head a ∈ X then insert s (rootSet π X) else rootSet π X) < rankNat M univ := by
    rw [← cast_rankNat M _, ← cast_rankNat M _] at hfail
    exact_mod_cast hfail
  have hconn := connected_rankNat D π M hc X hX
  have hdel := delete_inDeg D ha X
  have hsub : rootSet π X ⊆ (if D.head a ∈ X then insert s (rootSet π X) else rootSet π X) := by
    split_ifs
    · exact subset_insert _ _
    · exact subset_rfl
  have hmono := rankNat_mono M hsub
  have hent : D.tail a ∉ X ∧ D.head a ∈ X := by
    by_contra hn
    rw [if_neg hn] at hdel
    omega
  rw [if_pos hent] at hdel
  rw [if_pos hent.2] at hfail' hmono
  have ht : Tight D π M X := by unfold Tight; omega
  have hr : rankNat M (insert s (rootSet π X)) = rankNat M (rootSet π X) := by omega
  have hr' : s ∈ Span M (rootSet π X) := by
    change M.eRk (insert s (rootSet π X)) = M.eRk (rootSet π X)
    rw [← cast_rankNat M _, ← cast_rankNat M _, hr]
  rw [span_eq_closure M hM] at hr'
  exact ⟨X,hX,hent.1,hent.2,ht,hr'⟩

end BasicPackArb.Main.BPFresh

-- Complete module: BPProof.TightUncrossing

open Set

namespace BasicPackArb.Main.BPFresh

variable {V Arc S : Type*} [Fintype V] [DecidableEq V] [Fintype S]

omit [Fintype V] in
lemma tight_uncross (D : Digraph V Arc) (π : S → V) (M : Matroid S)
    (hc : MConnected D π M) {X Y : Finset V} (hX : Tight D π M X)
    (hY : Tight D π M Y) (hne : (X ∩ Y).Nonempty) :
    Tight D π M (X ∩ Y) ∧ Tight D π M (X ∪ Y) ∧
    rankNat M (rootSet π (X ∩ Y)) + rankNat M (rootSet π (X ∪ Y)) =
      rankNat M (rootSet π X) + rankNat M (rootSet π Y) := by
  have hu : (X ∪ Y).Nonempty := hne.mono (fun _ h => Finset.mem_union_left _ (Finset.mem_inter.mp h).1)
  have hi := connected_rankNat D π M hc (X ∩ Y) hne
  have hj := connected_rankNat D π M hc (X ∪ Y) hu
  have hr := rankNat_submod M (rootSet π X) (rootSet π Y)
  rw [← rootSet_inter, ← rootSet_union] at hr
  have hd := entering_submod D X Y
  unfold Tight at *
  omega

lemma rank_insert_of_closure (M : Matroid S) (hM : M.E = univ)
    {P : Set S} {s : S} (hs : s ∈ M.closure P) :
    rankNat M (insert s P) = rankNat M P := by
  have h : s ∈ Span M P := by rw [span_eq_closure M hM]; exact hs
  exact congrArg ENat.toNat h

lemma modular_closure_inter (M : Matroid S) (hM : M.E = univ)
    (P Q : Set S)
    (hmod : rankNat M (P ∩ Q) + rankNat M (P ∪ Q) = rankNat M P + rankNat M Q)
    {s : S} (hp : s ∈ M.closure P) (hq : s ∈ M.closure Q) :
    s ∈ M.closure (P ∩ Q) := by
  have hp' := rank_insert_of_closure M hM hp
  have hq' := rank_insert_of_closure M hM hq
  have hh := rankNat_submod M (insert s P) (insert s Q)
  have hi : insert s P ∩ insert s Q = insert s (P ∩ Q) := by ext x; simp; tauto
  have hu : insert s P ∪ insert s Q = insert s (P ∪ Q) := by ext x; simp; tauto
  rw [hi, hu, hp', hq'] at hh
  have hi' := rankNat_mono M (subset_insert s (P ∩ Q))
  have hu' := rankNat_mono M (subset_insert s (P ∪ Q))
  have he : rankNat M (insert s (P ∩ Q)) = rankNat M (P ∩ Q) := by omega
  have he' : M.eRk (insert s (P ∩ Q)) = M.eRk (P ∩ Q) := by
    rw [← cast_rankNat M _, ← cast_rankNat M _, he]
  have hs : s ∈ Span M (P ∩ Q) := he'
  rwa [span_eq_closure M hM] at hs

end BasicPackArb.Main.BPFresh

-- Complete module: BPProof.BadArcWitness

open Set

namespace BasicPackArb.Main.BPFresh

variable {V Arc S : Type*} [Fintype V] [DecidableEq V] [Fintype S]

lemma bad_arc_tight_witness (D : Digraph V Arc) (π : S → V) (M : Matroid S)
    (hM : M.E = univ) (hc : MConnected D π M)
    (hfail : ∀ a ∈ D.arcs, ∀ s : S, π s = D.tail a →
      s ∉ M.closure (π ⁻¹' {D.head a}) → ¬ CutExtension D π M a s)
    {a : Arc} (ha : a ∈ D.arcs) (hbad : ¬ GoodArc D π M a) :
    ∃ X : Finset V, D.tail a ∉ X ∧ D.head a ∈ X ∧ Tight D π M X ∧
      π ⁻¹' {D.tail a} ⊆ M.closure (rootSet π X) := by
  classical
  obtain ⟨s0, hs0, hn0⟩ := Set.not_subset.mp hbad
  obtain ⟨X0, _, ht0, hh0, hT0, _⟩ :=
    failed_extension_witness D π M hM hc ha (hfail a ha s0 hs0 hn0)
  let F : Finset (Finset V) := Finset.univ.filter
    (fun X => D.tail a ∉ X ∧ D.head a ∈ X ∧ Tight D π M X)
  have hF : X0 ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht0, hh0, hT0⟩
  obtain ⟨X, hXF, hmax⟩ := F.exists_max_image Finset.card ⟨X0,hF⟩
  obtain ⟨ht, hh, hT⟩ := (Finset.mem_filter.mp hXF).2
  refine ⟨X,ht,hh,hT,?_⟩
  intro s hs
  by_cases hn : s ∈ M.closure (π ⁻¹' {D.head a})
  · have hsub : π ⁻¹' {D.head a} ⊆ rootSet π X := by
      intro z hz
      change π z = D.head a at hz
      change π z ∈ X
      rwa [hz]
    exact M.closure_mono hsub hn
  · obtain ⟨Y, _, hyt, hyh, hyT, hys⟩ :=
      failed_extension_witness D π M hM hc ha (hfail a ha s hs hn)
    have hne : (X ∩ Y).Nonempty := ⟨D.head a, Finset.mem_inter.mpr ⟨hh,hyh⟩⟩
    have huT := (tight_uncross D π M hc hT hyT hne).2.1
    have huF : X ∪ Y ∈ F := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by simpa using And.intro ht hyt,
        Finset.mem_union_left _ hh, huT⟩
    have hcard := hmax (X ∪ Y) huF
    have he : X ∪ Y = X := (Finset.eq_of_subset_of_card_le Finset.subset_union_left hcard).symm
    have hyX : Y ⊆ X := by rw [← he]; exact Finset.subset_union_right
    exact M.closure_mono (rootSet_mono π hyX) hys

end BasicPackArb.Main.BPFresh

-- Complete module: BPProof.ReachTight

open Set

namespace BasicPackArb.Main.BPFresh

variable {V Arc S : Type*} [Fintype V] [DecidableEq V] [Fintype S]

omit [Fintype V] in
lemma mem_reachSet_iff (D : Digraph V Arc) (X : Finset V) (u v : V) :
    u ∈ D.reachSet X v ↔ D.ReachVia (fun _ => True) X u v := by
  classical
  simp [Digraph.reachSet, Digraph.reachSetVia, Digraph.ReachVia]

omit [Fintype V] in
lemma reachSet_subset (D : Digraph V Arc) (X : Finset V) (v : V) :
    D.reachSet X v ⊆ X := by
  intro u hu
  exact ((mem_reachSet_iff D X u v).mp hu).1

omit [Fintype V] in
lemma mem_reachSet_self (D : Digraph V Arc) (X : Finset V) {v : V} (hv : v ∈ X) :
    v ∈ D.reachSet X v :=
  (mem_reachSet_iff D X v v).mpr ⟨hv, Relation.ReflTransGen.refl⟩

omit [Fintype V] in
lemma entering_reachSet_subset (D : Digraph V Arc) (X : Finset V) (v : V) :
    D.enteringArcs (D.reachSet X v) ⊆ D.enteringArcs X := by
  intro a ha
  obtain ⟨haD, htail, hhead⟩ := Finset.mem_filter.mp ha
  refine Finset.mem_filter.mpr ⟨haD, ?_, reachSet_subset D X v hhead⟩
  intro htX
  apply htail
  apply (mem_reachSet_iff D X (D.tail a) v).mpr
  refine ⟨htX, ?_⟩
  exact (((mem_reachSet_iff D X (D.head a) v).mp hhead).2).head
    ⟨a, haD, trivial, rfl, rfl, htX, reachSet_subset D X v hhead⟩

omit [Fintype V] in
lemma reachSet_tight (D : Digraph V Arc) (π : S → V) (M : Matroid S)
    (hc : MConnected D π M) {X : Finset V} (ht : Tight D π M X)
    {v : V} (hv : v ∈ X) :
    Tight D π M (D.reachSet X v) ∧
      M.closure (rootSet π (D.reachSet X v)) = M.closure (rootSet π X) := by
  have hn : (D.reachSet X v).Nonempty := ⟨v, mem_reachSet_self D X hv⟩
  have hb := connected_rankNat D π M hc _ hn
  have hd : D.inDeg (D.reachSet X v) ≤ D.inDeg X :=
    Finset.card_le_card (entering_reachSet_subset D X v)
  have hs := rootSet_mono π (reachSet_subset D X v)
  have hr := rankNat_mono M hs
  have he : rankNat M (rootSet π X) ≤ rankNat M (rootSet π (D.reachSet X v)) := by
    unfold Tight at ht
    omega
  exact ⟨by unfold Tight at *; omega, closure_eq_of_subset_rank M hs he⟩

omit [Fintype V] [DecidableEq V] [Fintype S] in
lemma good_reach_dominates (D : Digraph V Arc) (π : S → V) (M : Matroid S)
    (hM : M.E = univ) (X : Finset V) {u v : V}
    (hr : D.ReachVia (GoodArc D π M) X u v) :
    π ⁻¹' {u} ⊆ M.closure (π ⁻¹' {v}) := by
  induction hr.2 with
  | refl => exact M.subset_closure _ (by simp [hM])
  | @tail b c hpath hedge ih =>
    obtain ⟨e, _, hg, ht, hh, _, _⟩ := hedge
    have hbc : π ⁻¹' {b} ⊆ M.closure (π ⁻¹' {c}) := by
      simpa only [GoodArc, ht, hh] using hg
    exact (ih ⟨hr.1,hpath⟩).trans (M.closure_subset_closure_of_subset_closure hbc)

end BasicPackArb.Main.BPFresh

-- Complete module: BPProof.AdmissibleExtension

open Set

namespace BasicPackArb.Main.BPFresh

variable {V Arc S : Type*} [Fintype V] [DecidableEq V] [Fintype S]

lemma exists_admissible_extension (D : Digraph V Arc) (π : S → V) (M : Matroid S)
    (hM : M.E = univ) (hc : MConnected D π M)
    (hbad : ∃ a ∈ D.arcs, ¬ GoodArc D π M a) :
    ∃ a ∈ D.arcs, ∃ s : S, π s = D.tail a ∧
      s ∉ M.closure (π ⁻¹' {D.head a}) ∧ CutExtension D π M a s := by
  classical
  by_contra hf
  push Not at hf
  have hw : ∀ {a : Arc}, a ∈ D.arcs → ¬ GoodArc D π M a →
      ∃ X : Finset V, D.tail a ∉ X ∧ D.head a ∈ X ∧ Tight D π M X ∧
        π ⁻¹' {D.tail a} ⊆ M.closure (rootSet π X) :=
    by
      intro a ha hb
      exact bad_arc_tight_witness D π M hM hc hf (a := a) ha hb
  let F : Finset (Arc × Finset V) := (D.arcs ×ˢ Finset.univ).filter
    (fun p => ¬ GoodArc D π M p.1 ∧ D.tail p.1 ∉ p.2 ∧ D.head p.1 ∈ p.2 ∧
      Tight D π M p.2 ∧ π ⁻¹' {D.tail p.1} ⊆ M.closure (rootSet π p.2))
  have hF : F.Nonempty := by
    obtain ⟨a,ha,hb⟩ := hbad
    obtain ⟨X,ht,hh,hT,hd⟩ := hw ha hb
    exact ⟨(a,X), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,Finset.mem_univ _⟩,hb,ht,hh,hT,hd⟩⟩
  obtain ⟨⟨a,X⟩, hp, hmin⟩ := F.exists_min_image (fun p => p.2.card) hF
  obtain ⟨hpair,hba,hat,hah,hXT,hdom⟩ := Finset.mem_filter.mp hp
  have ha : a ∈ D.arcs := (Finset.mem_product.mp hpair).1
  have hreach : D.reachSet X (D.head a) = X := by
    obtain ⟨hYT,he⟩ := reachSet_tight D π M hc hXT hah
    have hyh := mem_reachSet_self D X hah
    have hyt : D.tail a ∉ D.reachSet X (D.head a) := fun h => hat (reachSet_subset D X _ h)
    have hyd : π ⁻¹' {D.tail a} ⊆ M.closure (rootSet π (D.reachSet X (D.head a))) := by
      rw [he]
      exact hdom
    have hm : (a,D.reachSet X (D.head a)) ∈ F :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,Finset.mem_univ _⟩,hba,hyt,hyh,hYT,hyd⟩
    exact Finset.eq_of_subset_of_card_le (reachSet_subset D X _) (hmin _ hm)
  have hex : ∃ b ∈ D.arcs, D.tail b ∈ X ∧ D.head b ∈ X ∧ ¬ GoodArc D π M b := by
    by_contra hn
    push Not at hn
    apply hba
    apply hdom.trans
    apply M.closure_subset_closure_of_subset_closure
    intro s hs
    have hu : π s ∈ D.reachSet X (D.head a) := by rw [hreach]; exact hs
    have hr := (mem_reachSet_iff D X (π s) (D.head a)).mp hu
    have hgood : D.ReachVia (GoodArc D π M) X (π s) (D.head a) := by
      refine ⟨hr.1, Relation.ReflTransGen.mono ?_ _ _ hr.2⟩
      intro u v huv
      obtain ⟨b,hb,_,ht,hh,huX,hvX⟩ := huv
      exact ⟨b,hb,hn b hb (ht.symm ▸ huX) (hh.symm ▸ hvX),ht,hh,huX,hvX⟩
    exact good_reach_dominates D π M hM X hgood (by simp)
  obtain ⟨b,hb,hbt,hbh,hbb⟩ := hex
  obtain ⟨Y,hyt,hyh,hYT,hyd⟩ := hw hb hbb
  have hne : (X ∩ Y).Nonempty := ⟨D.head b,Finset.mem_inter.mpr ⟨hbh,hyh⟩⟩
  obtain ⟨hIT,_,hmod⟩ := tight_uncross D π M hc hXT hYT hne
  have hid : π ⁻¹' {D.tail b} ⊆ M.closure (rootSet π (X ∩ Y)) := by
    intro s hs
    rw [rootSet_inter]
    apply modular_closure_inter M hM (rootSet π X) (rootSet π Y)
    · simpa only [rootSet_inter,rootSet_union] using hmod
    · apply M.mem_closure_of_mem _ (by simp [hM])
      change π s ∈ X
      change π s = D.tail b at hs
      rwa [hs]
    · exact hyd hs
  have hit : D.tail b ∉ X ∩ Y := fun h => hyt (Finset.mem_inter.mp h).2
  have hih : D.head b ∈ X ∩ Y := Finset.mem_inter.mpr ⟨hbh,hyh⟩
  have hm : (b,X ∩ Y) ∈ F :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb,Finset.mem_univ _⟩,hbb,hit,hih,hIT,hid⟩
  have hcard := hmin _ hm
  have he : X ∩ Y = X := Finset.eq_of_subset_of_card_le Finset.inter_subset_left hcard
  exact hit (he.symm ▸ hbt)

end BasicPackArb.Main.BPFresh

-- Complete module: BPProof.NoBadPacking

open Set

namespace BasicPackArb.Main.BPFresh

variable {V Arc S : Type*} [Fintype V] [DecidableEq V] [Fintype S]

lemma no_bad_fibre_base (D : Digraph V Arc) (π : S → V) (M : Matroid S)
    (hM : M.E = univ) (hi : MIndependent π M) (hc : MConnected D π M)
    (hg : ∀ a ∈ D.arcs, GoodArc D π M a) (v : V) :
    M.IsBase (π ⁻¹' {v}) := by
  classical
  have hT : Tight D π M Finset.univ := by
    simp [Tight, Digraph.inDeg, Digraph.enteringArcs, rootSet]
  obtain ⟨_, he⟩ := reachSet_tight D π M hc hT (Finset.mem_univ v)
  have hdom : rootSet π (D.reachSet Finset.univ v) ⊆ M.closure (π ⁻¹' {v}) := by
    intro s hs
    have hr := (mem_reachSet_iff D Finset.univ (π s) v).mp hs
    have hrg : D.ReachVia (GoodArc D π M) Finset.univ (π s) v := by
      refine ⟨hr.1, Relation.ReflTransGen.mono ?_ _ _ hr.2⟩
      intro u w huw
      obtain ⟨a,ha,_,ht,hh,hu,hw⟩ := huw
      exact ⟨a,ha,hg a ha,ht,hh,hu,hw⟩
    exact good_reach_dominates D π M hM Finset.univ hrg (by simp)
  apply (hi v).isBase_of_ground_subset_closure
  have hcl := M.closure_subset_closure_of_subset_closure hdom
  rw [he] at hcl
  have hroot : rootSet π Finset.univ = univ := by ext s; simp [rootSet]
  rw [hroot] at hcl
  rw [hM]
  exact (M.subset_closure univ (by simp [hM])).trans hcl

lemma no_bad_packing (D : Digraph V Arc) (π : S → V) (M : Matroid S)
    (hM : M.E = univ) (hi : MIndependent π M) (hc : MConnected D π M)
    (hg : ∀ a ∈ D.arcs, GoodArc D π M a) :
    ∃ T : S → Arborescence D, IsBasicPacking D π M T := by
  refine ⟨fun s => Arborescence.single D (π s), ?_⟩
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro s t hst
    exact Finset.disjoint_empty_left _
  · intro v
    have hb := no_bad_fibre_base D π M hM hi hc hg v
    convert hb using 1
    ext s
    simp [Arborescence.single, eq_comm]

end BasicPackArb.Main.BPFresh

-- Complete module: BPProof.ParallelExtension

namespace BasicPackArb.Main.BPFresh
open Set
open scoped Classical

variable {V Arc S : Type*}

def collapse (s : S) : Option S → S := fun z => z.getD s

def extendPlacement (π : S → V) (v : V) : Option S → V
  | none => v
  | some z => π z

@[simp] theorem collapse_none (s : S) : collapse s none = s := rfl
@[simp] theorem collapse_some (s z : S) : collapse s (some z) = z := rfl
@[simp] theorem extendPlacement_none (π : S → V) (v : V) :
    extendPlacement π v none = v := rfl
@[simp] theorem extendPlacement_some (π : S → V) (v : V) (z : S) :
    extendPlacement π v (some z) = π z := rfl

theorem collapse_surjective (s : S) : Function.Surjective (collapse s) :=
  fun z => ⟨some z, rfl⟩

theorem collapse_image_preimage (s : S) (π : S → V) (v : V) (X : Set V) :
    collapse s '' (extendPlacement π v ⁻¹' X) =
      if v ∈ X then insert s (π ⁻¹' X) else π ⁻¹' X := by
  classical
  ext z
  by_cases hv : v ∈ X
  · simp only [hv, ↓reduceIte, mem_image, mem_preimage, mem_insert_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      cases a with
      | none => exact Or.inl rfl
      | some a => exact Or.inr ha
    · rintro (rfl | hz)
      · exact ⟨none, hv, rfl⟩
      · exact ⟨some z, hz, rfl⟩
  · simp only [hv, ↓reduceIte, mem_image, mem_preimage]
    constructor
    · rintro ⟨a, ha, rfl⟩
      cases a with
      | none => exact (hv ha).elim
      | some a => exact ha
    · intro hz
      exact ⟨some z, hz, rfl⟩

theorem comap_full_ground (M : Matroid S) (hM : M.E = univ) (s : S) :
    (M.comap (collapse s)).E = univ := by
  simp [Matroid.comap_ground_eq, hM]

theorem comap_total_rank (M : Matroid S) (s : S) :
    (M.comap (collapse s)).eRk univ = M.eRk univ := by
  rw [Matroid.eRk_comap, Set.image_univ, Set.range_eq_univ.mpr (collapse_surjective s)]

theorem extend_independent (π : S → V) (M : Matroid S) (hM : M.E = univ)
    (hi : MIndependent π M) (s : S) (v : V)
    (hs : s ∉ M.closure (π ⁻¹' {v})) :
    MIndependent (extendPlacement π v) (M.comap (collapse s)) := by
  classical
  have hsv : π s ≠ v := by
    intro h
    apply hs
    exact M.mem_closure_of_mem (by simpa using h)
  intro w
  rw [Matroid.comap_indep_iff, collapse_image_preimage]
  constructor
  · by_cases hw : v = w
    · subst w
      simp only [mem_singleton_iff, ↓reduceIte]
      exact (hi v).insert_indep_iff.mpr (Or.inl ⟨by simp [hM], hs⟩)
    · simpa [hw] using hi w
  · intro a ha b hb hab
    cases a <;> cases b <;> simp_all [collapse, extendPlacement]

theorem extend_connected [DecidableEq V] [DecidableEq Arc]
    (D : Digraph V Arc) (π : S → V) (M : Matroid S) (a : Arc) (s : S)
    (hcut : ∀ X : Finset V, X.Nonempty →
      M.eRk univ ≤ ((D.deleteArc a).inDeg X : ℕ∞) +
        M.eRk (if D.head a ∈ X then insert s (π ⁻¹' (X : Set V))
          else π ⁻¹' (X : Set V))) :
    MConnected (D.deleteArc a) (extendPlacement π (D.head a))
      (M.comap (collapse s)) := by
  intro X hX
  rw [comap_total_rank, Matroid.eRk_comap, collapse_image_preimage]
  by_cases hh : D.head a ∈ X
  · simpa only [Finset.mem_coe, hh, ↓reduceIte] using hcut X hX
  · simpa only [Finset.mem_coe, hh, ↓reduceIte] using hcut X hX

theorem comap_base_image (M : Matroid S) (hM : M.E = univ) (s : S)
    {B : Set (Option S)} (hB : (M.comap (collapse s)).IsBase B) :
    M.IsBase (collapse s '' B) := by
  rw [Matroid.comap_isBase_iff] at hB
  have h := hB.1
  rw [hM, preimage_univ, Set.image_univ, Set.range_eq_univ.mpr (collapse_surjective s)] at h
  exact (M.isBasis_ground_iff).mp (by simpa [hM] using h)

end BasicPackArb.Main.BPFresh

-- Complete module: BPProof.TreeJoining

namespace BasicPackArb.Main.BPFresh

variable {V Arc : Type*} [DecidableEq V] [DecidableEq Arc]

def restoreTree (D : Digraph V Arc) (a : Arc) (T : Arborescence (D.deleteArc a)) :
    Arborescence D where
  verts := T.verts
  arcs := T.arcs
  root := T.root
  arcs_subset := fun _ hx => Finset.mem_of_mem_erase (T.arcs_subset hx)
  tail_mem := T.tail_mem
  head_mem := T.head_mem
  root_mem := T.root_mem
  root_inDeg := T.root_inDeg
  inDeg_one := T.inDeg_one
  reach := T.reach

theorem join_trees (D : Digraph V Arc) (T U : Arborescence D) (a : Arc)
    (ha : a ∈ D.arcs) (ht : D.tail a = T.root) (hh : D.head a = U.root)
    (hdis : Disjoint T.verts U.verts) :
    ∃ R : Arborescence D, R.root = T.root ∧ R.verts = T.verts ∪ U.verts ∧
      R.arcs = insert a (T.arcs ∪ U.arcs) := by
  classical
  have hdu := Finset.disjoint_left.mp hdis
  have htU : T.root ∉ U.verts := fun h => hdu T.root_mem h
  have huT : U.root ∉ T.verts := fun h => hdu h U.root_mem
  have hroots : U.root ≠ T.root := fun h => huT (h ▸ T.root_mem)
  have hnoT (e : Arc) (he : e ∈ T.arcs) : D.head e ∉ U.verts :=
    fun h => hdu (T.head_mem e he) h
  have hnoU (e : Arc) (he : e ∈ U.arcs) : D.head e ∉ T.verts :=
    fun h => hdu h (U.head_mem e he)
  let R : Arborescence D := {
    verts := T.verts ∪ U.verts
    arcs := insert a (T.arcs ∪ U.arcs)
    root := T.root
    arcs_subset := by
      intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact ha
      · rcases Finset.mem_union.mp he with he | he
        · exact T.arcs_subset he
        · exact U.arcs_subset he
    tail_mem := by
      intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact Finset.mem_union_left _ (ht ▸ T.root_mem)
      · rcases Finset.mem_union.mp he with he | he
        · exact Finset.mem_union_left _ (T.tail_mem e he)
        · exact Finset.mem_union_right _ (U.tail_mem e he)
    head_mem := by
      intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact Finset.mem_union_right _ (hh ▸ U.root_mem)
      · rcases Finset.mem_union.mp he with he | he
        · exact Finset.mem_union_left _ (T.head_mem e he)
        · exact Finset.mem_union_right _ (U.head_mem e he)
    root_mem := Finset.mem_union_left _ T.root_mem
    root_inDeg := by
      intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact hh ▸ hroots
      · rcases Finset.mem_union.mp he with he | he
        · exact T.root_inDeg e he
        · intro h
          exact hnoU e he (h ▸ T.root_mem)
    inDeg_one := by
      intro v hv hvr
      by_cases hvT : v ∈ T.verts
      · obtain ⟨e, he, huniq⟩ := T.inDeg_one v hvT hvr
        refine ⟨e, ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ he.1), he.2⟩, ?_⟩
        rintro b ⟨hb, hhead⟩
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact (huT (by simpa [← hh, hhead] using hvT)).elim
        · rcases Finset.mem_union.mp hb with hb | hb
          · exact huniq b ⟨hb, hhead⟩
          · exact (hnoU b hb (hhead ▸ hvT)).elim
      · have hvU : v ∈ U.verts := (Finset.mem_union.mp hv).resolve_left hvT
        by_cases hvroot : v = U.root
        · refine ⟨a, ⟨Finset.mem_insert_self _ _, hh.trans hvroot.symm⟩, ?_⟩
          rintro b ⟨hb, hhead⟩
          rcases Finset.mem_insert.mp hb with rfl | hb
          · rfl
          · rcases Finset.mem_union.mp hb with hb | hb
            · exact (hnoT b hb (hhead ▸ hvU)).elim
            · exact (U.root_inDeg b hb (hhead.trans hvroot)).elim
        · obtain ⟨e, he, huniq⟩ := U.inDeg_one v hvU hvroot
          refine ⟨e, ⟨Finset.mem_insert_of_mem (Finset.mem_union_right _ he.1), he.2⟩, ?_⟩
          rintro b ⟨hb, hhead⟩
          rcases Finset.mem_insert.mp hb with rfl | hb
          · exact (hvroot (hhead.symm.trans hh)).elim
          · rcases Finset.mem_union.mp hb with hb | hb
            · exact (hnoT b hb (hhead ▸ hvU)).elim
            · exact huniq b ⟨hb, hhead⟩
    reach := by
      intro v hv
      have hT (w : V) (hw : w ∈ T.verts) :
          Relation.ReflTransGen (fun x y => ∃ b ∈ insert a (T.arcs ∪ U.arcs),
            D.tail b = x ∧ D.head b = y) T.root w :=
        Relation.ReflTransGen.mono (by
          rintro x y ⟨b, hb, hbt, hbh⟩
          exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_union_left _ hb), hbt, hbh⟩) _ _ (T.reach w hw)
      rcases Finset.mem_union.mp hv with hv | hv
      · exact hT v hv
      · have hstep : Relation.ReflTransGen
            (fun x y => ∃ b ∈ insert a (T.arcs ∪ U.arcs), D.tail b = x ∧ D.head b = y)
            T.root U.root := Relation.ReflTransGen.single ⟨a, Finset.mem_insert_self _ _, ht, hh⟩
        exact hstep.trans (Relation.ReflTransGen.mono (by
          rintro x y ⟨b, hb, hbt, hbh⟩
          exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_union_right _ hb), hbt, hbh⟩) _ _ (U.reach v hv)) }
  exact ⟨R, rfl, rfl, rfl⟩

end BasicPackArb.Main.BPFresh

-- Complete module: BPProof.PackingLift

namespace BasicPackArb.Main.BPFresh
open Set

variable {V Arc S : Type*} [DecidableEq V] [DecidableEq Arc]

theorem packing_lift (D : Digraph V Arc) (π : S → V) (M : Matroid S)
    (hM : M.E = univ) (a : Arc) (ha : a ∈ D.arcs) (s : S)
    (hs : π s = D.tail a)
    (T : Option S → Arborescence (D.deleteArc a))
    (hT : IsBasicPacking (D.deleteArc a) (extendPlacement π (D.head a))
      (M.comap (collapse s)) T) :
    ∃ U : S → Arborescence D, IsBasicPacking D π M U := by
  classical
  have hverts : Disjoint (T (some s)).verts (T none).verts := by
    rw [Finset.disjoint_left]
    intro v hv hw
    have hi := (Matroid.comap_indep_iff.mp (hT.2.2 v).indep).2
    have he : (some s : Option S) = none := hi hv hw rfl
    cases he
  obtain ⟨R, hr, hv, he⟩ := join_trees D (restoreTree D a (T (some s)))
    (restoreTree D a (T none)) a ha
    (by simpa [restoreTree, hT.1] using hs.symm)
    (by simp [restoreTree, hT.1]) hverts
  let U : S → Arborescence D := fun z => if z = s then R else restoreTree D a (T (some z))
  have hroot : ∀ z, (U z).root = π z := by
    intro z
    by_cases hz : z = s
    · subst z
      simpa [U, restoreTree, hT.1] using hr
    · simp [U, hz, restoreTree, hT.1]
  have hnot (z : Option S) : a ∉ (T z).arcs := by
    intro hm
    exact (Finset.mem_erase.mp ((T z).arcs_subset hm)).1 rfl
  have hdis : ∀ z w : S, z ≠ w → Disjoint (U z).arcs (U w).arcs := by
    intro z w hzw
    by_cases hz : z = s
    · subst z
      have hw : w ≠ s := Ne.symm hzw
      simp only [U, ↓reduceIte, hw, restoreTree]
      rw [he]
      simp only [restoreTree, Finset.disjoint_insert_left, Finset.disjoint_union_left]
      exact ⟨hnot (some w), hT.2.1 _ _ (by simpa using hzw), hT.2.1 _ _ (by simp)⟩
    · by_cases hw : w = s
      · subst w
        apply Disjoint.symm
        simp only [U, ↓reduceIte, hz, restoreTree]
        rw [he]
        simp only [restoreTree, Finset.disjoint_insert_left, Finset.disjoint_union_left]
        exact ⟨hnot (some z), hT.2.1 _ _ (by simpa using Ne.symm hzw), hT.2.1 _ _ (by simp)⟩
      · simpa only [U, hz, hw, ↓reduceIte, restoreTree] using
          hT.2.1 (some z) (some w) (by simpa using hzw)
  refine ⟨U, hroot, hdis, ?_⟩
  intro v
  have hb := comap_base_image M hM s (hT.2.2 v)
  have himage : collapse s '' {z | v ∈ (T z).verts} = {z | v ∈ (U z).verts} := by
    ext z
    simp only [mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨q, hq, rfl⟩
      cases q with
      | none =>
        simp only [collapse_none, U, ↓reduceIte]
        rw [hv]
        exact Finset.mem_union_right _ hq
      | some q =>
        simp only [collapse_some, U]
        split_ifs with hqeq
        · subst q
          rw [hv]
          exact Finset.mem_union_left _ hq
        · exact hq
    · intro hz
      by_cases hzs : z = s
      · subst z
        simp only [U, ↓reduceIte] at hz
        rw [hv] at hz
        rcases Finset.mem_union.mp hz with hz | hz
        · exact ⟨some s, hz, rfl⟩
        · exact ⟨none, hz, rfl⟩
      · exact ⟨some z, by simpa only [U, hzs, ↓reduceIte, restoreTree] using hz, rfl⟩
  exact himage ▸ hb

end BasicPackArb.Main.BPFresh

-- Complete module: BPProof.PackingInduction

namespace BasicPackArb.Main.BPFresh
open Set

universe u v w

private theorem packing_induction {V : Type u} {Arc : Type v}
    [Fintype V] [DecidableEq V] (n : ℕ) :
    ∀ (S : Type w) [Fintype S] (D : Digraph V Arc), D.arcs.card = n →
      ∀ (π : S → V) (M : Matroid S), M.E = univ →
        MIndependent π M → MConnected D π M →
          ∃ T : S → Arborescence D, IsBasicPacking D π M T := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S _ D hcard π M hM hi hc
    by_cases hbad : ∃ a ∈ D.arcs, ¬ GoodArc D π M a
    · obtain ⟨a, ha, s, hs, hsn, hcut⟩ := exists_admissible_extension D π M hM hc hbad
      have hsmall : (D.deleteArc a).arcs.card < n := by
        rw [← hcard]
        exact Finset.card_erase_lt_of_mem ha
      have hi' := extend_independent π M hM hi s (D.head a) hsn
      have hc' : MConnected (D.deleteArc a) (extendPlacement π (D.head a))
          (M.comap (collapse s)) := by
        apply extend_connected D π M a s
        exact hcut
      obtain ⟨T, hT⟩ := ih (D.deleteArc a).arcs.card hsmall (Option S)
        (D.deleteArc a) rfl (extendPlacement π (D.head a)) (M.comap (collapse s))
        (comap_full_ground M hM s) hi' hc'
      exact packing_lift D π M hM a ha s hs T hT
    · have hg : ∀ a ∈ D.arcs, GoodArc D π M a := by
        intro a ha
        by_contra hn
        exact hbad ⟨a, ha, hn⟩
      exact no_bad_packing D π M hM hi hc hg

theorem packing_sufficiency {V : Type u} {Arc : Type v} {S : Type w}
    [Fintype V] [DecidableEq V] [Fintype S]
    (D : Digraph V Arc) (π : S → V) (M : Matroid S) (hM : M.E = univ)
    (hi : MIndependent π M) (hc : MConnected D π M) :
    ∃ T : S → Arborescence D, IsBasicPacking D π M T :=
  packing_induction D.arcs.card S D rfl π M hM hi hc

end BasicPackArb.Main.BPFresh

-- Complete module: BPProof.FinalRoot

namespace BasicPackArb.Main

/-- Theorem 1.6 (p. 3). Let `(D, S, π)` be a digraph with roots and `M` a matroid on `S`. There
exists an `M`-basic packing of arborescences in `(D, S, π)` if and only if `π` is `M`-independent
and `(D, S, π)` is `M`-connected. -/
theorem theorem_1_6 {V Arc S : Type*} [Fintype V] [DecidableEq V] [Fintype S]
    (D : Digraph V Arc) (π : S → V) (M : Matroid S) (hM : M.E = Set.univ) :
    (∃ T : S → Arborescence D, IsBasicPacking D π M T) ↔
      MIndependent π M ∧ MConnected D π M := by
  constructor
  · rintro ⟨T, hT⟩
    exact BPFresh.packing_necessity D π M hM T hT
  · rintro ⟨hi, hc⟩
    exact BPFresh.packing_sufficiency D π M hM hi hc

end BasicPackArb.Main

open BasicPackArb.Main

theorem solution {V Arc S : Type*} [Fintype V] [DecidableEq V] [Fintype S]
    (D : Digraph V Arc) (π : S → V) (M : Matroid S) (hM : M.E = Set.univ) :
    (∃ T : S → Arborescence D, IsBasicPacking D π M T) ↔
      MIndependent π M ∧ MConnected D π M := by
  exact theorem_1_6 D π M hM
