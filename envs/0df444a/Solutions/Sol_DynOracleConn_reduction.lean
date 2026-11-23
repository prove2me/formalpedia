-- Prove2me | solution 1 for DynOracleConn.reduction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T06:09:58.454828+00:00
-- url     : https://prove2.me/submissions/de746190-d37e-4b5f-a404-4ecbb67e6431
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DynOracleConn_Gadget
import Definitions.Def_DynOracleConn_Oracles
import Definitions.Def_DynOracleConn_DetAlg
import Theorems.Thm_DynOracleConn_gadget_isAcyclic
import Theorems.Thm_DynOracleConn_epoch_answer
import Theorems.Thm_DynOracleConn_probe_simulation

open DynOracleConn

namespace AuxReduction

/-! ### 1. Edge uniqueness and length of `gadgetEdges` -/

def symKey {d : ℕ} : GV d → GV d → Option (Fin 5 × Bool × ℕ)
  | .s, .l b j => some (0, b, j.val)
  | .l b j, .s => some (0, b, j.val)
  | .r b j, .l _ _ => some (1, b, j.val)
  | .l _ _, .r b j => some (1, b, j.val)
  | .u b i, .v _ _ => some (2, b, i.val)
  | .v _ _, .u b i => some (2, b, i.val)
  | .l b _, .u _ i => some (3, b, i.val)
  | .u _ i, .l b _ => some (3, b, i.val)
  | .v b i, .r _ _ => some (4, b, i.val)
  | .r _ _, .v b i => some (4, b, i.val)
  | _, _ => none

lemma symKey_symm {d : ℕ} (x y : GV d) : symKey x y = symKey y x := by
  cases x <;> cases y <;> rfl

def edgeKey {d : ℕ} : Sym2 (GV d) → Option (Fin 5 × Bool × ℕ) :=
  Sym2.lift ⟨symKey, symKey_symm⟩

@[simp] lemma edgeKey_mk {d : ℕ} (x y : GV d) : edgeKey s(x, y) = symKey x y := rfl

lemma nodup_flatMap_of_inj {α β : Type} {l : List α} {f : α → List β}
    (hl : l.Nodup) (hf : ∀ a ∈ l, (f a).Nodup)
    (hdisj : ∀ a₁ ∈ l, ∀ a₂ ∈ l, ∀ y ∈ f a₁, y ∈ f a₂ → a₁ = a₂) :
    (l.flatMap f).Nodup := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a l ih =>
      rw [List.nodup_cons] at hl
      rw [List.flatMap_cons, List.nodup_append]
      refine ⟨hf a List.mem_cons_self,
        ih hl.2 (fun x hx => hf x (List.mem_cons_of_mem a hx))
          (fun x₁ hx₁ x₂ hx₂ y hy₁ hy₂ =>
            hdisj x₁ (List.mem_cons_of_mem a hx₁) x₂ (List.mem_cons_of_mem a hx₂) y hy₁ hy₂),
        ?_⟩
      rintro y₁ hy₁ _ hy₂ rfl
      rw [List.mem_flatMap] at hy₂
      obtain ⟨a₂, ha₂, hya₂⟩ := hy₂
      have heq := hdisj a List.mem_cons_self a₂ (List.mem_cons_of_mem a ha₂) y₁ hy₁ hya₂
      exact hl.1 (heq ▸ ha₂)

lemma gadgetEdges_ne {d : ℕ} (X : PPHPInst d) :
    ∀ p ∈ gadgetEdges X, p.1 ≠ p.2 := by
  intro p hp
  simp only [gadgetEdges, fixedEdges, variableEdges, List.mem_append, List.mem_flatMap,
    List.mem_finRange, true_and] at hp
  rcases hp with ((hp1 | ⟨j, hp2⟩) | ⟨i, hp3⟩) | ⟨i, hp4⟩
  · split_ifs at hp1 with hd
    · simp only [List.mem_singleton] at hp1; subst hp1; intro h; nomatch h
    · nomatch hp1
  · split_ifs at hp2 with hj
    · rcases List.mem_cons.mp hp2 with rfl | hp2
      · intro h; nomatch h
      · rcases List.mem_cons.mp hp2 with rfl | hp2
        · intro h; nomatch h
        · nomatch hp2
    · nomatch hp2
  · rcases List.mem_cons.mp hp3 with rfl | hp3
    · intro h; nomatch h
    · rcases List.mem_cons.mp hp3 with rfl | hp3
      · intro h; nomatch h
      · nomatch hp3
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp4
    rcases hp4 with rfl | rfl | rfl | rfl <;> (intro h; nomatch h)

lemma gadgetEdges_sym2_nodup {d : ℕ} (X : PPHPInst d) :
    ((gadgetEdges X).map (fun p => (s(p.1, p.2) : Sym2 (GV d)))).Nodup := by
  apply List.Nodup.of_map edgeKey
  rw [List.map_map]
  let f : GV d × GV d → Option (Fin 5 × Bool × ℕ) := fun p => symKey p.1 p.2
  change ((gadgetEdges X).map f).Nodup
  unfold gadgetEdges fixedEdges variableEdges
  simp only [List.map_append, List.map_flatMap]
  set L1 := List.map f (if h : 0 < d then [(GV.s, GV.l false ⟨0, h⟩)] else [])
  set L2 := (List.finRange d).flatMap (fun j : Fin d =>
    List.map f (if h : j.val + 1 < d then
      [(GV.r false j, GV.l false ⟨j.val + 1, h⟩), (GV.r true j, GV.l true ⟨j.val + 1, h⟩)] else []))
  set L3 := (List.finRange d).flatMap (fun i : Fin d =>
    List.map f [(GV.u false i, GV.v false i), (GV.u true i, GV.v true i)])
  set L4 := (List.finRange d).flatMap (fun i : Fin d =>
    List.map f [(GV.l false (X.1 i), GV.u (xor false (X.2 (X.1 i))) i),
      (GV.l true (X.1 i), GV.u (xor true (X.2 (X.1 i))) i),
      (GV.v false i, GV.r false (X.1 i)),
      (GV.v true i, GV.r true (X.1 i))])
  have hL1_tag : ∀ z ∈ L1, ∃ b k, z = some (0, b, k) := by
    intro z hz; dsimp [L1, f, symKey] at hz
    split_ifs at hz with hd
    · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hz
      exact ⟨false, 0, hz⟩
    · simp at hz
  have hL2_tag : ∀ z ∈ L2, ∃ b k, z = some (1, b, k) := by
    intro z hz; dsimp [L2, f, symKey] at hz
    rw [List.mem_flatMap] at hz
    obtain ⟨j, _, hjz⟩ := hz
    split_ifs at hjz with hj
    · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hjz
      rcases hjz with rfl | rfl <;> exact ⟨_, j.val, rfl⟩
    · simp at hjz
  have hL3_tag : ∀ z ∈ L3, ∃ b k, z = some (2, b, k) := by
    intro z hz; dsimp [L3, f, symKey] at hz
    rw [List.mem_flatMap] at hz
    obtain ⟨i, _, hiz⟩ := hz
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hiz
    rcases hiz with rfl | rfl <;> exact ⟨_, i.val, rfl⟩
  have hL4_tag : ∀ z ∈ L4, ∃ c : Fin 5, (c = 3 ∨ c = 4) ∧ ∃ b k, z = some (c, b, k) := by
    intro z hz; dsimp [L4, f, symKey] at hz
    rw [List.mem_flatMap] at hz
    obtain ⟨i, _, hiz⟩ := hz
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hiz
    rcases hiz with rfl | rfl | rfl | rfl
    · exact ⟨3, Or.inl rfl, false, i.val, rfl⟩
    · exact ⟨3, Or.inl rfl, true, i.val, rfl⟩
    · exact ⟨4, Or.inr rfl, false, i.val, rfl⟩
    · exact ⟨4, Or.inr rfl, true, i.val, rfl⟩
  have hL1 : L1.Nodup := by
    dsimp [L1]; split_ifs <;> simp
  have hL2 : L2.Nodup := by
    apply nodup_flatMap_of_inj (List.nodup_finRange d)
    · intro j _; split_ifs <;> simp [f, symKey]
    · intro j₁ _ j₂ _ y hy₁ hy₂
      split_ifs at hy₁ with h1 <;> split_ifs at hy₂ with h2
      · simp [f, symKey] at hy₁ hy₂
        ext; rcases hy₁ with rfl | rfl <;> rcases hy₂ with h | h <;> simp at h <;> omega
      · simp at hy₂
      · simp at hy₁
      · simp at hy₁
  have hL3 : L3.Nodup := by
    apply nodup_flatMap_of_inj (List.nodup_finRange d)
    · intro i _; simp [f, symKey]
    · intro i₁ _ i₂ _ y hy₁ hy₂
      simp [f, symKey] at hy₁ hy₂
      ext; rcases hy₁ with rfl | rfl <;> rcases hy₂ with h | h <;> simp at h <;> omega
  have hL4 : L4.Nodup := by
    apply nodup_flatMap_of_inj (List.nodup_finRange d)
    · intro i _; simp [f, symKey]
    · intro i₁ _ i₂ _ y hy₁ hy₂
      simp [f, symKey] at hy₁ hy₂
      ext
      rcases hy₁ with rfl | rfl | rfl | rfl <;>
        rcases hy₂ with h | h | h | h <;> simp at h <;> omega
  rw [List.nodup_append]
  refine ⟨?_, hL4, ?_⟩
  · rw [List.nodup_append]
    refine ⟨?_, hL3, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hL1, hL2, ?_⟩
      rintro z₁ hz1 _ hz2 rfl
      obtain ⟨_, _, h1⟩ := hL1_tag z₁ hz1
      obtain ⟨_, _, h2⟩ := hL2_tag z₁ hz2
      rw [h1] at h2; simp at h2
    · rintro z₁ hz12 _ hz3 rfl
      obtain ⟨_, _, h3⟩ := hL3_tag z₁ hz3
      rcases List.mem_append.mp hz12 with hz1 | hz2
      · obtain ⟨_, _, h1⟩ := hL1_tag z₁ hz1; rw [h1] at h3; simp at h3
      · obtain ⟨_, _, h2⟩ := hL2_tag z₁ hz2; rw [h2] at h3; simp at h3
  · rintro z₁ hz123 _ hz4 rfl
    obtain ⟨c, hc, _, _, h4⟩ := hL4_tag z₁ hz4
    rcases List.mem_append.mp hz123 with (hz12 | hz3)
    · rcases List.mem_append.mp hz12 with hz1 | hz2
      · obtain ⟨_, _, h1⟩ := hL1_tag z₁ hz1; rw [h1] at h4; simp at h4; rcases h4 with ⟨rfl, _⟩; simp at hc
      · obtain ⟨_, _, h2⟩ := hL2_tag z₁ hz2; rw [h2] at h4; simp at h4; rcases h4 with ⟨rfl, _⟩; simp at hc
    · obtain ⟨_, _, h3⟩ := hL3_tag z₁ hz3; rw [h3] at h4; simp at h4; rcases h4 with ⟨rfl, _⟩; simp at hc

lemma gadgetEdges_length {d : ℕ} (X : PPHPInst d) :
    (gadgetEdges X).length = 8 * d - 1 := by
  unfold gadgetEdges fixedEdges variableEdges
  simp only [List.length_append, List.length_flatMap]
  cases d with
  | zero => simp
  | succ m =>
      have hpos : 0 < m + 1 := Nat.succ_pos m
      rw [dif_pos hpos, List.length_singleton]
      have hsum2 : ((List.finRange (m + 1)).map (fun _ : Fin (m + 1) => 2)).sum = 2 * (m + 1) := by
        simp [List.map_const']; ring
      have hsum4 : ((List.finRange (m + 1)).map (fun _ : Fin (m + 1) => 4)).sum = 4 * (m + 1) := by
        simp [List.map_const']; ring
      have hmid :
          ((List.finRange (m + 1)).map (fun j : Fin (m + 1) =>
            (if h : j.val + 1 < m + 1 then
              [(GV.r false j, GV.l false ⟨j.val + 1, h⟩), (GV.r true j, GV.l true ⟨j.val + 1, h⟩)]
            else []).length)).sum = 2 * m := by
        rw [List.finRange_succ_last, List.map_append, List.sum_append, List.map_map]
        have hcast : ∀ x : Fin m,
            (if h : (Fin.castSucc x).val + 1 < m + 1 then
              [(GV.r false (Fin.castSucc x), GV.l false ⟨(Fin.castSucc x).val + 1, h⟩),
               (GV.r true (Fin.castSucc x), GV.l true ⟨(Fin.castSucc x).val + 1, h⟩)]
            else []).length = 2 := by
          intro x
          have hx : (Fin.castSucc x).val + 1 < m + 1 := by simp
          rw [dif_pos hx]; rfl
        have hlast :
            (if h : (Fin.last m).val + 1 < m + 1 then
              [(GV.r false (Fin.last m), GV.l false ⟨(Fin.last m).val + 1, h⟩),
               (GV.r true (Fin.last m), GV.l true ⟨(Fin.last m).val + 1, h⟩)]
            else []).length = 0 := by
          have hx : ¬ ((Fin.last m).val + 1 < m + 1) := by simp [Fin.last]
          rw [dif_neg hx]; rfl
        have hmap_eq : List.map ((fun j : Fin (m + 1) =>
            (if h : j.val + 1 < m + 1 then
              [(GV.r false j, GV.l false ⟨j.val + 1, h⟩), (GV.r true j, GV.l true ⟨j.val + 1, h⟩)]
            else []).length) ∘ Fin.castSucc) (List.finRange m) =
            List.map (fun _ : Fin m => 2) (List.finRange m) := by
          apply List.map_congr_left
          intro x _; exact hcast x
        rw [hmap_eq]
        simp only [List.map_singleton, hlast, List.sum_singleton, add_zero]
        simp [List.map_const']; ring
      change 1 + _ + ((List.finRange (m + 1)).map (fun _ => 2)).sum +
          ((List.finRange (m + 1)).map (fun _ => 4)).sum = 8 * (m + 1) - 1
      rw [hmid, hsum2, hsum4]
      omega

/-! ### 2. Stream graph, validity, and acyclicity of `hardSeq` -/

lemma edge_eq_fromEdgeSet {n : ℕ} (a b : Fin n) :
    SimpleGraph.edge a b = SimpleGraph.fromEdgeSet {s(a, b)} := by
  ext x y
  simp [SimpleGraph.fromEdgeSet_adj, SimpleGraph.edge_adj, and_comm]

lemma isAcyclic_mono {n : ℕ} {G₁ G₂ : SimpleGraph (Fin n)} (hle : G₁ ≤ G₂)
    (hG₂ : G₂.IsAcyclic) : G₁.IsAcyclic := by
  intro v c hc
  exact hG₂ (c.map (SimpleGraph.Hom.ofLE hle)) (hc.map Function.injective_id)

lemma foldl_insert_edges {n d : ℕ} (e : GV d ↪ Fin n) :
    ∀ (ps : List (GV d × GV d)) (G₀ : SimpleGraph (Fin n)),
      (ps.map (fun p => ⟨e p.1, e p.2, true⟩ : GV d × GV d → PunctSketch.Update n)).foldl
        (fun G u => u.apply G) G₀ =
      G₀ ⊔ SimpleGraph.fromEdgeSet {x | ∃ p ∈ ps, x = s(e p.1, e p.2)}
  | [], G₀ => by simp
  | p :: ps, G₀ => by
      rw [List.map_cons, List.foldl_cons, foldl_insert_edges e ps]
      have hap : ({ u := e p.1, v := e p.2, insert := true } : PunctSketch.Update n).apply G₀ =
          G₀ ⊔ SimpleGraph.edge (e p.1) (e p.2) := rfl
      rw [hap, sup_assoc]
      congr 1
      ext x y
      simp only [SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj, SimpleGraph.edge_adj]
      constructor
      · rintro (⟨h1, hne⟩ | ⟨⟨q, hq, heq⟩, hne⟩)
        · exact ⟨⟨p, List.mem_cons_self, Sym2.eq_iff.mpr h1⟩, hne⟩
        · exact ⟨⟨q, List.mem_cons_of_mem p hq, heq⟩, hne⟩
      · rintro ⟨⟨q, hq, heq⟩, hne⟩
        rcases List.mem_cons.mp hq with rfl | hq
        · exact Or.inl ⟨Sym2.eq_iff.mp heq, hne⟩
        · exact Or.inr ⟨⟨q, hq, heq⟩, hne⟩

def initSeq {n d : ℕ} (e : GV d ↪ Fin n) (X : PPHPInst d) : List (PunctSketch.Update n) :=
  (gadgetEdges X).map (fun p => ⟨e p.1, e p.2, true⟩)

def epochUpdates {n d : ℕ} (e : GV d ↪ Fin n) (ℐ : List (Fin d)) : List (PunctSketch.Update n) :=
  ℐ.flatMap (fun i => [⟨e GV.t, e (GV.v false i), true⟩, ⟨e GV.t, e (GV.v false i), false⟩])

lemma streamGraph_initSeq {n d : ℕ} (e : GV d ↪ Fin n) (X : PPHPInst d) :
    PunctSketch.streamGraph (initSeq e X) = gadget e X := by
  unfold PunctSketch.streamGraph initSeq gadget
  rw [foldl_insert_edges, bot_sup_eq]

lemma streamGraph_initSeq_take_le {n d : ℕ} (e : GV d ↪ Fin n) (X : PPHPInst d) (k : ℕ) :
    PunctSketch.streamGraph ((initSeq e X).take k) ≤ gadget e X := by
  unfold PunctSketch.streamGraph initSeq gadget
  rw [← List.map_take, foldl_insert_edges, bot_sup_eq]
  intro x y hadj
  simp only [SimpleGraph.fromEdgeSet_adj] at hadj ⊢
  obtain ⟨⟨p, hp, heq⟩, hne⟩ := hadj
  exact ⟨⟨p, List.mem_of_mem_take hp, heq⟩, hne⟩

lemma isValidStream_initSeq {n d : ℕ} (e : GV d ↪ Fin n) (X : PPHPInst d) :
    PunctSketch.IsValidStream (initSeq e X) := by
  intro idx hidx
  have hlen : (initSeq e X).length = (gadgetEdges X).length := List.length_map _
  have hidx' : idx < (gadgetEdges X).length := hlen ▸ hidx
  have hget : (initSeq e X)[idx] = ⟨e (gadgetEdges X)[idx].1, e (gadgetEdges X)[idx].2, true⟩ := by
    simp [initSeq]
  rw [hget]
  dsimp only
  have hp_mem : (gadgetEdges X)[idx] ∈ gadgetEdges X := List.getElem_mem hidx'
  have hne_gv : (gadgetEdges X)[idx].1 ≠ (gadgetEdges X)[idx].2 := gadgetEdges_ne X _ hp_mem
  have hne : e (gadgetEdges X)[idx].1 ≠ e (gadgetEdges X)[idx].2 :=
    fun h => hne_gv (e.injective h)
  refine ⟨hne, fun _ hadj => ?_, fun h => nomatch h⟩
  unfold PunctSketch.streamGraph initSeq at hadj
  rw [← List.map_take, foldl_insert_edges, bot_sup_eq, SimpleGraph.fromEdgeSet_adj] at hadj
  obtain ⟨⟨q, hq_take, hsym⟩, _⟩ := hadj
  rw [List.mem_iff_getElem] at hq_take
  obtain ⟨j, hj, hq_eq⟩ := hq_take
  have hj_lt : j < idx := by
    simp only [List.length_take] at hj
    omega
  have hj_lt' : j < (gadgetEdges X).length := lt_trans hj_lt hidx'
  have hq_get : ((gadgetEdges X).take idx)[j] = (gadgetEdges X)[j] := List.getElem_take
  rw [hq_get] at hq_eq
  have hsym_gv : (s((gadgetEdges X)[j].1, (gadgetEdges X)[j].2) : Sym2 (GV d)) =
      s((gadgetEdges X)[idx].1, (gadgetEdges X)[idx].2) := by
    rw [hq_eq]
    simp only [Sym2.eq_iff, Function.Embedding.apply_eq_iff_eq] at hsym ⊢
    tauto
  have hnodup := gadgetEdges_sym2_nodup X
  rw [List.nodup_iff_injective_get] at hnodup
  have hinj := @hnodup ⟨j, by simp [hj_lt']⟩ ⟨idx, by simp [hidx']⟩ (by simp [hsym_gv])
  simp only [Fin.mk.injEq] at hinj
  omega

lemma ins_apply_gadget {n d : ℕ} (e : GV d ↪ Fin n) (X : PPHPInst d) (i : Fin d) :
    (⟨e GV.t, e (GV.v false i), true⟩ : PunctSketch.Update n).apply (gadget e X) = withT e X i := by
  simp only [PunctSketch.Update.apply, ↓reduceIte, withT, edge_eq_fromEdgeSet]

lemma del_apply_withT {n d : ℕ} (e : GV d ↪ Fin n) (X : PPHPInst d) (i : Fin d) :
    (⟨e GV.t, e (GV.v false i), false⟩ : PunctSketch.Update n).apply (withT e X i) = gadget e X := by
  have ht_iso := (DynOracleConn.gadget_isAcyclic e X).2.2.1
  simp only [PunctSketch.Update.apply, Bool.false_eq_true, ↓reduceIte, withT, edge_eq_fromEdgeSet]
  ext x y
  simp only [SimpleGraph.sdiff_adj, SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj,
    Set.mem_singleton_iff, Sym2.eq_iff]
  constructor
  · rintro ⟨hg | h1, hnot⟩
    · exact hg
    · exact False.elim (hnot h1)
  · intro hg
    refine ⟨Or.inl hg, ?_⟩
    rintro ⟨⟨rfl, _⟩ | ⟨_, rfl⟩, _⟩
    · exact ht_iso y hg
    · exact ht_iso x hg.symm

lemma epochUpdates_length {n d : ℕ} (e : GV d ↪ Fin n) (ℐ : List (Fin d)) :
    (epochUpdates e ℐ).length = 2 * ℐ.length := by
  induction ℐ with
  | nil => rfl
  | cons i rest ih =>
      simp only [epochUpdates, List.flatMap_cons, List.length_append, List.length_cons,
        List.length_nil] at ih ⊢
      omega

lemma epochUpdates_prefix {n d : ℕ} (e : GV d ↪ Fin n) (X : PPHPInst d) :
    ∀ (ℐ : List (Fin d)) (j : ℕ), j ≤ (epochUpdates e ℐ).length →
      let G := ((epochUpdates e ℐ).take j).foldl (fun G u => u.apply G) (gadget e X)
      G.IsAcyclic ∧
        (j % 2 = 0 → G = gadget e X) ∧
        (∀ m (hm : m < ℐ.length), j = 2 * m + 1 → G = withT e X ℐ[m]) ∧
        (∀ (hj : j < (epochUpdates e ℐ).length),
          (epochUpdates e ℐ)[j].u ≠ (epochUpdates e ℐ)[j].v ∧
          ((epochUpdates e ℐ)[j].insert = true → ¬ G.Adj (epochUpdates e ℐ)[j].u (epochUpdates e ℐ)[j].v) ∧
          ((epochUpdates e ℐ)[j].insert = false → G.Adj (epochUpdates e ℐ)[j].u (epochUpdates e ℐ)[j].v))
  | [], j, hj => by
      have hj0 : j = 0 := by simp [epochUpdates] at hj; omega
      subst hj0
      refine ⟨(DynOracleConn.gadget_isAcyclic e X).2.1, fun _ => rfl, ?_, ?_⟩
      · intro m hm; simp at hm
      · intro hj; simp [epochUpdates] at hj
  | i :: rest, 0, _ => by
      have htake : (epochUpdates e (i :: rest)).take 0 = [] := rfl
      dsimp only
      rw [htake]
      dsimp only [List.foldl_nil]
      refine ⟨(DynOracleConn.gadget_isAcyclic e X).2.1, fun _ => rfl, ?_, ?_⟩
      · intro m _ hm; omega
      · intro _
        have hget : (epochUpdates e (i :: rest))[0] = ⟨e GV.t, e (GV.v false i), true⟩ := rfl
        rw [hget]
        have hne : e GV.t ≠ e (GV.v false i) := fun h => by have := e.injective h; cases this
        refine ⟨hne, ?_, ?_⟩
        · intro _; exact (DynOracleConn.gadget_isAcyclic e X).2.2.1 _
        · intro h; dsimp at h; exact Bool.noConfusion h
  | i :: rest, 1, _ => by
      have htake : (epochUpdates e (i :: rest)).take 1 = [⟨e GV.t, e (GV.v false i), true⟩] := rfl
      dsimp only
      rw [htake]
      simp only [List.foldl_cons, List.foldl_nil, ins_apply_gadget]
      refine ⟨(DynOracleConn.gadget_isAcyclic e X).2.2.2.2.2 i, fun h => by omega, ?_, ?_⟩
      · intro m hm hjm
        have hm0 : m = 0 := by omega
        subst hm0; rfl
      · intro _
        have hget : (epochUpdates e (i :: rest))[1] = ⟨e GV.t, e (GV.v false i), false⟩ := rfl
        rw [hget]
        have hne : e GV.t ≠ e (GV.v false i) := fun h => by have := e.injective h; cases this
        have hadj : (withT e X i).Adj (e GV.t) (e (GV.v false i)) := by
          simp [withT, SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj, hne]
        refine ⟨hne, ?_, ?_⟩
        · intro h; dsimp at h; exact Bool.noConfusion h
        · intro _; exact hadj
  | i :: rest, j + 2, hj => by
      have hlen_cons : (epochUpdates e (i :: rest)).length = 2 + (epochUpdates e rest).length := by
        simp only [epochUpdates, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil]
      have hj' : j ≤ (epochUpdates e rest).length := by omega
      have htake : (epochUpdates e (i :: rest)).take (j + 2) =
          ⟨e GV.t, e (GV.v false i), true⟩ :: ⟨e GV.t, e (GV.v false i), false⟩ ::
            (epochUpdates e rest).take j := rfl
      rw [htake]
      simp only [List.foldl_cons, ins_apply_gadget, del_apply_withT]
      obtain ⟨hacyc, heven, hodd, hval⟩ := epochUpdates_prefix e X rest j hj'
      refine ⟨hacyc, fun hmod => heven (by omega), ?_, ?_⟩
      · intro m hm hjm
        cases m with
        | zero => omega
        | succ m' =>
            have hm' : m' < rest.length := by simp at hm; omega
            exact hodd m' hm' (by omega)
      · intro hj_lt
        have hj_lt' : j < (epochUpdates e rest).length := by omega
        have hget : (epochUpdates e (i :: rest))[j + 2] = (epochUpdates e rest)[j] := rfl
        rw [hget]
        exact hval hj_lt'

lemma take_add_len {α : Type} (l₁ l₂ : List α) (j : ℕ) :
    (l₁ ++ l₂).take (l₁.length + j) = l₁ ++ l₂.take j := by
  rw [List.take_append]
  have h1 : l₁.take (l₁.length + j) = l₁ := List.take_of_length_le (by omega)
  have h2 : l₁.length + j - l₁.length = j := by omega
  rw [h1, h2]

lemma hardSeq_props {n d : ℕ} (e : GV d ↪ Fin n) (X : PPHPInst d) (ℐ : List (Fin d)) :
    PunctSketch.IsValidStream (hardSeq e X ℐ) ∧
    ForestThroughout (hardSeq e X ℐ) ∧
    (hardSeq e X ℐ).length = 8 * d - 1 + 2 * ℐ.length := by
  have hdef : hardSeq e X ℐ = initSeq e X ++ epochUpdates e ℐ := rfl
  have hinit_len : (initSeq e X).length = 8 * d - 1 := by
    simp [initSeq, gadgetEdges_length]
  have hepoch_len : (epochUpdates e ℐ).length = 2 * ℐ.length := epochUpdates_length e ℐ
  have htot_len : (hardSeq e X ℐ).length = 8 * d - 1 + 2 * ℐ.length := by
    rw [hdef, List.length_append, hinit_len, hepoch_len]
  refine ⟨?_, ?_, htot_len⟩
  · change PunctSketch.IsValidStream (initSeq e X ++ epochUpdates e ℐ)
    intro idx hidx
    by_cases hlt : idx < (initSeq e X).length
    · have hget : (initSeq e X ++ epochUpdates e ℐ)[idx] = (initSeq e X)[idx] :=
        List.getElem_append_left hlt
      have htake : (initSeq e X ++ epochUpdates e ℐ).take idx = (initSeq e X).take idx :=
        List.take_append_of_le_length hlt.le
      rw [hget, htake]
      exact isValidStream_initSeq e X idx hlt
    · push Not at hlt
      let j := idx - (initSeq e X).length
      have hj_lt : j < (epochUpdates e ℐ).length := by
        rw [List.length_append] at hidx; omega
      have hget : (initSeq e X ++ epochUpdates e ℐ)[idx] = (epochUpdates e ℐ)[j] :=
        List.getElem_append_right hlt
      have htake : (initSeq e X ++ epochUpdates e ℐ).take idx =
          initSeq e X ++ (epochUpdates e ℐ).take j := by
        have hidx_eq : idx = (initSeq e X).length + j := by omega
        rw [hidx_eq, take_add_len]
      have hsg : PunctSketch.streamGraph (initSeq e X ++ (epochUpdates e ℐ).take j) =
          ((epochUpdates e ℐ).take j).foldl (fun G u => u.apply G) (gadget e X) := by
        unfold PunctSketch.streamGraph
        rw [List.foldl_append]
        exact congrArg (fun G₀ => ((epochUpdates e ℐ).take j).foldl _ G₀) (streamGraph_initSeq e X)
      rw [hget, htake, hsg]
      exact (epochUpdates_prefix e X ℐ j hj_lt.le).2.2.2 hj_lt
  · intro k hk
    unfold graphAfter
    rw [hdef] at hk ⊢
    by_cases hlt : k ≤ (initSeq e X).length
    · rw [List.take_append_of_le_length hlt]
      exact isAcyclic_mono (streamGraph_initSeq_take_le e X k)
        (DynOracleConn.gadget_isAcyclic e X).2.1
    · push Not at hlt
      let j := k - (initSeq e X).length
      have hj_le : j ≤ (epochUpdates e ℐ).length := by
        rw [List.length_append] at hk; omega
      have hk_eq : k = (initSeq e X).length + j := by omega
      rw [hk_eq, take_add_len]
      unfold PunctSketch.streamGraph
      rw [List.foldl_append]
      have hsg : (initSeq e X).foldl (fun G u => u.apply G) ⊥ = gadget e X :=
        streamGraph_initSeq e X
      rw [hsg]
      exact (epochUpdates_prefix e X ℐ j hj_le).1

lemma graphAfter_epoch_after_ins {n d : ℕ} (e : GV d ↪ Fin n) (X : PPHPInst d)
    (ℐ : List (Fin d)) (m : ℕ) (hm : m < ℐ.length) :
    graphAfter (hardSeq e X ℐ) (8 * d - 1 + 2 * m + 1) = withT e X ℐ[m] := by
  unfold graphAfter
  have hdef : hardSeq e X ℐ = initSeq e X ++ epochUpdates e ℐ := rfl
  have hinit_len : (initSeq e X).length = 8 * d - 1 := by simp [initSeq, gadgetEdges_length]
  rw [hdef, ← hinit_len, Nat.add_assoc, take_add_len]
  unfold PunctSketch.streamGraph
  rw [List.foldl_append]
  have hsg : (initSeq e X).foldl (fun G u => u.apply G) ⊥ = gadget e X :=
    streamGraph_initSeq e X
  rw [hsg]
  have hj_le : 2 * m + 1 ≤ (epochUpdates e ℐ).length := by
    rw [epochUpdates_length]; omega
  exact (epochUpdates_prefix e X ℐ (2 * m + 1) hj_le).2.2.1 m hm rfl

/-! ### 3. Algorithmic simulation `red` and transcript factorization `F` -/

noncomputable def simOpt {n d : ℕ} (e : GV d ↪ Fin n) (optI : Option (Fin d))
    (q : Fin n × Fin n) : Option (Fin d × Fin d) :=
  Classical.choose (DynOracleConn.probe_simulation e optI q.1 q.2)

noncomputable def simDec {n d : ℕ} (e : GV d ↪ Fin n) (optI : Option (Fin d))
    (q : Fin n × Fin n) : Option (Option Bool) → Bool :=
  Classical.choose (Classical.choose_spec (DynOracleConn.probe_simulation e optI q.1 q.2))

lemma sim_spec {n d : ℕ} (e : GV d ↪ Fin n) (optI : Option (Fin d))
    (q : Fin n × Fin n) (X : PPHPInst d) :
    simDec e optI q ((simOpt e optI q).map (pOracle X)) =
      matrixOracle (epochGraph e X optI) q := by
  have h := Classical.choose_spec
    (Classical.choose_spec (DynOracleConn.probe_simulation e optI q.1 q.2)) X
  apply Bool.eq_iff_iff.mpr
  unfold simDec simOpt
  rw [← h]
  simp [matrixOracle]

noncomputable def transTree {n d : ℕ} {R : Type} (e : GV d ↪ Fin n) (optI : Option (Fin d)) :
    ProbeTree (Fin n × Fin n) Bool R → PPHPTree d R
  | .done r => .done r
  | .probe q k =>
      match simOpt e optI q with
      | none => transTree e optI (k (simDec e optI q none))
      | some pq => .probe pq (fun ans => transTree e optI (k (simDec e optI q (some ans))))

lemma transTree_run {n d : ℕ} {R : Type} (e : GV d ↪ Fin n) (optI : Option (Fin d))
    (t : ProbeTree (Fin n × Fin n) Bool R) (X : PPHPInst d) :
    (transTree e optI t).run (pOracle X) = t.run (matrixOracle (epochGraph e X optI)) := by
  induction t with
  | done r => rfl
  | probe q k ih =>
      unfold transTree
      have hspec := sim_spec e optI q X
      cases hopt : simOpt e optI q with
      | none =>
          simp only [hopt, Option.map_none] at hspec ⊢
          rw [ih, hspec]; rfl
      | some pq =>
          simp only [hopt, Option.map_some, ProbeTree.run] at hspec ⊢
          rw [ih, hspec]

lemma transTree_transcript {n d : ℕ} {R : Type} (e : GV d ↪ Fin n) (optI : Option (Fin d))
    (t : ProbeTree (Fin n × Fin n) Bool R) (X : PPHPInst d) :
    (transTree e optI t).transcript (pOracle X) =
      (t.transcript (matrixOracle (epochGraph e X optI))).filterMap
        (fun p => (simOpt e optI p.1).map (fun pq => (pq, pOracle X pq))) := by
  induction t with
  | done r => rfl
  | probe q k ih =>
      unfold transTree
      have hspec := sim_spec e optI q X
      cases hopt : simOpt e optI q with
      | none =>
          simp only [hopt, Option.map_none, ProbeTree.transcript, List.filterMap_cons] at hspec ⊢
          rw [ih, hspec]
      | some pq =>
          simp only [hopt, Option.map_some, ProbeTree.transcript, List.filterMap_cons] at hspec ⊢
          rw [ih, hspec]

def bindTree {Q Ans R₁ R₂ : Type} :
    ProbeTree Q Ans R₁ → (R₁ → ProbeTree Q Ans R₂) → ProbeTree Q Ans R₂
  | .done r₁, k₂ => k₂ r₁
  | .probe q k₁, k₂ => .probe q (fun a => bindTree (k₁ a) k₂)

lemma bindTree_run {Q Ans R₁ R₂ : Type} (t₁ : ProbeTree Q Ans R₁)
    (k₂ : R₁ → ProbeTree Q Ans R₂) (O : Q → Ans) :
    (bindTree t₁ k₂).run O = (k₂ (t₁.run O)).run O := by
  induction t₁ with
  | done r₁ => rfl
  | probe q k₁ ih => exact ih (O q)

lemma bindTree_transcript {Q Ans R₁ R₂ : Type} (t₁ : ProbeTree Q Ans R₁)
    (k₂ : R₁ → ProbeTree Q Ans R₂) (O : Q → Ans) :
    (bindTree t₁ k₂).transcript O = t₁.transcript O ++ (k₂ (t₁.run O)).transcript O := by
  induction t₁ with
  | done r₁ => rfl
  | probe q k₁ ih =>
      simp only [bindTree, ProbeTree.transcript, ProbeTree.run, List.cons_append]
      rw [ih (O q)]

noncomputable def stateAfter {n : ℕ} {Q Ans S : Type} (A : DetAlg n Q Ans S)
    (O : SimpleGraph (Fin n) → Q → Ans) :
    ℕ → S → SimpleGraph (Fin n) → List (PunctSketch.Update n) → S
  | _, st, _, [] => st
  | k, st, G, u :: rest =>
      stateAfter A O (k + 1) ((A.step k st u).run (O G)).1 (u.apply G) rest

lemma runFrom_append {n : ℕ} {Q Ans S : Type} (A : DetAlg n Q Ans S)
    (O : SimpleGraph (Fin n) → Q → Ans) :
    ∀ (k : ℕ) (st : S) (G : SimpleGraph (Fin n)) (σ₁ σ₂ : List (PunctSketch.Update n)),
      A.runFrom O k st G (σ₁ ++ σ₂) =
        A.runFrom O k st G σ₁ ++
          A.runFrom O (k + σ₁.length) (stateAfter A O k st G σ₁)
            (σ₁.foldl (fun G' u => u.apply G') G) σ₂
  | k, st, G, [], σ₂ => by simp [DetAlg.runFrom, stateAfter]
  | k, st, G, u :: σ₁, σ₂ => by
      simp only [List.cons_append, DetAlg.runFrom, stateAfter, List.length_cons, List.foldl_cons]
      rw [runFrom_append A O (k + 1) _ (u.apply G) σ₁ σ₂]
      have hk : k + 1 + σ₁.length = k + (σ₁.length + 1) := by omega
      rw [hk]

noncomputable def redAlg {n d : ℕ} {S : Type} (e : GV d ↪ Fin n)
    (A : DetAlg n (Fin n × Fin n) Bool S) : PPHPAlg d S where
  pre X := stateAfter A matrixOracle 0 A.init ⊥ (initSeq e X)
  step m st i :=
    let k₀ := 8 * d - 1 + 2 * m
    let u_ins : PunctSketch.Update n := ⟨e GV.t, e (GV.v false i), true⟩
    let u_del : PunctSketch.Update n := ⟨e GV.t, e (GV.v false i), false⟩
    bindTree (transTree e none (A.step k₀ st u_ins)) (fun p₁ =>
      bindTree (transTree e (some i) (A.step (k₀ + 1) p₁.1 u_del)) (fun p₂ =>
        .done (p₂.1, !p₁.2)))

noncomputable def decodeEpochs {n d : ℕ} (e : GV d ↪ Fin n) (X : PPHPInst d) :
    List (Fin d) → List (List ((Fin n × Fin n) × Bool) × Bool) →
    List (List ((Fin d × Fin d) × Option Bool) × Bool)
  | i :: rest, (qs₁, ans₁) :: (qs₂, _) :: trRest =>
      (qs₁.filterMap (fun p => (simOpt e none p.1).map (fun pq => (pq, pOracle X pq))) ++
       qs₂.filterMap (fun p => (simOpt e (some i) p.1).map (fun pq => (pq, pOracle X pq))),
       !ans₁) :: decodeEpochs e X rest trRest
  | _, _ => []

noncomputable def F_map {n d : ℕ} (e : GV d ↪ Fin n) (X : PPHPInst d) (ℐ : List (Fin d))
    (tr : List (List ((Fin n × Fin n) × Bool) × Bool)) :
    List (List ((Fin d × Fin d) × Option Bool) × Bool) :=
  decodeEpochs e X ℐ (tr.drop (8 * d - 1))

lemma runFrom_redAlg {n d : ℕ} {S : Type} (e : GV d ↪ Fin n)
    (A : DetAlg n (Fin n × Fin n) Bool S) (X : PPHPInst d) :
    ∀ (m : ℕ) (st : S) (rest : List (Fin d)),
      (redAlg e A).runFrom X m st rest =
        decodeEpochs e X rest
          (A.runFrom matrixOracle (8 * d - 1 + 2 * m) st (gadget e X) (epochUpdates e rest))
  | _, _, [] => rfl
  | m, st, i :: rest => by
      have heu : epochUpdates e (i :: rest) =
          ⟨e GV.t, e (GV.v false i), true⟩ :: ⟨e GV.t, e (GV.v false i), false⟩ ::
            epochUpdates e rest := rfl
      rw [heu]
      unfold PPHPAlg.runFrom
      conv_rhs =>
        rw [DetAlg.runFrom, ins_apply_gadget, DetAlg.runFrom, del_apply_withT]
      dsimp only [redAlg]
      simp only [bindTree_transcript, bindTree_run, transTree_transcript, transTree_run,
        epochGraph, ProbeTree.transcript, ProbeTree.run, List.append_nil, decodeEpochs]
      congr 1
      have hk : 8 * d - 1 + 2 * m + 1 + 1 = 8 * d - 1 + 2 * (m + 1) := by omega
      rw [hk]
      exact runFrom_redAlg e A X (m + 1) _ rest

lemma runFrom_length {n : ℕ} {Q Ans S : Type} (A : DetAlg n Q Ans S)
    (O : SimpleGraph (Fin n) → Q → Ans) :
    ∀ (k : ℕ) (st : S) (G : SimpleGraph (Fin n)) (rest : List (PunctSketch.Update n)),
      (A.runFrom O k st G rest).length = rest.length
  | _, _, _, [] => rfl
  | k, st, G, u :: rest => by
      simp [DetAlg.runFrom, runFrom_length A O (k + 1) _ (u.apply G) rest]

lemma decodeEpochs_cost_le {n d : ℕ} (e : GV d ↪ Fin n) (X : PPHPInst d) :
    ∀ (ℐ : List (Fin d)) (tr : List (List ((Fin n × Fin n) × Bool) × Bool)),
      ((decodeEpochs e X ℐ tr).map (fun p => p.1.length)).sum ≤
        (tr.map (fun p => p.1.length)).sum
  | i :: rest, (qs₁, ans₁) :: (qs₂, ans₂) :: trRest => by
      simp only [decodeEpochs, List.map_cons, List.sum_cons, List.length_append]
      have h1 : (qs₁.filterMap (fun p => (simOpt e none p.1).map (fun pq => (pq, pOracle X pq)))).length ≤
          qs₁.length := List.length_filterMap_le _ _
      have h2 : (qs₂.filterMap (fun p => (simOpt e (some i) p.1).map (fun pq => (pq, pOracle X pq)))).length ≤
          qs₂.length := List.length_filterMap_le _ _
      have h3 := decodeEpochs_cost_le e X rest trRest
      omega
  | [], _ => by simp [decodeEpochs]
  | _ :: _, [] => by simp [decodeEpochs]
  | _ :: _, [_] => by simp [decodeEpochs]

lemma decodeEpochs_outputs {n d : ℕ} (e : GV d ↪ Fin n) (X : PPHPInst d) :
    ∀ (ℐ : List (Fin d)) (tr : List (List ((Fin n × Fin n) × Bool) × Bool)),
      tr.length = 2 * ℐ.length →
      ((decodeEpochs e X ℐ tr).map Prod.snd).length = ℐ.length ∧
      ∀ m (_hm : m < ℐ.length),
        ((decodeEpochs e X ℐ tr).map Prod.snd)[m]? =
          (tr.map Prod.snd)[2 * m]?.map (fun b => !b)
  | [], [], _ => ⟨rfl, fun _ hm => by simp at hm⟩
  | i :: rest, (qs₁, ans₁) :: (qs₂, ans₂) :: trRest, hlen => by
      have hlen' : trRest.length = 2 * rest.length := by simp at hlen; omega
      obtain ⟨hl, hget⟩ := decodeEpochs_outputs e X rest trRest hlen'
      refine ⟨by simp [decodeEpochs, hl], ?_⟩
      intro m hm
      cases m with
      | zero => simp [decodeEpochs]
      | succ m' =>
          have hm' : m' < rest.length := by simp at hm; omega
          simp only [decodeEpochs, List.map_cons]
          have h1 : ((!ans₁) :: List.map Prod.snd (decodeEpochs e X rest trRest))[m' + 1]? =
              (List.map Prod.snd (decodeEpochs e X rest trRest))[m']? := rfl
          have h2 : (ans₁ :: ans₂ :: List.map Prod.snd trRest)[2 * (m' + 1)]? =
              (List.map Prod.snd trRest)[2 * m']? := by
            have : 2 * (m' + 1) = (2 * m') + 2 := by omega
            rw [this]; rfl
          rw [h1, h2, hget m' hm']
  | _ :: _, [], hlen => by simp at hlen
  | _ :: _, [_], hlen => by simp at hlen; omega

end AuxReduction

theorem solution {n d : ℕ} {S : Type} (e : GV d ↪ Fin n) :
    ∃ red : DetAlg n (Fin n × Fin n) Bool S → PPHPAlg d S,
      ∀ (X : PPHPInst d) (ℐ : List (Fin d)),
        PunctSketch.IsValidStream (hardSeq e X ℐ) ∧ ForestThroughout (hardSeq e X ℐ) ∧
        (hardSeq e X ℐ).length = 8 * d - 1 + 2 * ℐ.length ∧
        ∃ F : List (List ((Fin n × Fin n) × Bool) × Bool) →
            List (List ((Fin d × Fin d) × Option Bool) × Bool),
          ∀ A : DetAlg n (Fin n × Fin n) Bool S,
            (red A).transcript X ℐ = F (A.transcript matrixOracle (hardSeq e X ℐ)) ∧
            (A.AllCorrect matrixOracle (e GV.s) (e GV.t) (hardSeq e X ℐ) →
              (red A).correctTotal X ℐ) ∧
            (red A).Ltotal X ℐ ≤ A.totalCost matrixOracle (hardSeq e X ℐ) := by
  refine ⟨AuxReduction.redAlg e, fun X ℐ => ?_⟩
  obtain ⟨hValid, hForest, hLen⟩ := AuxReduction.hardSeq_props e X ℐ
  refine ⟨hValid, hForest, hLen, AuxReduction.F_map e X ℐ, fun A => ?_⟩
  have hdef : hardSeq e X ℐ = AuxReduction.initSeq e X ++ AuxReduction.epochUpdates e ℐ := rfl
  have hinit_len : (AuxReduction.initSeq e X).length = 8 * d - 1 := by
    simp [AuxReduction.initSeq, AuxReduction.gadgetEdges_length]
  have htr_split :
      A.transcript matrixOracle (hardSeq e X ℐ) =
        A.runFrom matrixOracle 0 A.init ⊥ (AuxReduction.initSeq e X) ++
          A.runFrom matrixOracle (8 * d - 1) (AuxReduction.stateAfter A matrixOracle 0 A.init ⊥ (AuxReduction.initSeq e X))
            (gadget e X) (AuxReduction.epochUpdates e ℐ) := by
    unfold DetAlg.transcript
    rw [hdef, AuxReduction.runFrom_append, hinit_len, zero_add]
    congr 2
    exact AuxReduction.streamGraph_initSeq e X
  have hdrop :
      (A.transcript matrixOracle (hardSeq e X ℐ)).drop (8 * d - 1) =
        A.runFrom matrixOracle (8 * d - 1) ((AuxReduction.redAlg e A).pre X)
          (gadget e X) (AuxReduction.epochUpdates e ℐ) := by
    rw [htr_split]
    have hpre_len : (A.runFrom matrixOracle 0 A.init ⊥ (AuxReduction.initSeq e X)).length = 8 * d - 1 := by
      rw [AuxReduction.runFrom_length, hinit_len]
    rw [← hpre_len, List.drop_left]
    rfl
  have htr_eq :
      (AuxReduction.redAlg e A).transcript X ℐ =
        AuxReduction.F_map e X ℐ (A.transcript matrixOracle (hardSeq e X ℐ)) := by
    unfold PPHPAlg.transcript AuxReduction.F_map
    rw [hdrop]
    simpa using AuxReduction.runFrom_redAlg e A X 0 ((AuxReduction.redAlg e A).pre X) ℐ
  refine ⟨htr_eq, ?_, ?_⟩
  · intro hAll
    unfold PPHPAlg.correctTotal
    rw [htr_eq]
    unfold AuxReduction.F_map
    let trEpoch := (A.transcript matrixOracle (hardSeq e X ℐ)).drop (8 * d - 1)
    have htrEpoch_len : trEpoch.length = 2 * ℐ.length := by
      dsimp [trEpoch]
      rw [hdrop, AuxReduction.runFrom_length, AuxReduction.epochUpdates_length]
    obtain ⟨hout_len, hout_get⟩ := AuxReduction.decodeEpochs_outputs e X ℐ trEpoch htrEpoch_len
    apply List.ext_getElem
    · rw [hout_len, List.length_map]
    · intro m hm1 hm2
      have hm : m < ℐ.length := by simpa using hm2
      have hopt := hout_get m hm
      rw [List.getElem?_eq_getElem hm1] at hopt
      have hk_lt : 8 * d - 1 + 2 * m < (hardSeq e X ℐ).length := by omega
      have hans_len : (A.answers matrixOracle (hardSeq e X ℐ)).length = (hardSeq e X ℐ).length := by
        unfold DetAlg.answers DetAlg.transcript
        rw [List.length_map, AuxReduction.runFrom_length]
      have hans_drop :
          (trEpoch.map Prod.snd)[2 * m]? = (A.answers matrixOracle (hardSeq e X ℐ))[8 * d - 1 + 2 * m]? := by
        dsimp [trEpoch, DetAlg.answers]
        rw [List.map_drop]
        simp
      rw [hans_drop] at hopt
      have hans_lt : 8 * d - 1 + 2 * m < (A.answers matrixOracle (hardSeq e X ℐ)).length :=
        hans_len ▸ hk_lt
      rw [List.getElem?_eq_getElem hans_lt, Option.map_some, Option.some.injEq] at hopt
      have hcorr := hAll (8 * d - 1 + 2 * m) hk_lt
      rw [List.getElem?_eq_getElem hans_lt, Option.some.injEq,
        AuxReduction.graphAfter_epoch_after_ins e X ℐ m hm,
        (DynOracleConn.epoch_answer e X ℐ[m]).1] at hcorr
      rw [hopt, List.getElem_map]
      cases hy : yval X ℐ[m] <;>
        cases ha : (A.answers matrixOracle (hardSeq e X ℐ))[8 * d - 1 + 2 * m] <;>
        simp_all
  · unfold PPHPAlg.Ltotal DetAlg.totalCost
    rw [htr_eq]
    unfold AuxReduction.F_map
    have h1 := AuxReduction.decodeEpochs_cost_le e X ℐ
      ((A.transcript matrixOracle (hardSeq e X ℐ)).drop (8 * d - 1))
    let fullCosts := (A.transcript matrixOracle (hardSeq e X ℐ)).map (fun p => p.1.length)
    have hdrop_map :
        (((A.transcript matrixOracle (hardSeq e X ℐ)).drop (8 * d - 1)).map (fun p => p.1.length)) =
          fullCosts.drop (8 * d - 1) := by
      dsimp [fullCosts]; rw [List.map_drop]
    rw [hdrop_map] at h1
    have hsum_drop : ∀ (L : List ℕ) (k : ℕ), (L.drop k).sum ≤ L.sum := by
      intro L k
      conv_rhs => rw [← List.take_append_drop k L, List.sum_append]
      omega
    exact h1.trans (hsum_drop fullCosts (8 * d - 1))
