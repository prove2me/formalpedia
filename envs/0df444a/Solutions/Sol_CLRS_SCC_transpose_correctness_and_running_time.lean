-- Prove2me | solution 1 for CLRS.SCC.transpose_correctness_and_running_time
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:35:38.787657+00:00
-- url     : https://prove2.me/submissions/7053b2e1-0be6-4cbc-b57c-aadb8b0ab58e

import Definitions.Def_CLRS_SCC_Program
import Mathlib.Data.List.Count

set_option autoImplicit false

open Algo2LeanGenerated CLRS.GraphTraversal CLRS.SCC Algo2LeanCore
open Algo.scc.Algo2LeanGenerated

namespace TransposeProof

abbrev GI := Algo.graph_input.Algo2LeanGenerated.seq_Seq_Int

theorem preserves_refl (h : Heap) : Preserves h h := by
  constructor <;> intros <;> rfl

theorem preserves_trans {a b c : Heap} (ab : Preserves a b) (bc : Preserves b c) : Preserves a c := by
  constructor
  · intro r hr; exact (bc.sequences r (lt_of_lt_of_le hr ab.sequenceAllocation)).trans (ab.sequences r hr)
  · intro r hr; exact (bc.objects r (lt_of_lt_of_le hr ab.objectAllocation)).trans (ab.objects r hr)
  · intro r hr; exact (bc.collections r (lt_of_lt_of_le hr ab.collectionAllocation)).trans (ab.collections r hr)
  · exact ab.sequenceAllocation.trans bc.sequenceAllocation
  · exact ab.objectAllocation.trans bc.objectAllocation
  · exact ab.collectionAllocation.trans bc.collectionAllocation
  · exact ab.workMonotone.trans bc.workMonotone
  · intro n hn; exact (bc.otherClocks n hn).trans (ab.otherClocks n hn)

theorem preserves_tick (h : Heap) (k : Nat) : Preserves h (h.tick "graph_work" k) := by
  constructor
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · exact le_refl _
  · exact le_refl _
  · exact le_refl _
  · simp
  · intro name hn; simp [Heap.clocks_tick_other, hn]

theorem preserves_allocate (h : Heap) (s : Seq) : Preserves h (h.allocate s) := by
  constructor
  · intro r hr; funext i; exact Heap.read_allocate_old _ _ _ _ hr
  all_goals intros; simp

theorem preserves_write {before h : Heap} (p : Preserves before h) (r : SeqRef)
    (hr : before.nextRef ≤ r) (i v : Int) : Preserves before (h.write r i v) := by
  constructor
  · intro ref href; funext j
    have ne : ref ≠ r := Nat.ne_of_lt (lt_of_lt_of_le href hr)
    exact (Heap.read_write_other_ref h ref r j i v ne).trans (congrFun (p.sequences ref href) j)
  · exact p.objects
  · exact p.collections
  · exact p.sequenceAllocation
  · exact p.objectAllocation
  · exact p.collectionAllocation
  · exact p.workMonotone
  · exact p.otherClocks

theorem preserves_set {before h : Heap} (p : Preserves before h) (r : CollectionRef)
    (hr : before.nextCollection ≤ r) (i : Int) (v : SeqRef) :
    Preserves before (seq_Seq_Int.set h r i v) := by
  constructor
  · exact p.sequences
  · exact p.objects
  · intro ref href
    simpa [SequenceType.set, Heap.writeElement, show ref ≠ r by omega] using p.collections ref href
  · exact p.sequenceAllocation
  · exact p.objectAllocation
  · exact p.collectionAllocation
  · exact p.workMonotone
  · exact p.otherClocks

theorem preserves_const (h : Heap) (r : SeqRef) : Preserves h (seq_Seq_Int.const h r).1 := by
  constructor
  · intros; rfl
  · intros; rfl
  · intro ref href
    exact Heap.collections_allocateSequence_old _ _ _ _ href
  · exact le_refl _
  · exact le_refl _
  · change h.nextCollection ≤ h.nextCollection + 1; omega
  · exact le_refl _
  · intros; rfl

theorem graph_preserved {a b : Heap} (p : Preserves a b) {ref : ObjectRef} {g : Graph}
    (hg : GraphRep a ref g) : GraphRep b ref g := by
  have cls : Algo.graph_input.Algo2LeanGenerated.is_UnweightedGraph b ref := by
    rcases hg.1 with ⟨allocated,cl⟩
    exact ⟨lt_of_lt_of_le allocated p.objectAllocation, by
      simpa [Heap.objectClass, p.objects ref allocated] using cl⟩
  have fields : ∀ field, b.readField ref field = a.readField ref field := by
    intro f; simp [Heap.readField, p.objects ref hg.1.1]
  have size := hg.2.1
  rcases hg.2.2 with ⟨adj,deg,ha,hd,hav,hdv,rows⟩
  have col : b.collections adj = a.collections adj := p.collections adj hav.1
  have valid : GI.valid b adj := ⟨lt_of_lt_of_le hav.1 p.collectionAllocation, by
    simpa [Heap.sequenceType, col] using hav.2⟩
  refine ⟨cls,?_,adj,deg,?_,?_,valid,lt_of_lt_of_le hdv p.sequenceAllocation,?_⟩
  · simpa [Algo.graph_input.Algo2LeanGenerated.field_UnweightedGraph_size, cls, hg.1, fields] using size
  · simpa [Algo.graph_input.Algo2LeanGenerated.field_UnweightedGraph_adj, cls, hg.1, fields] using ha
  · simpa [Algo.graph_input.Algo2LeanGenerated.field_UnweightedGraph_degree, cls, hg.1, fields] using hd
  · intro u hu
    rcases rows u hu with ⟨degv,row,get,rv,vals⟩
    refine ⟨by simpa [p.sequences deg hdv] using degv,row,?_,lt_of_lt_of_le rv p.sequenceAllocation,?_⟩
    · simpa [SequenceType.get, hav, valid, Heap.readElement, col] using get
    · intro j hj; simpa [p.sequences row rv] using vals j hj

@[simp] theorem valid_tick (h : Heap) (r : CollectionRef) (k : Nat) :
    seq_Seq_Int.valid (h.tick "graph_work" k) r ↔ seq_Seq_Int.valid h r := Iff.rfl
@[simp] theorem get_tick (h : Heap) (r : CollectionRef) (i : Int) (k : Nat) :
    seq_Seq_Int.get (h.tick "graph_work" k) r i = seq_Seq_Int.get h r i := rfl
@[simp] theorem valid_alloc (h : Heap) (r : CollectionRef) (s : Seq) :
    seq_Seq_Int.valid (h.allocate s) r ↔ seq_Seq_Int.valid h r := Iff.rfl
@[simp] theorem get_alloc (h : Heap) (r : CollectionRef) (i : Int) (s : Seq) :
    seq_Seq_Int.get (h.allocate s) r i = seq_Seq_Int.get h r i := rfl
@[simp] theorem valid_write (h : Heap) (r : CollectionRef) (a : SeqRef) (i v : Int) :
    seq_Seq_Int.valid (h.write a i v) r ↔ seq_Seq_Int.valid h r := Iff.rfl
@[simp] theorem get_write (h : Heap) (r : CollectionRef) (i : Int) (a : SeqRef) (j v : Int) :
    seq_Seq_Int.get (h.write a j v) r i = seq_Seq_Int.get h r i := rfl

-- The first loop allocates one distinct zero row per vertex.
def initHeap (h : Heap) : Nat → Heap
  | 0 => ((seq_Seq_Int.const ((h.tick "graph_work" 1).allocate (fun _ => 0)) h.nextRef).1.allocate (fun _ => 0)).tick "graph_work" 1
  | k+1 => (seq_Seq_Int.set ((initHeap h k).tick "graph_work" 1 |>.allocate (fun _ => 0))
      h.nextCollection k (h.nextRef + 2 + k)).tick "graph_work" 1

@[simp] theorem init_meta (h : Heap) (k : Nat) :
    (initHeap h k).nextRef = h.nextRef + 2 + k ∧
    (initHeap h k).nextObject = h.nextObject ∧
    (initHeap h k).nextCollection = h.nextCollection + 1 ∧
    (initHeap h k).objects = h.objects ∧
    (initHeap h k).clocks "graph_work" = h.clocks "graph_work" + 2 + 2*k := by
  induction k with
  | zero => simp [initHeap, SequenceType.const, SequenceType.create, Heap.createSequence]
  | succ k ih =>
    simp only [initHeap, SequenceType.set, Heap.tick_nextRef, Heap.writeElement_nextRef,
      Heap.allocate_nextRef, Heap.tick_nextObject, Heap.writeElement_nextObject, Heap.allocate_nextObject,
      Heap.tick_nextCollection, Heap.writeElement_nextCollection, Heap.allocate_nextCollection,
      Heap.tick_objects, Heap.writeElement_objects, Heap.allocate_objects, Heap.clocks_tick_same,
      Heap.writeElement_clocks, Heap.allocate_clocks]
    rcases ih with ⟨a,b,c,d,e⟩; simp_all; omega

theorem init_preserves (h : Heap) (k : Nat) : Preserves h (initHeap h k) := by
  induction k with
  | zero => exact preserves_trans (preserves_trans (preserves_trans (preserves_trans
      (preserves_tick h 1) (preserves_allocate _ _)) (preserves_const _ _))
      (preserves_allocate _ _)) (preserves_tick _ 1)
  | succ k ih =>
    apply preserves_trans (preserves_set
      (preserves_trans (preserves_trans ih (preserves_tick _ 1)) (preserves_allocate _ _))
      _ (le_refl _) _ _) (preserves_tick _ 1)

theorem init_valid (h : Heap) (k : Nat) : seq_Seq_Int.valid (initHeap h k) h.nextCollection := by
  induction k with
  | zero =>
    change seq_Seq_Int.valid (seq_Seq_Int.const ((h.tick "graph_work" 1).allocate (fun _ => 0)) h.nextRef).1 h.nextCollection
    exact seq_Seq_Int.valid_const _ _
  | succ k ih => simpa [initHeap] using ih

theorem init_get (h : Heap) (k v : Nat) (hv : v < k) :
    seq_Seq_Int.get (initHeap h k) h.nextCollection v = some (h.nextRef+2+v) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases eq : v = k
    · subst v; simp [initHeap, init_valid]
    · have ne : (v : Int) ≠ (k : Int) := by omega
      simpa [initHeap, ne] using ih (by omega)

theorem init_degree (h : Heap) (k : Nat) (i : Int) :
    (initHeap h k).read (h.nextRef+1) i = 0 := by
  induction k with
  | zero =>
    change ((seq_Seq_Int.const ((h.tick "graph_work" 1).allocate (fun _ => 0)) h.nextRef).1.allocate (fun _ => 0)).read (h.nextRef+1) i = 0
    exact Heap.read_allocate_new _ _ _
  | succ k ih =>
    have lt : h.nextRef+1 < ((initHeap h k).tick "graph_work" 1).nextRef := by simp only [Heap.tick_nextRef, (init_meta h k).1]; omega
    change (((initHeap h k).tick "graph_work" 1).allocate (fun _ => 0)).read (h.nextRef+1) i = 0
    rw [Heap.read_allocate_old _ _ _ _ lt]; exact ih

theorem init_row (h : Heap) (k v : Nat) (hv : v < k) (i : Int) :
    (initHeap h k).read (h.nextRef+2+v) i = 0 := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases eq : v = k
    · subst v
      simp only [initHeap, Heap.read, Heap.tick_store, SequenceType.set, Heap.writeElement_store]
      change (((initHeap h k).tick "graph_work" 1).allocate (fun _ => 0)).read (h.nextRef+2+k) i = 0
      rw [← (init_meta h k).1]; exact Heap.read_allocate_new _ _ _
    · have lt : h.nextRef+2+v < ((initHeap h k).tick "graph_work" 1).nextRef := by
        simp only [Heap.tick_nextRef, (init_meta h k).1]; omega
      change (((initHeap h k).tick "graph_work" 1).allocate (fun _ => 0)).read (h.nextRef+2+v) i = 0
      rw [Heap.read_allocate_old _ _ _ _ lt]; exact ih (by omega)


theorem init_execution (h : Heap) (graph : ObjectRef) (g : Graph)
    (hg : GraphRep h graph g) (k : Nat) (hk : k ≤ g.size) (stack : Stack) :
    ∃ s : State_transpose, s.v0 = graph ∧ s.v1 = h.nextCollection ∧
      s.v2 = h.nextRef+1 ∧ s.v3 = (k : Int) ∧
      Reaches Step (.active h (Frame.fn_transpose 44 {v0 := graph}) stack)
        (.active (initHeap h k) (Frame.fn_transpose 26 s) stack) := by
  induction k with
  | zero =>
    refine ⟨{v0 := graph, v1 := h.nextCollection, v2 := h.nextRef+1, t21 := h.nextRef, t20 := h.nextCollection, t18 := h.nextRef+1},rfl,rfl,rfl,rfl,?_⟩
    apply Reaches.prepend (Step.transpose_pc44 _ _ _)
    apply Reaches.prepend (Step.transpose_pc43 _ _ _)
    apply Reaches.prepend (Step.transpose_pc42 _ _ _)
    apply Reaches.prepend (Step.transpose_pc41 _ _ _)
    apply Reaches.prepend (Step.transpose_pc40 _ _ _)
    apply Reaches.prepend (Step.transpose_pc39 _ _ _)
    apply Reaches.prepend (Step.transpose_pc38 _ _ _)
    apply Reaches.prepend (Step.transpose_pc37 _ _ _)
    apply Reaches.prepend (Step.transpose_pc36 _ _ _)
    apply Reaches.prepend (Step.transpose_pc35 _ _ _)
    exact Reaches.refl _
  | succ k ih =>
    obtain ⟨s,sv0,sv1,sv2,sv3,run⟩ := ih (by omega)
    have size : field__a2l_import_0_UnweightedGraph_size (initHeap h k) s.v0 = some (g.size : Int) := by
      rw [sv0]; exact (graph_preserved (init_preserves h k) hg).2.1
    have cond : decide (s.v3 < (field__a2l_import_0_UnweightedGraph_size (initHeap h k) s.v0).getD 0) = true := by
      simp only [size, Option.getD_some, sv3, decide_eq_true_eq]; omega
    refine ⟨{s with t13 := true, t17 := 0, t14 := h.nextRef+2+k, t16 := s.v1, t15 := s.v3, v3 := s.v3+1},sv0,sv1,sv2,by simp [sv3],run.trans ?_⟩
    apply Reaches.prepend (Step.transpose_pc26 _ _ _ (by simp [size]))
    apply Reaches.prepend (Step.transpose_pc25_true _ _ _ cond)
    apply Reaches.prepend (Step.transpose_pc34 _ _ _)
    apply Reaches.prepend (Step.transpose_pc33 _ _ _)
    apply Reaches.prepend (Step.transpose_pc32 _ _ _)
    apply Reaches.prepend (Step.transpose_pc31 _ _ _)
    apply Reaches.prepend (Step.transpose_pc30 _ _ _)
    apply Reaches.prepend (Step.transpose_pc29 _ _ _ (by simpa [sv1] using init_valid h k))
    apply Reaches.prepend (Step.transpose_pc28 _ _ _)
    apply Reaches.prepend (Step.transpose_pc27 _ _ _)
    have cond' : decide ((k : Int) < (field__a2l_import_0_UnweightedGraph_size (initHeap h k) s.v0).getD 0) = true := by simpa only [sv3] using cond
    simpa only [initHeap, sv1, sv3, cond', Heap.tick_nextRef, (init_meta h k).1] using
      (Reaches.refl (.active (initHeap h (k+1))
        (Frame.fn_transpose 26 {s with t13 := true, t17 := 0, t14 := h.nextRef+2+k, t16 := s.v1, t15 := s.v3, v3 := s.v3+1}) stack) : Reaches Step _ _)

abbrev RowData := Nat → List Nat

def appendRow (R : RowData) (u v : Nat) : RowData :=
  fun x => if x = v then R x ++ [u] else R x

def mass (n : Nat) (R : RowData) : Nat := ((List.range n).map fun v => (R v).length).sum

theorem mass_append (n : Nat) (R : RowData) (u v : Nat) (hv : v < n) :
    mass n (appendRow R u v) = mass n R + 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [mass, List.range_succ, List.map_append, List.map_singleton, List.sum_append,
      List.sum_singleton] at ih ⊢
    by_cases eq : v = n
    · subst v
      have old : (List.range n).map (fun v => (appendRow R u n v).length) =
          (List.range n).map (fun v => (R v).length) := by
        apply List.map_congr_left
        intro x hx; have hxn := List.mem_range.mp hx
        simp [appendRow, show x ≠ n by omega]
      rw [old]; simp [appendRow]; omega
    · have vn : v < n := by omega
      rw [ih vn]
      simp [appendRow, Ne.symm eq]; omega

structure Rows (h : Heap) (base n : Nat) (adj : CollectionRef) (degree : SeqRef) (R : RowData) : Prop where
  valid : seq_Seq_Int.valid h adj
  degreeValid : degree < h.nextRef
  separate : degree < base
  rowsValid : base + n ≤ h.nextRef
  get : ∀ v : Nat, v < n → seq_Seq_Int.get h adj v = some (base+v)
  lengths : ∀ v : Nat, v < n → h.read degree v = ((R v).length : Int)
  values : ∀ v : Nat, v < n → ∀ j : Nat, j < (R v).length → h.read (base+v) j = ((R v)[j]! : Int)
  bounded : ∀ v : Nat, v < n → ∀ x ∈ R v, x < n

theorem Rows.tick {h : Heap} {base n adj degree : Nat} {R : RowData}
    (r : Rows h base n adj degree R) (k : Nat) : Rows (h.tick "graph_work" k) base n adj degree R :=
  ⟨r.valid,r.degreeValid,r.separate,r.rowsValid,r.get,r.lengths,r.values,r.bounded⟩

theorem initial_rows (h : Heap) (n : Nat) :
    Rows (initHeap h n) (h.nextRef+2) n h.nextCollection (h.nextRef+1) (fun _ => []) := by
  constructor
  · exact init_valid h n
  · rw [(init_meta h n).1]; exact lt_of_lt_of_le (Nat.lt_succ_self (h.nextRef+1)) (Nat.le_add_right (h.nextRef+2) n)
  · exact Nat.lt_succ_self (h.nextRef+1)
  · rw [(init_meta h n).1]
  · exact init_get h n
  · intro v hv; exact init_degree h n v
  · intros v hv j hj; simp at hj
  · intros v hv x hx; simp at hx

def push (h : Heap) (base degree u v : Nat) : Heap :=
  (((h.tick "graph_work" 1).write (base+v) (h.read degree v) u).write degree v
    (h.read degree v + 1)).tick "graph_work" 1

@[simp] theorem push_meta (h : Heap) (base degree u v : Nat) :
    (push h base degree u v).nextRef = h.nextRef ∧
    (push h base degree u v).nextObject = h.nextObject ∧
    (push h base degree u v).nextCollection = h.nextCollection ∧
    (push h base degree u v).objects = h.objects ∧
    (push h base degree u v).collections = h.collections ∧
    (push h base degree u v).clocks "graph_work" = h.clocks "graph_work" + 2 := by
  simp [push]

theorem push_preserves {before h : Heap} (p : Preserves before h) (base degree u v : Nat)
    (hb : before.nextRef ≤ base) (hd : before.nextRef ≤ degree) :
    Preserves before (push h base degree u v) := by
  exact preserves_trans (preserves_write (preserves_write
    (preserves_trans p (preserves_tick _ 1)) _ (by omega) _ _) _ hd _ _) (preserves_tick _ 1)

theorem push_rows {h : Heap} {base n adj degree : Nat} {R : RowData}
    (r : Rows h base n adj degree R) (u v : Nat) (hu : u < n) (hv : v < n) :
    Rows (push h base degree u v) base n adj degree (appendRow R u v) := by
  have sep : ∀ x, base+x ≠ degree := fun x => Nat.ne_of_gt (lt_of_lt_of_le r.separate (Nat.le_add_right base x))
  refine ⟨r.valid,r.degreeValid,r.separate,r.rowsValid,r.get,?_,?_,?_⟩
  · intro x hx
    by_cases eq : x = v
    · subst x; simp [push, appendRow, r.lengths v hv]
    · have ine : (x : Int) ≠ (v : Int) := by omega
      simp only [push, Heap.read_tick, Heap.read_write_other_index _ _ _ _ _ ine]
      rw [Heap.read_write_other_ref _ degree (base+v) _ _ _ (Ne.symm (sep v))]
      simpa [appendRow, eq] using r.lengths x hx
  · intro x hx j hj
    simp only [push, Heap.read_tick]
    rw [Heap.read_write_other_ref _ (base+x) degree _ _ _ (sep x)]
    by_cases eq : x = v
    · subst x
      have len := r.lengths v hv
      simp only [appendRow, if_true, List.length_append, List.length_singleton] at hj
      by_cases jeq : j = (R v).length
      · subst j
        rw [len, Heap.read_write_same]
        simp [appendRow, List.getElem!_eq_getElem?_getD, List.getElem?_append]
      · have jl : j < (R v).length := by omega
        have jne : (j : Int) ≠ h.read degree v := by rw [len]; omega
        rw [Heap.read_write_other_index _ _ _ _ _ jne, Heap.read_tick, r.values v hv j jl]
        simp [appendRow, List.getElem!_eq_getElem?_getD, List.getElem?_append, jl]
    · rw [Heap.read_write_other_ref _ (base+x) (base+v) _ _ _ (by omega : base+x ≠ base+v), Heap.read_tick]
      simpa [appendRow, eq] using r.values x hx j (by simpa [appendRow, eq] using hj)
  · intro x hx y hy
    by_cases eq : x = v
    · subst x; simp only [appendRow, if_true, List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · exact r.bounded v hv y hy
      · exact hu
    · exact r.bounded x hx y (by simpa [appendRow, eq] using hy)


def scanHeap (h : Heap) (base degree u : Nat) : List Nat → Heap
  | [] => h
  | v::vs => scanHeap (push h base degree u v) base degree u vs

def scanData (R : RowData) (u : Nat) : List Nat → RowData
  | [] => R
  | v::vs => scanData (appendRow R u v) u vs

theorem scan_rows {h : Heap} {base n adj degree : Nat} {R : RowData}
    (r : Rows h base n adj degree R) (u : Nat) (hu : u < n)
    (vs : List Nat) (hv : ∀ v ∈ vs, v < n) :
    Rows (scanHeap h base degree u vs) base n adj degree (scanData R u vs) := by
  induction vs generalizing h R with
  | nil => exact r
  | cons v vs ih => exact ih (push_rows r u v hu (hv v (by simp))) (fun x hx => hv x (by simp [hx]))

theorem scan_preserves {before h : Heap} (p : Preserves before h) (base degree u : Nat)
    (hb : before.nextRef ≤ base) (hd : before.nextRef ≤ degree) (vs : List Nat) :
    Preserves before (scanHeap h base degree u vs) := by
  induction vs generalizing h with
  | nil => exact p
  | cons v vs ih => exact ih (push_preserves p base degree u v hb hd)

theorem scan_clock (h : Heap) (base degree u : Nat) (vs : List Nat) :
    (scanHeap h base degree u vs).clocks "graph_work" = h.clocks "graph_work" + 2*vs.length := by
  induction vs generalizing h with
  | nil => simp [scanHeap]
  | cons v vs ih => rw [scanHeap, ih, (push_meta h base degree u v).2.2.2.2.2]; simp [List.length_cons]; omega

theorem scan_mass (n : Nat) (R : RowData) (u : Nat) (vs : List Nat) (hv : ∀ v ∈ vs, v < n) :
    mass n (scanData R u vs) = mass n R + vs.length := by
  induction vs generalizing R with
  | nil => simp [scanData]
  | cons v vs ih =>
    rw [scanData, ih _ (fun x hx => hv x (by simp [hx])), mass_append n R u v (hv v (by simp))]
    simp; omega

theorem scan_count (R : RowData) (u : Nat) (vs : List Nat) (x y : Nat) :
    (scanData R u vs x).count y = (R x).count y + if y = u then vs.count x else 0 := by
  induction vs generalizing R with
  | nil => simp [scanData]
  | cons v vs ih =>
    rw [scanData, ih]
    by_cases hx : x = v <;> by_cases hy : y = u <;>
      simp [appendRow, hx, hy, Ne.symm, List.count_cons, BEq.beq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem inner_run (before h : Heap) (g : Graph) (base : Nat) (R : RowData)
    (u row : Nat) (s : State_transpose) (pre todo : List Nat)
    (hg : GraphRep before s.v0 g) (p : Preserves before h)
    (r : Rows h base g.size s.v1 s.v2 R)
    (hb : before.nextRef ≤ base) (hd : before.nextRef ≤ s.v2)
    (hu : u < g.size) (su : s.v3 = (u : Int)) (sr : s.v4 = row)
    (sj : s.v5 = (pre.length : Int)) (eq : g.neighbors u = pre ++ todo)
    (rv : row < before.nextRef)
    (vals : ∀ j : Nat, j < (g.neighbors u).length → before.read row j = ((g.neighbors u)[j]! : Int))
    (stack : Stack) :
    ∃ s' : State_transpose, s'.v0 = s.v0 ∧ s'.v1 = s.v1 ∧ s'.v2 = s.v2 ∧ s'.v3 = s.v3 ∧
      Reaches Step (.active h (Frame.fn_transpose 12 s) stack)
        (.active (scanHeap h base s.v2 u todo) (Frame.fn_transpose 10 s') stack) := by
  induction todo generalizing h R s pre with
  | nil =>
    have rep := graph_preserved p hg
    rcases rep.2.2 with ⟨adj,deg,ha,hdeg,hav,hdv,hrows⟩
    have dval := (hrows u hu).1
    have cond : decide (s.v5 < h.read ((field__a2l_import_0_UnweightedGraph_degree h s.v0).getD 0) s.v3) = false := by
      simp only [hdeg, Option.getD_some, su, dval, sj, eq, List.append_nil, decide_eq_false_iff_not]
      omega
    refine ⟨{s with t12 := false},rfl,rfl,rfl,rfl,?_⟩
    apply Reaches.prepend (Step.transpose_pc12 _ _ _ (by simp [hdeg,hdv]))
    apply Reaches.prepend (Step.transpose_pc11_false _ _ _ cond)
    simpa only [scanHeap, cond] using
      (Reaches.refl (.active h (Frame.fn_transpose 10 {s with t12 := false}) stack) : Reaches Step _ _)
  | cons v vs ih =>
    have rep := graph_preserved p hg
    rcases rep.2.2 with ⟨adj,deg,ha,hdeg,hav,hdv,hrows⟩
    have dval := (hrows u hu).1
    have cond : decide (s.v5 < h.read ((field__a2l_import_0_UnweightedGraph_degree h s.v0).getD 0) s.v3) = true := by
      simp only [hdeg, Option.getD_some, su, dval, sj, eq, List.length_append, List.length_cons, decide_eq_true_eq]
      omega
    have vin : v ∈ g.neighbors u := by rw [eq]; simp
    have hv := g.bounded u hu v vin
    have atj : h.read s.v4 s.v5 = (v : Int) := by
      rw [sr,sj,p.sequences row rv]
      rw [vals pre.length (by rw [eq]; simp)]
      simp [eq]
    let sn : State_transpose := {s with t12 := true, v6 := v, v5 := s.v5+1}
    have p' := push_preserves p base s.v2 u v hb hd
    have r' := push_rows r u v hu hv
    have eq' : g.neighbors u = (pre ++ [v]) ++ vs := by simpa [List.append_assoc] using eq
    obtain ⟨s',s0,s1,s2,s3,run⟩ := ih (push h base s.v2 u v) (appendRow R u v) sn (pre++[v])
      hg p' r' hd (by simpa [sn] using su) (by simpa [sn] using sr)
      (by simp [sn,sj]) eq'
    refine ⟨s',s0,s1,s2,s3,?_⟩
    apply Reaches.prepend (Step.transpose_pc12 _ _ _ (by simp [hdeg,hdv]))
    apply Reaches.prepend (Step.transpose_pc11_true _ _ _ cond)
    apply Reaches.prepend (Step.transpose_pc18 _ _ _)
    apply Reaches.prepend (Step.transpose_pc17 _ _ _ (by simpa [sr] using lt_of_lt_of_le rv p.sequenceAllocation))
    apply Reaches.prepend (Step.transpose_pc16 _ _ _ ?_)
    · apply Reaches.prepend (Step.transpose_pc15 _ _ _ (by simp [r.degreeValid]))
      apply Reaches.prepend (Step.transpose_pc14 _ _ _)
      apply Reaches.prepend (Step.transpose_pc13 _ _ _)
      have getv := r.get v hv
      have sep : s.v2 ≠ base+v := Nat.ne_of_lt (lt_of_lt_of_le r.separate (Nat.le_add_right base v))
      have cond' : decide (s.v5 < h.read ((field__a2l_import_0_UnweightedGraph_degree h s.v0).getD 0) (u : Int)) = true := by simpa only [su] using cond
      simpa only [scanHeap, push, sn, cond, cond', atj, getv, Option.getD_some, su,
        Heap.read_tick, get_tick, Heap.read_write_other_ref _ s.v2 (base+v) _ _ _ sep] using run
    · simp only [Heap.read_tick, atj, Heap.tick_nextRef, get_tick, r.get v hv, Option.isSome_some,
        Option.getD_some, true_and]
      exact ⟨r.degreeValid,lt_of_lt_of_le (Nat.add_lt_add_left hv base) r.rowsValid⟩


@[simp] theorem size_tick (h : Heap) (ref : ObjectRef) (k : Nat) :
    field__a2l_import_0_UnweightedGraph_size (h.tick "graph_work" k) ref = field__a2l_import_0_UnweightedGraph_size h ref := rfl
@[simp] theorem adj_tick (h : Heap) (ref : ObjectRef) (k : Nat) :
    field__a2l_import_0_UnweightedGraph_adj (h.tick "graph_work" k) ref = field__a2l_import_0_UnweightedGraph_adj h ref := rfl

theorem get_preserved {a b : Heap} (p : Preserves a b) (ref : CollectionRef)
    (hv : seq_Seq_Int.valid a ref) (i : Int) :
    seq_Seq_Int.get b ref i = seq_Seq_Int.get a ref i := by
  have col := p.collections ref hv.1
  have valid : seq_Seq_Int.valid b ref := ⟨lt_of_lt_of_le hv.1 p.collectionAllocation, by
    simpa [Heap.sequenceType,col] using hv.2⟩
  simp [SequenceType.get, valid, hv, Heap.readElement,col]

theorem field_adj_preserved {a b : Heap} (p : Preserves a b) {ref : ObjectRef} {g : Graph}
    (hg : GraphRep a ref g) :
    field__a2l_import_0_UnweightedGraph_adj b ref = field__a2l_import_0_UnweightedGraph_adj a ref := by
  have cl := (graph_preserved p hg).1
  simp [field__a2l_import_0_UnweightedGraph_adj, Algo.graph_input.Algo2LeanGenerated.field_UnweightedGraph_adj,
    cl,hg.1,Heap.readField,p.objects ref hg.1.1]

def edgePrefix (g : Graph) (k : Nat) : Nat := ((List.range k).map fun u => (g.neighbors u).length).sum

def outerData (g : Graph) : Nat → RowData
  | 0 => fun _ => []
  | k+1 => scanData (outerData g k) k (g.neighbors k)

def outerHeap (h : Heap) (base degree : Nat) (g : Graph) : Nat → Heap
  | 0 => h
  | k+1 => (scanHeap (((outerHeap h base degree g k).tick "graph_work" 1).tick "graph_work" 1)
      base degree k (g.neighbors k)).tick "graph_work" 1

theorem outer_preserves {before h : Heap} (p : Preserves before h) (base degree : Nat) (g : Graph)
    (hb : before.nextRef ≤ base) (hd : before.nextRef ≤ degree) (k : Nat) :
    Preserves before (outerHeap h base degree g k) := by
  induction k with
  | zero => exact p
  | succ k ih =>
    exact preserves_trans (scan_preserves
      (preserves_trans (preserves_trans ih (preserves_tick _ 1)) (preserves_tick _ 1))
      base degree k hb hd _) (preserves_tick _ 1)

theorem outer_rows {h : Heap} {base adj degree : Nat} {g : Graph}
    (r : Rows h base g.size adj degree (fun _ => [])) (k : Nat) (hk : k ≤ g.size) :
    Rows (outerHeap h base degree g k) base g.size adj degree (outerData g k) := by
  induction k with
  | zero => exact r
  | succ k ih =>
    exact (scan_rows (((ih (by omega)).tick 1).tick 1) k (by omega) _ (g.bounded k (by omega))).tick 1

theorem outer_count (g : Graph) (k x y : Nat) :
    (outerData g k x).count y = if y < k then (g.neighbors y).count x else 0 := by
  induction k with
  | zero => simp [outerData]
  | succ k ih =>
    rw [outerData,scan_count,ih]
    by_cases hy : y = k
    · subst y; simp
    · by_cases hlt : y < k <;> simp [hy,hlt,show (y < k+1 ↔ y < k) by omega]

theorem outer_mass (g : Graph) (k : Nat) (hk : k ≤ g.size) :
    mass g.size (outerData g k) = edgePrefix g k := by
  induction k with
  | zero => simp [mass,outerData,edgePrefix]
  | succ k ih =>
    rw [outerData,scan_mass _ _ _ _ (g.bounded k (by omega)),ih (by omega)]
    simp [edgePrefix,List.range_succ]

theorem outer_clock (h : Heap) (base degree : Nat) (g : Graph) (k : Nat) :
    (outerHeap h base degree g k).clocks "graph_work" =
      h.clocks "graph_work" + 3*k + 2*edgePrefix g k := by
  induction k with
  | zero => simp [outerHeap,edgePrefix]
  | succ k ih =>
    simp only [outerHeap,Heap.clocks_tick_same,scan_clock,ih]
    simp only [edgePrefix,List.range_succ,List.map_append,List.map_singleton,List.sum_append,List.sum_singleton]
    omega

theorem outer_run (before h : Heap) (g : Graph) (base : Nat) (s : State_transpose)
    (hg : GraphRep before s.v0 g) (p : Preserves before h)
    (r : Rows h base g.size s.v1 s.v2 (fun _ => []))
    (hb : before.nextRef ≤ base) (hd : before.nextRef ≤ s.v2) (sz : s.v3 = 0)
    (k : Nat) (hk : k ≤ g.size) (stack : Stack) :
    ∃ s' : State_transpose, s'.v0 = s.v0 ∧ s'.v1 = s.v1 ∧ s'.v2 = s.v2 ∧ s'.v3 = (k : Int) ∧
      Reaches Step (.active h (Frame.fn_transpose 8 s) stack)
        (.active (outerHeap h base s.v2 g k) (Frame.fn_transpose 8 s') stack) := by
  induction k with
  | zero => exact ⟨s,rfl,rfl,rfl,sz,Reaches.refl _⟩
  | succ k ih =>
    obtain ⟨sk,sk0,sk1,sk2,sk3,run⟩ := ih (by omega)
    let cur := outerHeap h base s.v2 g k
    have pc : Preserves before cur := outer_preserves p base s.v2 g hb hd k
    have rc : Rows cur base g.size sk.v1 sk.v2 (outerData g k) := by
      simpa only [sk1,sk2] using outer_rows r k (by omega)
    have gcur : GraphRep cur sk.v0 g := by rw [sk0]; exact graph_preserved pc hg
    have size := gcur.2.1
    have cond : decide (sk.v3 < (field__a2l_import_0_UnweightedGraph_size cur sk.v0).getD 0) = true := by
      simp only [size,Option.getD_some,sk3,decide_eq_true_eq]; omega
    rcases hg.2.2 with ⟨adj,deg,ha,hdeg,hav,hdv,hrows⟩
    rcases (hrows k (by omega)).2 with ⟨row,get,rv,vals⟩
    have adjCur : field__a2l_import_0_UnweightedGraph_adj cur sk.v0 = some adj := by
      rw [sk0,field_adj_preserved pc hg]; exact ha
    have getCur : seq_Seq_Int.get cur adj sk.v3 = some row := by
      rw [sk3,get_preserved pc adj hav]; exact get
    let si : State_transpose := {sk with t11 := true, v4 := row, v5 := 0}
    have pi : Preserves before ((cur.tick "graph_work" 1).tick "graph_work" 1) :=
      preserves_trans (preserves_trans pc (preserves_tick _ 1)) (preserves_tick _ 1)
    obtain ⟨sf,f0,f1,f2,f3,inner⟩ := inner_run before ((cur.tick "graph_work" 1).tick "graph_work" 1)
      g base (outerData g k) k row si [] (g.neighbors k)
      (by simpa only [si,sk0] using hg) pi (rc.tick 1 |>.tick 1) hb
      (by simpa only [si,sk2] using hd) (by omega) (by simpa [si] using sk3) rfl rfl (by simp) rv vals stack
    refine ⟨{sf with v3 := sf.v3+1},f0.trans sk0,f1.trans sk1,f2.trans sk2,?_,run.trans ?_⟩
    · simp only [f3,si,sk3]; omega
    · simp only [cur] at size adjCur getCur cond
      simp only [sk3] at getCur
      apply Reaches.prepend (Step.transpose_pc8 _ _ _ (by simp [size]))
      apply Reaches.prepend (Step.transpose_pc7_true _ _ _ cond)
      apply Reaches.prepend (Step.transpose_pc22 _ _ _)
      apply Reaches.prepend (Step.transpose_pc21 _ _ _ (by simp only [sk3,adj_tick,adjCur,Option.isSome_some,Option.getD_some,get_tick,getCur,and_self]))
      apply Reaches.prepend (Step.transpose_pc20 _ _ _)
      apply Reaches.prepend (Step.transpose_pc19 _ _ _)
      have cond' : decide ((k : Int) < (field__a2l_import_0_UnweightedGraph_size (outerHeap h base s.v2 g k) sk.v0).getD 0) = true := by simpa only [sk3] using cond
      have inner' := inner
      simp only [si,cur,sk3,cond',get_tick,getCur,adj_tick,adjCur,Option.getD_some] at inner' ⊢
      apply inner'.trans
      apply Reaches.prepend (Step.transpose_pc10 _ _ _)
      apply Reaches.prepend (Step.transpose_pc9 _ _ _)
      simpa only [outerHeap,cur,si,sk2] using
        (Reaches.refl (.active (outerHeap h base s.v2 g (k+1))
          (Frame.fn_transpose 8 {sf with v3 := sf.v3+1}) stack) : Reaches Step _ _)


def constructorHeap (h : Heap) (n : Nat) (adj degree : Nat) : Heap :=
  (Algo.graph_input.Algo2LeanGenerated.create_UnweightedGraph h n adj degree).1

theorem constructor_valid (h : Heap) (n adj degree : Nat) :
    is__a2l_import_0_UnweightedGraph (constructorHeap h n adj degree) h.nextObject := by
  simp [constructorHeap,Algo.graph_input.Algo2LeanGenerated.create_UnweightedGraph,
    Algo.graph_input.Algo2LeanGenerated.set_UnweightedGraph_size,
    Algo.graph_input.Algo2LeanGenerated.set_UnweightedGraph_adj,
    Algo.graph_input.Algo2LeanGenerated.set_UnweightedGraph_degree,
    is__a2l_import_0_UnweightedGraph,Algo.graph_input.Algo2LeanGenerated.is_UnweightedGraph]

theorem constructor_fields (h : Heap) (n adj degree : Nat) :
    field__a2l_import_0_UnweightedGraph_size (constructorHeap h n adj degree) h.nextObject = some (n : Int) ∧
    field__a2l_import_0_UnweightedGraph_adj (constructorHeap h n adj degree) h.nextObject = some adj ∧
    field__a2l_import_0_UnweightedGraph_degree (constructorHeap h n adj degree) h.nextObject = some degree := by
  have cl := constructor_valid h n adj degree
  simp only [field__a2l_import_0_UnweightedGraph_size,field__a2l_import_0_UnweightedGraph_adj,
    field__a2l_import_0_UnweightedGraph_degree,Algo.graph_input.Algo2LeanGenerated.field_UnweightedGraph_size,
    Algo.graph_input.Algo2LeanGenerated.field_UnweightedGraph_adj,
    Algo.graph_input.Algo2LeanGenerated.field_UnweightedGraph_degree,cl,if_true]
  simp [constructorHeap,Algo.graph_input.Algo2LeanGenerated.create_UnweightedGraph,
    Algo.graph_input.Algo2LeanGenerated.set_UnweightedGraph_size,
    Algo.graph_input.Algo2LeanGenerated.set_UnweightedGraph_adj,
    Algo.graph_input.Algo2LeanGenerated.set_UnweightedGraph_degree,
    Heap.readField,Heap.writeField,Heap.allocateObject,ObjectValue.asInt,ObjectValue.asSeq,ObjectValue.asCollection]

theorem constructor_preserves (h : Heap) (n adj degree : Nat) :
    Preserves h (constructorHeap h n adj degree) := by
  constructor
  · intros; rfl
  · intro ref hr
    simp [constructorHeap,Algo.graph_input.Algo2LeanGenerated.create_UnweightedGraph,
      Algo.graph_input.Algo2LeanGenerated.set_UnweightedGraph_size,
      Algo.graph_input.Algo2LeanGenerated.set_UnweightedGraph_adj,
      Algo.graph_input.Algo2LeanGenerated.set_UnweightedGraph_degree,
      Heap.writeField,Heap.allocateObject,Nat.ne_of_lt hr]
  · intros; rfl
  · exact le_refl _
  · change h.nextObject ≤ h.nextObject+1; omega
  · exact le_refl _
  · exact le_refl _
  · intros; rfl

theorem constructor_rep {h : Heap} {base n adj degree : Nat} {R : RowData}
    (r : Rows h base n adj degree R) :
    GraphRep (constructorHeap h n adj degree) h.nextObject ⟨n,R,r.bounded⟩ := by
  rcases constructor_fields h n adj degree with ⟨size,ha,hd⟩
  refine ⟨constructor_valid h n adj degree,size,adj,degree,ha,hd,r.valid,r.degreeValid,?_⟩
  intro v hv
  refine ⟨r.lengths v hv,base+v,r.get v hv,?_,r.values v hv⟩
  exact lt_of_lt_of_le (Nat.add_lt_add_left hv base) r.rowsValid

theorem constructor_call (h : Heap) (n adj degree : Nat)
    (hav : GI.valid h adj) (hdv : degree < h.nextRef) :
    Algo.graph_input.UnweightedGraph.Call h ((n : Int),adj,degree)
      (constructorHeap h n adj degree) h.nextObject := by
  refine ⟨⟨hav,hdv⟩,?_⟩
  intro stack
  apply Reaches.prepend (Algo.graph_input.Algo2LeanGenerated.Step.UnweightedGraph_pc9 _ _ _)
  apply Reaches.prepend (Algo.graph_input.Algo2LeanGenerated.Step.UnweightedGraph_pc8 _ _ _)
  apply Reaches.prepend (Algo.graph_input.Algo2LeanGenerated.Step.UnweightedGraph_pc7 _ _ _)
  apply Reaches.prepend (Algo.graph_input.Algo2LeanGenerated.Step.UnweightedGraph_pc6 _ _ _)
  apply Reaches.prepend (Algo.graph_input.Algo2LeanGenerated.Step.UnweightedGraph_pc5 _ _ _)
  apply Reaches.prepend (Algo.graph_input.Algo2LeanGenerated.Step.UnweightedGraph_pc4 _ _ _)
  apply Reaches.prepend (Algo.graph_input.Algo2LeanGenerated.Step.UnweightedGraph_pc3 _ _ _)
  apply Reaches.prepend (Algo.graph_input.Algo2LeanGenerated.Step.UnweightedGraph___init___pc5 _ _ _ (by
    simp [Algo.graph_input.Algo2LeanGenerated.is_UnweightedGraph]))
  apply Reaches.prepend (Algo.graph_input.Algo2LeanGenerated.Step.UnweightedGraph___init___pc4 _ _ _ (by
    simp [Algo.graph_input.Algo2LeanGenerated.is_UnweightedGraph,Algo.graph_input.Algo2LeanGenerated.set_UnweightedGraph_size]))
  apply Reaches.prepend (Algo.graph_input.Algo2LeanGenerated.Step.UnweightedGraph___init___pc3 _ _ _ (by
    simp [Algo.graph_input.Algo2LeanGenerated.is_UnweightedGraph,Algo.graph_input.Algo2LeanGenerated.set_UnweightedGraph_size,
      Algo.graph_input.Algo2LeanGenerated.set_UnweightedGraph_adj]))
  apply Reaches.prepend (Algo.graph_input.Algo2LeanGenerated.Step.UnweightedGraph___init___pc2 _ _ _)
  apply Reaches.prepend (Algo.graph_input.Algo2LeanGenerated.Step.UnweightedGraph___init___pc1 _ _ _)
  apply Reaches.prepend (Algo.graph_input.Algo2LeanGenerated.Step.UnweightedGraph_pc2 _ _ _)
  apply Reaches.prepend (Algo.graph_input.Algo2LeanGenerated.Step.UnweightedGraph_pc1 _ _ _ (constructor_valid h n adj degree))
  exact Reaches.refl _


def prepared (h : Heap) (n : Nat) : Heap := (initHeap h n).tick "graph_work" 1

def finished (h : Heap) (g : Graph) : Heap :=
  (outerHeap (prepared h g.size) (h.nextRef+2) (h.nextRef+1) g g.size).tick "graph_work" 1

def finalHeap (h : Heap) (g : Graph) : Heap :=
  constructorHeap (finished h g) g.size h.nextCollection (h.nextRef+1)

theorem finished_preserves (h : Heap) (g : Graph) : Preserves h (finished h g) := by
  apply preserves_trans _ (preserves_tick _ 1)
  apply outer_preserves (preserves_trans (init_preserves h g.size) (preserves_tick _ 1))
  · omega
  · omega

theorem finished_rows (h : Heap) (g : Graph) :
    Rows (finished h g) (h.nextRef+2) g.size h.nextCollection (h.nextRef+1) (outerData g g.size) :=
  (outer_rows ((initial_rows h g.size).tick 1) g.size (le_refl _)).tick 1

theorem complete_call (h : Heap) (graph : ObjectRef) (g : Graph) (hg : GraphRep h graph g) :
    Algo.scc.transpose.Call h graph (finalHeap h g) (finished h g).nextObject := by
  refine ⟨hg.1,?_⟩
  intro stack
  obtain ⟨si,si0,si1,si2,si3,init⟩ := init_execution h graph g hg g.size (le_refl _) stack
  have gs : field__a2l_import_0_UnweightedGraph_size (initHeap h g.size) si.v0 = some (g.size : Int) := by
    rw [si0]; exact (graph_preserved (init_preserves h g.size) hg).2.1
  have cond : decide (si.v3 < (field__a2l_import_0_UnweightedGraph_size (initHeap h g.size) si.v0).getD 0) = false := by
    simp [gs,si3]
  let so : State_transpose := {si with t13 := false, v3 := 0}
  have rows : Rows (prepared h g.size) (h.nextRef+2) g.size so.v1 so.v2 (fun _ => []) := by
    simpa only [prepared,so,si1,si2] using (initial_rows h g.size).tick 1
  obtain ⟨sf,f0,f1,f2,f3,outer⟩ := outer_run h (prepared h g.size) g (h.nextRef+2) so
    (by simpa only [so,si0] using hg) (preserves_trans (init_preserves h g.size) (preserves_tick _ 1))
    rows (by omega) (by simp only [so,si2]; omega) rfl g.size (le_refl _) stack
  have outer' : Reaches Step (.active (prepared h g.size) (Frame.fn_transpose 8 so) stack)
      (.active (outerHeap (prepared h g.size) (h.nextRef+2) (h.nextRef+1) g g.size) (Frame.fn_transpose 8 sf) stack) := by
    simpa only [so,si2] using outer
  have fgraph : sf.v0 = graph := f0.trans si0
  have fadj : sf.v1 = h.nextCollection := f1.trans si1
  have fdeg : sf.v2 = h.nextRef+1 := f2.trans si2
  let doneLoop := outerHeap (prepared h g.size) (h.nextRef+2) (h.nextRef+1) g g.size
  have ploop : Preserves h doneLoop := outer_preserves
    (preserves_trans (init_preserves h g.size) (preserves_tick _ 1)) _ _ g (by omega) (by omega) g.size
  have sizeLoop : field__a2l_import_0_UnweightedGraph_size doneLoop sf.v0 = some (g.size : Int) := by
    rw [fgraph]; exact (graph_preserved ploop hg).2.1
  have noMore : decide (sf.v3 < (field__a2l_import_0_UnweightedGraph_size doneLoop sf.v0).getD 0) = false := by
    simp [sizeLoop,f3]
  have sizeEnd : field__a2l_import_0_UnweightedGraph_size (finished h g) sf.v0 = some (g.size : Int) := by
    rw [fgraph]; exact (graph_preserved (finished_preserves h g) hg).2.1
  refine init.trans ?_
  apply Reaches.prepend (Step.transpose_pc26 _ _ _ (by simp [gs]))
  apply Reaches.prepend (Step.transpose_pc25_false _ _ _ cond)
  apply Reaches.prepend (Step.transpose_pc24 _ _ _)
  apply Reaches.prepend (Step.transpose_pc23 _ _ _)
  have cond' : decide ((g.size : Int) < (field__a2l_import_0_UnweightedGraph_size (initHeap h g.size) si.v0).getD 0) = false := by simpa only [si3] using cond
  have startRun : Reaches Step
      (.active (prepared h g.size) (Frame.fn_transpose 8 so) stack)
      (resumeConfig (finalHeap h g) (Result.fn_transpose (finished h g).nextObject) stack) := by
    apply outer'.trans
    apply Reaches.prepend (Step.transpose_pc8 _ _ _ (by simpa only [doneLoop,Option.isSome_some] using congrArg Option.isSome sizeLoop))
    apply Reaches.prepend (Step.transpose_pc7_false _ _ _ noMore)
    apply Reaches.prepend (Step.transpose_pc6 _ _ _)
    apply Reaches.prepend (Step.transpose_pc5 _ _ _ (by simpa only [finished,doneLoop,Option.isSome_some] using congrArg Option.isSome sizeEnd))
    apply Reaches.prepend (Step.transpose_pc4 _ _ _)
    apply Reaches.prepend (Step.transpose_pc3 _ _ _)
    apply Reaches.prepend (Step.transpose_pc2 _ _ _)
    let sr : ObjectRef → State_transpose := fun result =>
      {sf with t11 := false, t8 := g.size, t9 := h.nextCollection, t10 := h.nextRef+1, t7 := result}
    have call := constructor_call (finished h g) g.size h.nextCollection (h.nextRef+1)
      (finished_rows h g).valid (finished_rows h g).degreeValid
    have lifted := ModuleCall.summary import_0_simulates
      (fun value => match value with
        | .fn_UnweightedGraph result => Frame.fn_transpose 1 (sr result)
        | _ => .invalid) stack call.2
    have tailRun := Reaches.single (Step.transpose_pc1 (finalHeap h g)
      (sr (finished h g).nextObject) stack (constructor_valid (finished h g) g.size h.nextCollection (h.nextRef+1)))
    have noMore' : decide ((g.size : Int) < (field__a2l_import_0_UnweightedGraph_size doneLoop sf.v0).getD 0) = false := by simpa only [f3] using noMore
    convert lifted.trans tailRun using 1 <;>
      simp only [sr,finished,finalHeap,doneLoop,Algo.graph_input.entry_UnweightedGraph,
        size_tick,sizeLoop,Option.getD_some,fadj,fdeg,f3,noMore',decide_eq_false_iff_not,lt_self_iff_false,
        decide_false]
    all_goals rfl
  simpa only [prepared,so,cond',si3] using startRun

theorem complete_post (h : Heap) (g : Graph) :
    TransposePost h (finalHeap h g) (finished h g).nextObject g := by
  let rows := finished_rows h g
  let t : Graph := ⟨g.size,outerData g g.size,rows.bounded⟩
  have pf := finished_preserves h g
  refine ⟨⟨pf.objectAllocation,?_⟩,preserves_trans pf (constructor_preserves _ _ _ _),t,
    constructor_rep rows,⟨rfl,?_⟩,?_⟩
  · change (finished h g).nextObject < (finished h g).nextObject+1
    exact Nat.lt_succ_self _
  · intro u v hu hv
    change (outerData g g.size u).count v = _
    rw [outer_count,if_pos hv]
  · change mass g.size (outerData g g.size) = edgeCount g
    exact outer_mass g g.size (le_refl _)

theorem complete_work (h : Heap) (g : Graph) :
    work h (finalHeap h g) = 4+5*g.size+2*edgeCount g := by
  have clock : (finalHeap h g).clocks "graph_work" =
      h.clocks "graph_work" + 4+5*g.size+2*edgeCount g := by
    change (finished h g).clocks "graph_work" = _
    rw [finished,Heap.clocks_tick_same,outer_clock]
    change (initHeap h g.size).clocks "graph_work" + 1 + 3*g.size + 2*edgePrefix g g.size + 1 = _
    rw [(init_meta h g.size).2.2.2.2]
    change h.clocks "graph_work" + 2+2*g.size+1+3*g.size+2*edgeCount g+1 = _
    omega
  simp only [work,Heap.cost,clock]; omega

end TransposeProof

open TransposeProof

theorem solution :
    ∃ C : Nat, 0 < C ∧
      ∀ (before : Heap) (graph : ObjectRef) (g : Graph),
        GraphRep before graph g →
        ∃ after result,
          Algo.scc.transpose.Call before graph after result ∧
          TransposePost before after result g ∧
          work before after ≤ C * (1 + g.size + edgeCount g) := by
  refine ⟨5,by omega,?_⟩
  intro before graph g represented
  refine ⟨finalHeap before g,(finished before g).nextObject,
    complete_call before graph g represented,complete_post before g,?_⟩
  rw [complete_work]
  omega
