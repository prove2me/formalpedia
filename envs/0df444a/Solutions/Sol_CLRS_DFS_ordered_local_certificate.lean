-- Prove2me | solution 1 for CLRS.DFS.ordered_local_certificate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T03:56:13.881461+00:00
-- url     : https://prove2.me/submissions/a6fa9f24-3b24-411c-8b1d-c9bcd7cfc546

import Theorems.Thm_CLRS_DFS_pure_execution_certificate
import Mathlib.Data.List.Range
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 1000000
open Algo2LeanGenerated CLRS.GraphTraversal CLRS.DFS CLRS.DFS.Pure
open Algo.dfs.Algo2LeanGenerated Algo2LeanCore

namespace DFSSim

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



def ref (before : Heap) (i : Fin 6) : SeqRef := before.nextRef + i.val

def arrField : Fin 6 → Heap → ObjectRef → Option SeqRef
  | 0 => field_DFSResult_color
  | 1 => field_DFSResult_parent
  | 2 => field_DFSResult_discover
  | 3 => field_DFSResult_finish
  | 4 => field_DFSResult_order
  | 5 => field_DFSResult_component

@[simp] theorem arr_tick (i : Fin 6) (h : Heap) (r : ObjectRef) (k : Nat) :
    arrField i (h.tick "graph_work" k) r = arrField i h r := by fin_cases i <;> rfl
@[simp] theorem arr_write (i : Fin 6) (h : Heap) (r a : Nat) (u v : Int) :
    arrField i (h.write a u v) r = arrField i h r := by fin_cases i <;> rfl
@[simp] theorem result_set (h : Heap) (r : ObjectRef) (name : String) (v : ObjectValue) :
    is_DFSResult (h.writeField r name v) r ↔ is_DFSResult h r := by simp [is_DFSResult]

@[simp] theorem class_tick (h : Heap) (r : ObjectRef) (k : Nat) :
    (h.tick "graph_work" k).objectClass r = h.objectClass r := rfl
@[simp] theorem class_allocate (h : Heap) (r : ObjectRef) (a : Seq) :
    (h.allocate a).objectClass r = h.objectClass r := rfl
@[simp] theorem readField_tick (h : Heap) (r : ObjectRef) (f : String) (k : Nat) :
    (h.tick "graph_work" k).readField r f = h.readField r f := rfl
@[simp] theorem readField_allocate (h : Heap) (r : ObjectRef) (f : String) (a : Seq) :
    (h.allocate a).readField r f = h.readField r f := rfl
@[simp] theorem clock_set_nr (h : Heap) (r : ObjectRef) (v : Int) :
    (set_DFSResult_clock h r v).nextRef = h.nextRef := rfl

@[simp] theorem class_new_tick (h : Heap) (name : String) :
    ((h.tick "graph_work" 1).allocateObject name).objectClass h.nextObject = some name := by
  simpa only [Heap.tick_nextObject] using Heap.objectClass_allocateObject_new (h.tick "graph_work" 1) name
@[simp] theorem read_write_field_known (h : Heap) (r : ObjectRef) (f : String) (v : ObjectValue)
    (present : h.objectClass r = some "dfs.DFSResult") :
    (h.writeField r f v).readField r f = some v := Heap.readField_writeField_same h r f v _ present

structure Rep (before h : Heap) (a : Pure.State) : Prop where
  preserves : Preserves before h
  nr : h.nextRef = before.nextRef + 6
  no : h.nextObject = before.nextObject + 1
  valid : is_DFSResult h before.nextObject
  fields : ∀ i, arrField i h before.nextObject = some (ref before i)
  clock : field_DFSResult_clock h before.nextObject = some a.clock
  finished : field_DFSResult_finished h before.nextObject = some a.finished
  count : field_DFSResult_components h before.nextObject = some a.count
  arrays : ∀ i, h.read (ref before i) = a.arrays i

theorem Rep.allocated {before h : Heap} {a : Pure.State} (r : Rep before h a) (i : Fin 6) :
    ref before i < h.nextRef := by rw [r.nr]; exact Nat.add_lt_add_left i.isLt _

theorem Rep.tick {before h : Heap} {a : Pure.State} (r : Rep before h a) (k : Nat) :
    Rep before (h.tick "graph_work" k) a := by
  exact ⟨preserves_trans r.preserves (preserves_tick _ _),r.nr,r.no,r.valid,(by simpa using r.fields),
    r.clock,r.finished,r.count,r.arrays⟩

theorem Rep.write {before h : Heap} {a : Pure.State} (r : Rep before h a)
    (i : Fin 6) (u v : Int) :
    Rep before (h.write (ref before i) u v) (Pure.write a i u v) := by
  refine ⟨preserves_write r.preserves _ (by simp [ref]) _ _,r.nr,r.no,r.valid,(by simpa using r.fields),
    r.clock,r.finished,r.count,?_⟩
  intro j
  by_cases eq : j = i
  · subst j; funext w
    by_cases same : w = u
    · subst w; simp [Pure.write]
    · simp [Heap.read_write_other_index, same, Pure.write, Function.update, r.arrays]
  · have ne : ref before j ≠ ref before i := by
      simp only [ref,ne_eq,Nat.add_left_cancel_iff,Fin.val_inj]; exact eq
    rw [show (Pure.write a i u v).arrays j = a.arrays j by simp [Pure.write,Function.update,eq]]
    funext w
    rw [Heap.read_write_other_ref _ _ _ _ _ _ ne,r.arrays]

theorem preserves_field {before h : Heap} (p : Preserves before h) (name : String)
    (value : ObjectValue) : Preserves before (h.writeField before.nextObject name value) := by
  constructor
  · exact p.sequences
  · intro obj ho
    have ne : obj ≠ before.nextObject := Nat.ne_of_lt ho
    simpa [Heap.writeField,ne] using p.objects obj ho
  · exact p.collections
  · exact p.sequenceAllocation
  · exact p.objectAllocation
  · exact p.collectionAllocation
  · exact p.workMonotone
  · exact p.otherClocks

theorem Rep.set_clock {before h : Heap} {a : Pure.State} (r : Rep before h a) (v : Int) :
    Rep before (set_DFSResult_clock h before.nextObject v) {a with clock := v} := by
  have valid : is_DFSResult (set_DFSResult_clock h before.nextObject v) before.nextObject := by
    simpa [is_DFSResult,set_DFSResult_clock] using r.valid
  refine ⟨preserves_field r.preserves _ _,r.nr,r.no,valid,?_,?_,?_,?_,r.arrays⟩
  · intro i
    fin_cases i
    · simpa [arrField,field_DFSResult_color,r.valid,set_DFSResult_clock] using r.fields (0 : Fin 6)
    · simpa [arrField,field_DFSResult_parent,r.valid,set_DFSResult_clock] using r.fields (1 : Fin 6)
    · simpa [arrField,field_DFSResult_discover,r.valid,set_DFSResult_clock] using r.fields (2 : Fin 6)
    · simpa [arrField,field_DFSResult_finish,r.valid,set_DFSResult_clock] using r.fields (3 : Fin 6)
    · simpa [arrField,field_DFSResult_order,r.valid,set_DFSResult_clock] using r.fields (4 : Fin 6)
    · simpa [arrField,field_DFSResult_component,r.valid,set_DFSResult_clock] using r.fields (5 : Fin 6)
  · exact field_DFSResult_clock_set h before.nextObject v r.valid
  · simpa [field_DFSResult_finished,valid,r.valid,set_DFSResult_clock] using r.finished
  · simpa [field_DFSResult_components,valid,r.valid,set_DFSResult_clock] using r.count
theorem Rep.set_finished {before h : Heap} {a : Pure.State} (r : Rep before h a) (v : Int) :
    Rep before (set_DFSResult_finished h before.nextObject v) {a with finished := v} := by
  have valid : is_DFSResult (set_DFSResult_finished h before.nextObject v) before.nextObject := by
    simpa [is_DFSResult,set_DFSResult_finished] using r.valid
  refine ⟨preserves_field r.preserves _ _,r.nr,r.no,valid,?_,?_,?_,?_,r.arrays⟩
  · intro i
    fin_cases i
    · simpa [arrField,field_DFSResult_color,r.valid,set_DFSResult_finished] using r.fields (0 : Fin 6)
    · simpa [arrField,field_DFSResult_parent,r.valid,set_DFSResult_finished] using r.fields (1 : Fin 6)
    · simpa [arrField,field_DFSResult_discover,r.valid,set_DFSResult_finished] using r.fields (2 : Fin 6)
    · simpa [arrField,field_DFSResult_finish,r.valid,set_DFSResult_finished] using r.fields (3 : Fin 6)
    · simpa [arrField,field_DFSResult_order,r.valid,set_DFSResult_finished] using r.fields (4 : Fin 6)
    · simpa [arrField,field_DFSResult_component,r.valid,set_DFSResult_finished] using r.fields (5 : Fin 6)
  · simpa [field_DFSResult_clock,valid,r.valid,set_DFSResult_finished] using r.clock
  · exact field_DFSResult_finished_set h before.nextObject v r.valid
  · simpa [field_DFSResult_components,valid,r.valid,set_DFSResult_finished] using r.count
theorem Rep.set_count {before h : Heap} {a : Pure.State} (r : Rep before h a) (v : Int) :
    Rep before (set_DFSResult_components h before.nextObject v) {a with count := v} := by
  have valid : is_DFSResult (set_DFSResult_components h before.nextObject v) before.nextObject := by
    simpa [is_DFSResult,set_DFSResult_components] using r.valid
  refine ⟨preserves_field r.preserves _ _,r.nr,r.no,valid,?_,?_,?_,?_,r.arrays⟩
  · intro i
    fin_cases i
    · simpa [arrField,field_DFSResult_color,r.valid,set_DFSResult_components] using r.fields (0 : Fin 6)
    · simpa [arrField,field_DFSResult_parent,r.valid,set_DFSResult_components] using r.fields (1 : Fin 6)
    · simpa [arrField,field_DFSResult_discover,r.valid,set_DFSResult_components] using r.fields (2 : Fin 6)
    · simpa [arrField,field_DFSResult_finish,r.valid,set_DFSResult_components] using r.fields (3 : Fin 6)
    · simpa [arrField,field_DFSResult_order,r.valid,set_DFSResult_components] using r.fields (4 : Fin 6)
    · simpa [arrField,field_DFSResult_component,r.valid,set_DFSResult_components] using r.fields (5 : Fin 6)
  · simpa [field_DFSResult_clock,valid,r.valid,set_DFSResult_components] using r.clock
  · simpa [field_DFSResult_finished,valid,r.valid,set_DFSResult_components] using r.finished
  · exact field_DFSResult_components_set h before.nextObject v r.valid
def enterHeap (before h : Heap) (a : Pure.State) (u label : Int) : Heap :=
  (((set_DFSResult_clock (h.tick "graph_work" 1) before.nextObject (a.clock+1)).write
    (ref before 2) u (a.clock+1)).write (ref before 0) u 1).write (ref before 5) u label

def leaveHeap (before h : Heap) (a : Pure.State) (u : Int) : Heap :=
  set_DFSResult_finished
    (((set_DFSResult_clock ((h.tick "graph_work" 1).write (ref before 0) u 2)
      before.nextObject (a.clock+1)).write (ref before 3) u (a.clock+1)).write
        (ref before 4) a.finished u) before.nextObject (a.finished+1)

theorem enter_rep {before h : Heap} {a : Pure.State} (r : Rep before h a) (u label : Int) :
    Rep before (enterHeap before h a u label) (enter a u label) :=
  (((((r.tick 1).set_clock (a.clock+1)).write 2 u (a.clock+1)).write 0 u 1).write 5 u label)

theorem leave_rep {before h : Heap} {a : Pure.State} (r : Rep before h a) (u : Int) :
    Rep before (leaveHeap before h a u) (leave a u) :=
  (((((r.tick 1).write 0 u 2).set_clock (a.clock+1)).write 3 u (a.clock+1)).write 4 a.finished u).set_finished (a.finished+1)

@[simp] theorem color_tick (h : Heap) (r : ObjectRef) (k : Nat) :
    field_DFSResult_color (h.tick "graph_work" k) r = field_DFSResult_color h r := rfl
@[simp] theorem color_write (h : Heap) (r : ObjectRef) (ref : SeqRef) (i v : Int) :
    field_DFSResult_color (h.write ref i v) r = field_DFSResult_color h r := rfl
@[simp] theorem color_allocate (h : Heap) (r : ObjectRef) (a : Seq) :
    field_DFSResult_color (h.allocate a) r = field_DFSResult_color h r := rfl
@[simp] theorem parent_tick (h : Heap) (r : ObjectRef) (k : Nat) :
    field_DFSResult_parent (h.tick "graph_work" k) r = field_DFSResult_parent h r := rfl
@[simp] theorem parent_write (h : Heap) (r : ObjectRef) (ref : SeqRef) (i v : Int) :
    field_DFSResult_parent (h.write ref i v) r = field_DFSResult_parent h r := rfl
@[simp] theorem parent_allocate (h : Heap) (r : ObjectRef) (a : Seq) :
    field_DFSResult_parent (h.allocate a) r = field_DFSResult_parent h r := rfl
@[simp] theorem discover_tick (h : Heap) (r : ObjectRef) (k : Nat) :
    field_DFSResult_discover (h.tick "graph_work" k) r = field_DFSResult_discover h r := rfl
@[simp] theorem discover_write (h : Heap) (r : ObjectRef) (ref : SeqRef) (i v : Int) :
    field_DFSResult_discover (h.write ref i v) r = field_DFSResult_discover h r := rfl
@[simp] theorem discover_allocate (h : Heap) (r : ObjectRef) (a : Seq) :
    field_DFSResult_discover (h.allocate a) r = field_DFSResult_discover h r := rfl
@[simp] theorem finish_tick (h : Heap) (r : ObjectRef) (k : Nat) :
    field_DFSResult_finish (h.tick "graph_work" k) r = field_DFSResult_finish h r := rfl
@[simp] theorem finish_write (h : Heap) (r : ObjectRef) (ref : SeqRef) (i v : Int) :
    field_DFSResult_finish (h.write ref i v) r = field_DFSResult_finish h r := rfl
@[simp] theorem finish_allocate (h : Heap) (r : ObjectRef) (a : Seq) :
    field_DFSResult_finish (h.allocate a) r = field_DFSResult_finish h r := rfl
@[simp] theorem order_tick (h : Heap) (r : ObjectRef) (k : Nat) :
    field_DFSResult_order (h.tick "graph_work" k) r = field_DFSResult_order h r := rfl
@[simp] theorem order_write (h : Heap) (r : ObjectRef) (ref : SeqRef) (i v : Int) :
    field_DFSResult_order (h.write ref i v) r = field_DFSResult_order h r := rfl
@[simp] theorem order_allocate (h : Heap) (r : ObjectRef) (a : Seq) :
    field_DFSResult_order (h.allocate a) r = field_DFSResult_order h r := rfl
@[simp] theorem component_tick (h : Heap) (r : ObjectRef) (k : Nat) :
    field_DFSResult_component (h.tick "graph_work" k) r = field_DFSResult_component h r := rfl
@[simp] theorem component_write (h : Heap) (r : ObjectRef) (ref : SeqRef) (i v : Int) :
    field_DFSResult_component (h.write ref i v) r = field_DFSResult_component h r := rfl
@[simp] theorem component_allocate (h : Heap) (r : ObjectRef) (a : Seq) :
    field_DFSResult_component (h.allocate a) r = field_DFSResult_component h r := rfl
@[simp] theorem clock_tick (h : Heap) (r : ObjectRef) (k : Nat) :
    field_DFSResult_clock (h.tick "graph_work" k) r = field_DFSResult_clock h r := rfl
@[simp] theorem clock_write (h : Heap) (r : ObjectRef) (ref : SeqRef) (i v : Int) :
    field_DFSResult_clock (h.write ref i v) r = field_DFSResult_clock h r := rfl
@[simp] theorem clock_allocate (h : Heap) (r : ObjectRef) (a : Seq) :
    field_DFSResult_clock (h.allocate a) r = field_DFSResult_clock h r := rfl
@[simp] theorem finished_tick (h : Heap) (r : ObjectRef) (k : Nat) :
    field_DFSResult_finished (h.tick "graph_work" k) r = field_DFSResult_finished h r := rfl
@[simp] theorem finished_write (h : Heap) (r : ObjectRef) (ref : SeqRef) (i v : Int) :
    field_DFSResult_finished (h.write ref i v) r = field_DFSResult_finished h r := rfl
@[simp] theorem finished_allocate (h : Heap) (r : ObjectRef) (a : Seq) :
    field_DFSResult_finished (h.allocate a) r = field_DFSResult_finished h r := rfl
@[simp] theorem components_tick (h : Heap) (r : ObjectRef) (k : Nat) :
    field_DFSResult_components (h.tick "graph_work" k) r = field_DFSResult_components h r := rfl
@[simp] theorem components_write (h : Heap) (r : ObjectRef) (ref : SeqRef) (i v : Int) :
    field_DFSResult_components (h.write ref i v) r = field_DFSResult_components h r := rfl
@[simp] theorem components_allocate (h : Heap) (r : ObjectRef) (a : Seq) :
    field_DFSResult_components (h.allocate a) r = field_DFSResult_components h r := rfl
@[simp] theorem get_tick (h : Heap) (r : CollectionRef) (i : Int) (k : Nat) :
    seq_Seq_Int.get (h.tick "graph_work" k) r i = seq_Seq_Int.get h r i := rfl

theorem Rep.color {before h : Heap} {a : Pure.State} (r : Rep before h a) :
    field_DFSResult_color h before.nextObject = some (ref before 0) := r.fields 0
theorem Rep.parent {before h : Heap} {a : Pure.State} (r : Rep before h a) :
    field_DFSResult_parent h before.nextObject = some (ref before 1) := r.fields 1
theorem Rep.discover {before h : Heap} {a : Pure.State} (r : Rep before h a) :
    field_DFSResult_discover h before.nextObject = some (ref before 2) := r.fields 2
theorem Rep.finish {before h : Heap} {a : Pure.State} (r : Rep before h a) :
    field_DFSResult_finish h before.nextObject = some (ref before 3) := r.fields 3
theorem Rep.order {before h : Heap} {a : Pure.State} (r : Rep before h a) :
    field_DFSResult_order h before.nextObject = some (ref before 4) := r.fields 4
theorem Rep.component {before h : Heap} {a : Pure.State} (r : Rep before h a) :
    field_DFSResult_component h before.nextObject = some (ref before 5) := r.fields 5

theorem enter_execution (before h : Heap) (graph : ObjectRef) (g : Graph) (a : Pure.State)
    (r : Rep before h a) (hg : GraphRep before graph g) (u label : Int) (uv : Vertex g u)
    (stack : Stack) :
    ∃ s : State_visit, s.v0 = graph ∧ s.v1 = before.nextObject ∧ s.v2 = u ∧ s.v3 = label ∧
      s.v5 = 0 ∧ s.v4 < before.nextRef ∧
      (∀ j : Nat, j < (g.neighbors u.toNat).length →
        before.read s.v4 j = ((g.neighbors u.toNat)[j]! : Int)) ∧
      Reaches Step (.active h (Frame.fn_visit 40 {v0 := graph,v1 := before.nextObject,v2 := u,v3 := label}) stack)
        (.active ((enterHeap before h a u label).tick "graph_work" 1) (Frame.fn_visit 16 s) stack) := by
  obtain ⟨adj,deg,ha,hd,hav,hdv,rows⟩ := hg.2.2
  obtain ⟨du,row,getr,rv,vals⟩ := rows u.toNat (by rcases uv with ⟨_,_⟩; omega)
  have getr' : seq_Seq_Int.get (enterHeap before h a u label) adj u = some row := by
    change GI.get (enterHeap before h a u label) adj u = some row
    have col := (enter_rep r u label).preserves.collections adj hav.1
    have val : GI.valid (enterHeap before h a u label) adj :=
      ⟨lt_of_lt_of_le hav.1 (enter_rep r u label).preserves.collectionAllocation,
        by simpa [Heap.sequenceType,col] using hav.2⟩
    simpa [SequenceType.get,Heap.readElement,col,hav,val,Int.toNat_of_nonneg uv.1] using getr
  let s : State_visit := {v0 := graph,v1 := before.nextObject,v2 := u,v3 := label, v4 := row,v5 := 0,t21 := before.nextObject,t22 := a.clock,t23 := 1}
  refine ⟨s,rfl,rfl,rfl,rfl,rfl,rv,vals,?_⟩
  have r1 := (r.tick 1).set_clock (a.clock+1)
  have r2 := r1.write 2 u (a.clock+1)
  have r3 := r2.write 0 u 1
  have r4 := r3.write 5 u label
  have ha' := (graph_preserved r4.preserves hg).2.2
  have adj' : field__a2l_import_0_UnweightedGraph_adj (enterHeap before h a u label) graph = some adj := by
    change Algo.graph_input.Algo2LeanGenerated.field_UnweightedGraph_adj _ _ = _
    rw [Algo.graph_input.Algo2LeanGenerated.field_UnweightedGraph_adj,
      if_pos (graph_preserved (enter_rep r u label).preserves hg).1]
    simpa only [Algo.graph_input.Algo2LeanGenerated.field_UnweightedGraph_adj,if_pos hg.1,
      Heap.readField,(enter_rep r u label).preserves.objects graph hg.1.1] using ha
  apply Reaches.prepend (Step.visit_pc40 _ _ _)
  apply Reaches.prepend (Step.visit_pc39 _ _ _)
  apply Reaches.prepend (Step.visit_pc38 _ _ _ (by simp [r.clock]))
  apply Reaches.prepend (Step.visit_pc37 _ _ _)
  apply Reaches.prepend (Step.visit_pc36 _ _ _ r.valid)
  simp only [clock_tick,r.clock,Option.getD_some]
  apply Reaches.prepend (Step.visit_pc35 _ _ _ (by simp [r1.clock,r1.discover,r.nr,ref]))
  simp only [r1.clock,r1.discover,Option.getD_some]
  apply Reaches.prepend (Step.visit_pc34 _ _ _ (by simp only [color_write,r1.color,Option.isSome_some,Option.getD_some,true_and,Heap.write_nextRef]; exact r1.allocated 0))
  simp only [r2.color,Option.getD_some]
  apply Reaches.prepend (Step.visit_pc33 _ _ _ (by simp only [component_write,r1.component,Option.isSome_some,Option.getD_some,true_and,Heap.write_nextRef]; exact r1.allocated 5))
  simp only [r3.component,Option.getD_some]
  change Reaches Step (.active (enterHeap before h a u label)
    (Frame.fn_visit 32 {v0 := graph,v1 := before.nextObject,v2 := u,v3 := label, t21 := before.nextObject,t22 := a.clock,t23 := 1}) stack) _
  apply Reaches.prepend (Step.visit_pc32 _ _ _ (by simp [adj',getr']))
  apply Reaches.prepend (Step.visit_pc31 _ _ _)
  apply Reaches.prepend (Step.visit_pc30 _ _ _)
  simpa [s,adj',getr'] using Reaches.refl (step:=Step)
    (.active ((enterHeap before h a u label).tick "graph_work" 1) (Frame.fn_visit 16 s) stack)

theorem leave_execution (before h : Heap) (a : Pure.State) (r : Rep before h a)
    (s : State_visit) (sr : s.v1 = before.nextObject) (u : Int) (su : s.v2 = u) (stack : Stack) :
    Reaches Step (.active h (Frame.fn_visit 14 s) stack)
      (resumeConfig (leaveHeap before h a u) (.fn_visit ()) stack) := by
  have r1 := (r.tick 1).write 0 u 2
  have r2 := r1.set_clock (a.clock+1)
  have r3 := r2.write 3 u (a.clock+1)
  have r4 := r3.write 4 a.finished u
  have fo : field_DFSResult_order (set_DFSResult_clock ((h.tick "graph_work" 1).write (ref before 0) u 2) before.nextObject (a.clock+1)) before.nextObject = some (ref before 4) := r2.order
  have ff : field_DFSResult_finished (set_DFSResult_clock ((h.tick "graph_work" 1).write (ref before 0) u 2) before.nextObject (a.clock+1)) before.nextObject = some a.finished := r2.finished
  apply Reaches.prepend (Step.visit_pc14 _ _ _)
  apply Reaches.prepend (Step.visit_pc13 _ _ _ (by simp [sr,r.color,r.allocated 0]))
  simp only [sr,su,color_tick,r.color,Option.getD_some]
  apply Reaches.prepend (Step.visit_pc12 _ _ _)
  apply Reaches.prepend (Step.visit_pc11 _ _ _ (by simpa only [sr,su] using (show (field_DFSResult_clock _ before.nextObject).isSome = true by rw [r1.clock]; rfl)))
  apply Reaches.prepend (Step.visit_pc10 _ _ _)
  apply Reaches.prepend (Step.visit_pc9 _ _ _ (by simpa only [sr,su] using r1.valid))
  simp only [sr,su,clock_write,clock_tick,r.clock,Option.getD_some]
  apply Reaches.prepend (Step.visit_pc8 _ _ _ (by simp only [r2.clock,r2.finish,Option.isSome_some,Option.getD_some,true_and]; exact r2.allocated 3))
  simp only [r2.clock,r2.finish,Option.getD_some]
  apply Reaches.prepend (Step.visit_pc7 _ _ _ (by simp only [order_write,finished_write,fo,ff,Option.isSome_some,Option.getD_some,true_and,Heap.write_nextRef]; exact r2.allocated 4))
  simp only [order_write,finished_write,fo,ff,Option.getD_some]
  apply Reaches.prepend (Step.visit_pc6 _ _ _)
  apply Reaches.prepend (Step.visit_pc5 _ _ _ (by simp [ff]))
  simp only [finished_write,ff,Option.getD_some]
  apply Reaches.prepend (Step.visit_pc4 _ _ _)
  apply Reaches.prepend (Step.visit_pc3 _ _ _ r4.valid)
  apply Reaches.prepend (Step.visit_pc2 _ _ _)
  apply Reaches.prepend (Step.visit_pc1 _ _ _)
  simpa only [finished_write,ff,Option.getD_some,leaveHeap] using
    Reaches.refl (step:=Step) (resumeConfig (leaveHeap before h a u) (.fn_visit ()) stack)


def Execution (before : Heap) (graph : ObjectRef) (g : Graph) (q : SeqRef) (input : List Int)
    (task : Task) (h h' : Heap) : Prop :=
  match task with
  | .visit u label => ∀ stack,
      Reaches Step (.active h (Frame.fn_visit 40 {v0 := graph,v1 := before.nextObject,v2 := u,v3 := label}) stack)
        (resumeConfig h' (.fn_visit ()) stack)
  | .scan u label vs => ∀ (s : State_visit) (pre : List Nat) (stack : Stack),
      s.v0 = graph → s.v1 = before.nextObject → s.v2 = u → s.v3 = label →
      s.v5 = (pre.length : Int) → Vertex g u → g.neighbors u.toNat = pre ++ vs →
      s.v4 < before.nextRef →
      (∀ j : Nat, j < (g.neighbors u.toNat).length → before.read s.v4 j = ((g.neighbors u.toNat)[j]! : Int)) →
      ∃ sf : State_visit, sf.v0 = graph ∧ sf.v1 = before.nextObject ∧ sf.v2 = u ∧ sf.v3 = label ∧
        Reaches Step (.active h (Frame.fn_visit 16 s) stack) (.active h' (Frame.fn_visit 14 sf) stack)
  | .roots vs => ∀ (s : State_dfs_ordered) (pre : List Int) (stack : Stack),
      s.v0 = graph → s.v1 = q → s.v2 = before.nextObject → s.v3 = (pre.length : Int) →
      input = pre ++ vs →
      ∃ sf : State_dfs_ordered, sf.v2 = before.nextObject ∧
        Reaches Step (.active h (Frame.fn_dfs_ordered 5 s) stack)
          (.active h' (Frame.fn_dfs_ordered 3 sf) stack)

def Realizes (before : Heap) (graph : ObjectRef) (g : Graph) (q : SeqRef) (input : List Int)
    (task : Task) (a b : Pure.State) (k : Nat) : Prop :=
  ∀ h, Rep before h a → ∃ h', Rep before h' b ∧
    h'.clocks "graph_work" = h.clocks "graph_work" + k ∧
    Execution before graph g q input task h h'

theorem scan_info (before h : Heap) (graph : ObjectRef) (g : Graph) (a : Pure.State)
    (r : Rep before h a) (hg : GraphRep before graph g) (u : Int) (uv : Vertex g u) :
    ∃ deg, field__a2l_import_0_UnweightedGraph_degree h graph = some deg ∧
      deg < h.nextRef ∧ h.read deg u = ((g.neighbors u.toNat).length : Int) := by
  obtain ⟨adj,deg,ha,hd,hav,hdv,rows⟩ := (graph_preserved r.preserves hg).2.2
  refine ⟨deg,hd,hdv,?_⟩
  have v := (rows u.toNat (by rcases uv with ⟨_,_⟩; omega)).1
  simpa only [Int.toNat_of_nonneg uv.1] using v

theorem realizes (before : Heap) (graph : ObjectRef) (g : Graph) (q : SeqRef) (input : List Int)
    (hg : GraphRep before graph g) (qa : q < before.nextRef) (len : input.length = g.size)
    (qi : ∀ i : Nat, i < g.size → before.read q i = input[i]!)
    {task : Task} {a b : Pure.State} {k : Nat} (eval : Eval g task a b k) :
    Realizes before graph g q input task a b k := by
  induction eval with
  | @visit u label a b k uv ev ih =>
    intro h r
    obtain ⟨h',r',cost,run⟩ := ih ((enterHeap before h a u label).tick "graph_work" 1) ((enter_rep r u label).tick 1)
    refine ⟨leaveHeap before h' b u,leave_rep r' u,?_,?_⟩
    · simp only [leaveHeap,set_DFSResult_finished,set_DFSResult_clock,Heap.writeField_clocks,
        Heap.write_clocks,Heap.clocks_tick_same,enterHeap] at cost ⊢
      omega
    · intro stack
      obtain ⟨s,s0,s1,s2,s3,s5,sa,sv,entry⟩ := enter_execution before h graph g a r hg u label uv stack
      obtain ⟨sf,sf0,sf1,sf2,sf3,scan⟩ := run s [] stack s0 s1 s2 s3 s5 uv rfl sa sv
      exact entry.trans (scan.trans (leave_execution before h' b r' sf sf1 u sf2 stack))
  | scan_nil u label a =>
    intro h r
    refine ⟨h,r,by omega,?_⟩
    intro s pre stack s0 s1 s2 s3 s5 uv row sa vals
    obtain ⟨deg,hd,da,dv⟩ := scan_info before h graph g a r hg u uv
    have cond : decide (s.v5 < h.read ((field__a2l_import_0_UnweightedGraph_degree h s.v0).getD 0) s.v2) = false := by
      simp only [s0,s2,hd,Option.getD_some,dv,s5,row,List.append_nil]; simp
    refine ⟨{s with t14 := false},s0,s1,s2,s3,?_⟩
    apply Reaches.prepend (Step.visit_pc16 _ _ _ (by simp [s0,hd,da]))
    apply Reaches.prepend (Step.visit_pc15_false _ _ _ cond)
    simpa only [cond] using Reaches.refl (step:=Step) (.active h (Frame.fn_visit 14 {s with t14 := false}) stack)
  | @scan_seen u label vs a b k v seen ev ih =>
    intro h r
    obtain ⟨h',r',cost,run⟩ := ih ((h.tick "graph_work" 1).tick "graph_work" 1) ((r.tick 1).tick 1)
    refine ⟨h',r',by simp only [Heap.clocks_tick_same] at cost; omega,?_⟩
    intro s pre stack s0 s1 s2 s3 s5 uv row sa vals
    obtain ⟨deg,hd,da,dv⟩ := scan_info before h graph g a r hg u uv
    have cond : decide (s.v5 < h.read ((field__a2l_import_0_UnweightedGraph_degree h s.v0).getD 0) s.v2) = true := by
      simp only [s0,s2,hd,Option.getD_some,dv,s5,row,List.length_append,List.length_cons]; simp
    have atj : h.read s.v4 s.v5 = (v : Int) := by
      rw [r.preserves.sequences s.v4 sa,s5,vals pre.length (by rw [row]; simp)]
      simp [row]
    let sn : State_visit := {s with t14 := true,t15 := false,v6 := v,v5 := s.v5+1}
    obtain ⟨sf,f0,f1,f2,f3,rest⟩ := run sn (pre++[v]) stack s0 s1 s2 s3
      (by simp [sn,s5]) uv (by rw [row]; simp) sa vals
    refine ⟨sf,f0,f1,f2,f3,?_⟩
    apply Reaches.prepend (Step.visit_pc16 _ _ _ (by simp [s0,hd,da]))
    apply Reaches.prepend (Step.visit_pc15_true _ _ _ cond)
    apply Reaches.prepend (Step.visit_pc29 _ _ _)
    apply Reaches.prepend (Step.visit_pc28 _ _ _ (by exact lt_of_lt_of_le sa r.preserves.sequenceAllocation))
    apply Reaches.prepend (Step.visit_pc27 _ _ _ (by simp [s1,r.color,r.allocated 0]))
    have test : decide (h.read (ref before 0) v = 0) = false := by rw [r.arrays]; simp [seen]
    apply Reaches.prepend (Step.visit_pc26_false _ _ _ (by simpa only [s1,color_tick,r.color,Option.getD_some,Heap.read_tick,atj] using test))
    apply Reaches.prepend (Step.visit_pc18 _ _ _)
    apply Reaches.prepend (Step.visit_pc17 _ _ _)
    have condN := cond; simp only [s0] at condN
    have atjN := atj; try simp only [s1] at atjN
    simpa only [sn,cond,condN,atjN,s1,color_tick,r.color,Option.getD_some,Heap.read_tick,atj,test] using rest
  | @scan_fresh u label vs a b c j k v fresh ev1 ev2 ih1 ih2 =>
    intro h r
    let hv := ((h.tick "graph_work" 1).tick "graph_work" 1).write (ref before 1) v u
    obtain ⟨hb,rb,cb,visitRun⟩ := ih1 hv (((r.tick 1).tick 1).write 1 v u)
    obtain ⟨hc,rc,cc,scanRun⟩ := ih2 (hb.tick "graph_work" 1) (rb.tick 1)
    refine ⟨hc,rc,?_,?_⟩
    · simp only [hv,Heap.clocks_tick_same,Heap.write_clocks] at cb cc; omega
    · intro s pre stack s0 s1 s2 s3 s5 uv row sa vals
      obtain ⟨deg,hd,da,dv⟩ := scan_info before h graph g a r hg u uv
      have cond : decide (s.v5 < h.read ((field__a2l_import_0_UnweightedGraph_degree h s.v0).getD 0) s.v2) = true := by
        simp only [s0,s2,hd,Option.getD_some,dv,s5,row,List.length_append,List.length_cons]; simp
      have atj : h.read s.v4 s.v5 = (v : Int) := by
        rw [r.preserves.sequences s.v4 sa,s5,vals pre.length (by rw [row]; simp)]; simp [row]
      have test : decide (h.read (ref before 0) v = 0) = true := by rw [r.arrays]; simp [fresh]
      let sn : State_visit := {s with t14 := true,t15 := true,v6 := v, t17 := graph,t18 := before.nextObject,t19 := v,t20 := label,t16 := (),v5 := s.v5+1}
      obtain ⟨sf,f0,f1,f2,f3,rest⟩ := scanRun sn (pre++[v]) stack s0 s1 s2 s3
        (by simp [sn,s5]) uv (by rw [row]; simp) sa vals
      refine ⟨sf,f0,f1,f2,f3,?_⟩
      apply Reaches.prepend (Step.visit_pc16 _ _ _ (by simp [s0,hd,da]))
      apply Reaches.prepend (Step.visit_pc15_true _ _ _ cond)
      apply Reaches.prepend (Step.visit_pc29 _ _ _)
      apply Reaches.prepend (Step.visit_pc28 _ _ _ (by exact lt_of_lt_of_le sa r.preserves.sequenceAllocation))
      apply Reaches.prepend (Step.visit_pc27 _ _ _ (by simp [s1,r.color,r.allocated 0]))
      apply Reaches.prepend (Step.visit_pc26_true _ _ _ (by simpa only [s1,color_tick,r.color,Option.getD_some,Heap.read_tick,atj] using test))
      apply Reaches.prepend (Step.visit_pc25 _ _ _)
      apply Reaches.prepend (Step.visit_pc24 _ _ _ (by simp [s1,r.parent,r.allocated 1]))
      apply Reaches.prepend (Step.visit_pc23 _ _ _)
      apply Reaches.prepend (Step.visit_pc22 _ _ _)
      apply Reaches.prepend (Step.visit_pc21 _ _ _)
      apply Reaches.prepend (Step.visit_pc20 _ _ _)
      apply Reaches.prepend (Step.visit_pc19 _ _ _)
      let sc : State_visit := {s with t14 := true,t15 := true,v6 := v, t17 := graph,t18 := before.nextObject,t19 := v,t20 := label}
      have vr := visitRun ((fun value => match value with
        | .fn_visit z => Frame.fn_visit 18 {sc with t16 := z}
        | _ => .invalid) :: stack)
      have tailRun : Reaches Step (resumeConfig hb (.fn_visit ())
          ((fun value => match value with
            | .fn_visit z => Frame.fn_visit 18 {sc with t16 := z}
            | _ => .invalid) :: stack)) (.active hc (Frame.fn_visit 14 sf) stack) := by
        apply Reaches.prepend (Step.visit_pc18 _ _ _)
        apply Reaches.prepend (Step.visit_pc17 _ _ _)
        exact rest
      have condN := cond; simp only [s0,s2] at condN
      have atjN := atj
      convert vr.trans tailRun using 1 <;>
        simp only [condN,atjN,sc,sn,hv,s0,s1,s2,s3,cond,color_tick,parent_tick,r.color,r.parent,
          Option.getD_some,Heap.read_tick,atj,test]
      congr 1
  | roots_nil a =>
    intro h r
    refine ⟨h,r,by omega,?_⟩
    intro s pre stack s0 s1 s2 s3 row
    have size := (graph_preserved r.preserves hg).2.1
    have cond : decide (s.v3 < (field__a2l_import_0_UnweightedGraph_size h s.v0).getD 0) = false := by
      simp only [s0,size,Option.getD_some,s3]
      have pl : pre.length = g.size := by simpa [row] using len
      simp [pl]
    refine ⟨{s with t6 := false},s2,?_⟩
    apply Reaches.prepend (Step.dfs_ordered_pc5 _ _ _ (by simp [s0,size]))
    apply Reaches.prepend (Step.dfs_ordered_pc4_false _ _ _ cond)
    simpa only [cond] using Reaches.refl (step:=Step) (.active h (Frame.fn_dfs_ordered 3 {s with t6 := false}) stack)
  | @roots_seen u us a b k seen ev ih =>
    intro h r
    obtain ⟨h',r',cost,run⟩ := ih ((h.tick "graph_work" 1).tick "graph_work" 1) ((r.tick 1).tick 1)
    refine ⟨h',r',by simp only [Heap.clocks_tick_same] at cost; omega,?_⟩
    intro s pre stack s0 s1 s2 s3 row
    have size := (graph_preserved r.preserves hg).2.1
    have pl : pre.length < g.size := by rw [row,List.length_append,List.length_cons] at len; omega
    have atj : h.read s.v1 s.v3 = u := by
      rw [s1,r.preserves.sequences q qa,s3,qi pre.length pl]; simp [row]
    have cond : decide (s.v3 < (field__a2l_import_0_UnweightedGraph_size h s.v0).getD 0) = true := by
      simp [s0,size,s3,pl]
    have test : decide (h.read (ref before 0) u = 0) = false := by rw [r.arrays]; simp [seen]
    let sn : State_dfs_ordered := {s with t6 := true,t7 := false,v4 := u,v3 := s.v3+1}
    obtain ⟨sf,f2,rest⟩ := run sn (pre++[u]) stack s0 s1 s2 (by simp [sn,s3]) (by rw [row]; simp)
    refine ⟨sf,f2,?_⟩
    apply Reaches.prepend (Step.dfs_ordered_pc5 _ _ _ (by simp [s0,size]))
    apply Reaches.prepend (Step.dfs_ordered_pc4_true _ _ _ cond)
    apply Reaches.prepend (Step.dfs_ordered_pc21 _ _ _)
    apply Reaches.prepend (Step.dfs_ordered_pc20 _ _ _ (by simpa [s1] using lt_of_lt_of_le qa r.preserves.sequenceAllocation))
    apply Reaches.prepend (Step.dfs_ordered_pc19 _ _ _ (by simp [s2,r.color,r.allocated 0]))
    apply Reaches.prepend (Step.dfs_ordered_pc18_false _ _ _ (by simpa only [s2,color_tick,r.color,Option.getD_some,Heap.read_tick,atj] using test))
    apply Reaches.prepend (Step.dfs_ordered_pc7 _ _ _)
    apply Reaches.prepend (Step.dfs_ordered_pc6 _ _ _)
    have condN := cond; simp only [s0] at condN
    have atjN := atj; try simp only [s1] at atjN
    simpa only [sn,cond,condN,atjN,s2,color_tick,r.color,Option.getD_some,Heap.read_tick,atj,test] using rest
  | @roots_fresh u us a b c j k fresh ev1 ev2 ih1 ih2 =>
    intro h r
    obtain ⟨hb,rb,cb,visitRun⟩ := ih1 ((h.tick "graph_work" 1).tick "graph_work" 1) ((r.tick 1).tick 1)
    let hn := set_DFSResult_components hb before.nextObject (b.count+1)
    obtain ⟨hc,rc,cc,rootsRun⟩ := ih2 (hn.tick "graph_work" 1) ((rb.set_count (b.count+1)).tick 1)
    refine ⟨hc,rc,?_,?_⟩
    · simp only [hn,set_DFSResult_components,Heap.writeField_clocks,Heap.clocks_tick_same] at cb cc; omega
    · intro s pre stack s0 s1 s2 s3 row
      have size := (graph_preserved r.preserves hg).2.1
      have pl : pre.length < g.size := by rw [row,List.length_append,List.length_cons] at len; omega
      have atj : h.read s.v1 s.v3 = u := by
        rw [s1,r.preserves.sequences q qa,s3,qi pre.length pl]; simp [row]
      have cond : decide (s.v3 < (field__a2l_import_0_UnweightedGraph_size h s.v0).getD 0) = true := by simp [s0,size,s3,pl]
      have test : decide (h.read (ref before 0) u = 0) = true := by rw [r.arrays]; simp [fresh]
      let sc : State_dfs_ordered := {s with t6 := true,t7 := true,v4 := u, t12 := graph,t13 := before.nextObject,t14 := u,t15 := a.count}
      let sn : State_dfs_ordered := {sc with t11 := (),t8 := before.nextObject,t9 := b.count,t10 := 1,v3 := s.v3+1}
      obtain ⟨sf,f2,rest⟩ := rootsRun sn (pre++[u]) stack s0 s1 s2 (by simp [sn,sc,s3]) (by rw [row]; simp)
      refine ⟨sf,f2,?_⟩
      apply Reaches.prepend (Step.dfs_ordered_pc5 _ _ _ (by simp [s0,size]))
      apply Reaches.prepend (Step.dfs_ordered_pc4_true _ _ _ cond)
      apply Reaches.prepend (Step.dfs_ordered_pc21 _ _ _)
      apply Reaches.prepend (Step.dfs_ordered_pc20 _ _ _ (by simpa [s1] using lt_of_lt_of_le qa r.preserves.sequenceAllocation))
      apply Reaches.prepend (Step.dfs_ordered_pc19 _ _ _ (by simp [s2,r.color,r.allocated 0]))
      apply Reaches.prepend (Step.dfs_ordered_pc18_true _ _ _ (by simpa only [s2,color_tick,r.color,Option.getD_some,Heap.read_tick,atj] using test))
      apply Reaches.prepend (Step.dfs_ordered_pc17 _ _ _)
      apply Reaches.prepend (Step.dfs_ordered_pc16 _ _ _)
      apply Reaches.prepend (Step.dfs_ordered_pc15 _ _ _)
      apply Reaches.prepend (Step.dfs_ordered_pc14 _ _ _)
      apply Reaches.prepend (Step.dfs_ordered_pc13 _ _ _ (by simp [s2,r.count]))
      apply Reaches.prepend (Step.dfs_ordered_pc12 _ _ _)
      have vr := visitRun ((fun value => match value with
        | .fn_visit z => Frame.fn_dfs_ordered 11 {sc with t11 := z}
        | _ => .invalid) :: stack)
      have tailRun : Reaches Step (resumeConfig hb (.fn_visit ())
          ((fun value => match value with
            | .fn_visit z => Frame.fn_dfs_ordered 11 {sc with t11 := z}
            | _ => .invalid) :: stack)) (.active hc (Frame.fn_dfs_ordered 3 sf) stack) := by
        apply Reaches.prepend (Step.dfs_ordered_pc11 _ _ _)
        apply Reaches.prepend (Step.dfs_ordered_pc10 _ _ _ (by simp [sc,s2,rb.count]))
        apply Reaches.prepend (Step.dfs_ordered_pc9 _ _ _)
        apply Reaches.prepend (Step.dfs_ordered_pc8 _ _ _ (by simpa [sc,s2] using rb.valid))
        apply Reaches.prepend (Step.dfs_ordered_pc7 _ _ _)
        apply Reaches.prepend (Step.dfs_ordered_pc6 _ _ _)
        simpa only [hn,sn,sc,s2,rb.count,Option.getD_some] using rest
      have condN := cond; simp only [s0] at condN
      have atjN := atj; try simp only [s1] at atjN
      convert vr.trans tailRun using 1 <;>
        simp only [condN,atjN,sc,s0,s1,s2,cond,color_tick,components_tick,r.color,r.count,
          Option.getD_some,Heap.read_tick,atj,test]
      congr 1


def con0 (h : Heap) : Heap := ((h.tick "graph_work" 1).allocateObject "dfs.DFSResult").tick "graph_work" 1
def con1 (h : Heap) : Heap := set_DFSResult_color ((con0 h).allocate (fun _ => 0)) h.nextObject (h.nextRef+0)
def con2 (h : Heap) : Heap := set_DFSResult_parent ((con1 h).allocate (fun _ => -1)) h.nextObject (h.nextRef+1)
def con3 (h : Heap) : Heap := set_DFSResult_discover ((con2 h).allocate (fun _ => 0)) h.nextObject (h.nextRef+2)
def con4 (h : Heap) : Heap := set_DFSResult_finish ((con3 h).allocate (fun _ => 0)) h.nextObject (h.nextRef+3)
def con5 (h : Heap) : Heap := set_DFSResult_order ((con4 h).allocate (fun _ => -1)) h.nextObject (h.nextRef+4)
def con6 (h : Heap) : Heap := set_DFSResult_component ((con5 h).allocate (fun _ => -1)) h.nextObject (h.nextRef+5)
def conHeap (h : Heap) : Heap :=
  set_DFSResult_components (set_DFSResult_finished (set_DFSResult_clock (con6 h) h.nextObject 0) h.nextObject 0) h.nextObject 0

def readyHeap (h : Heap) : Heap := (conHeap h).tick "graph_work" 1

theorem preserves_allocObj (h : Heap) (name : String) : Preserves h (h.allocateObject name) := by
  constructor
  · intros; rfl
  · intro r hr; simp [Heap.allocateObject,Nat.ne_of_lt hr]
  · intros; rfl
  · simp
  · simp
  · simp
  · rfl
  · intros; rfl

theorem con_preserves (h : Heap) : Preserves h (conHeap h) := by
  have p0 : Preserves h (con0 h) := preserves_trans
    (preserves_trans (preserves_tick h 1) (preserves_allocObj _ _)) (preserves_tick _ _)
  have p1 : Preserves h (con1 h) := preserves_field
    (preserves_trans p0 (preserves_allocate _ _)) _ _
  have p2 : Preserves h (con2 h) := preserves_field
    (preserves_trans p1 (preserves_allocate _ _)) _ _
  have p3 : Preserves h (con3 h) := preserves_field
    (preserves_trans p2 (preserves_allocate _ _)) _ _
  have p4 : Preserves h (con4 h) := preserves_field
    (preserves_trans p3 (preserves_allocate _ _)) _ _
  have p5 : Preserves h (con5 h) := preserves_field
    (preserves_trans p4 (preserves_allocate _ _)) _ _
  have p6 : Preserves h (con6 h) := preserves_field
    (preserves_trans p5 (preserves_allocate _ _)) _ _
  exact preserves_field (preserves_field (preserves_field p6 _ _) _ _) _ _

theorem con_rep (h : Heap) : Rep h (conHeap h) initial := by
  have valid : is_DFSResult (conHeap h) h.nextObject := by
    simp [conHeap,con6,con5,con4,con3,con2,con1,con0,
      is_DFSResult,set_DFSResult_color,set_DFSResult_parent,set_DFSResult_discover,
      set_DFSResult_finish,set_DFSResult_order,set_DFSResult_component,
      set_DFSResult_clock,set_DFSResult_finished,set_DFSResult_components]
  refine ⟨con_preserves h,?_,?_,valid,?_,?_,?_,?_,?_⟩
  · simp [conHeap,con6,con5,con4,con3,con2,con1,con0,
      set_DFSResult_color,set_DFSResult_parent,set_DFSResult_discover,
      set_DFSResult_finish,set_DFSResult_order,set_DFSResult_component,
      set_DFSResult_clock,set_DFSResult_finished,set_DFSResult_components]
  · simp [conHeap,con6,con5,con4,con3,con2,con1,con0,
      set_DFSResult_color,set_DFSResult_parent,set_DFSResult_discover,
      set_DFSResult_finish,set_DFSResult_order,set_DFSResult_component,
      set_DFSResult_clock,set_DFSResult_finished,set_DFSResult_components]
  · intro i; fin_cases i <;>
      simp [ObjectValue.asSeq,arrField,conHeap,con6,con5,con4,con3,con2,con1,con0,initial,ref,
        field_DFSResult_color,field_DFSResult_parent,field_DFSResult_discover,
        field_DFSResult_finish,field_DFSResult_order,field_DFSResult_component,
        is_DFSResult,set_DFSResult_color,set_DFSResult_parent,set_DFSResult_discover,
        set_DFSResult_finish,set_DFSResult_order,set_DFSResult_component,
        set_DFSResult_clock,set_DFSResult_finished,set_DFSResult_components]
  · simp [conHeap,con6,con5,con4,con3,con2,con1,con0,initial,
      ObjectValue.asInt,field_DFSResult_clock,is_DFSResult,set_DFSResult_color,set_DFSResult_parent,set_DFSResult_discover,
      set_DFSResult_finish,set_DFSResult_order,set_DFSResult_component,
      set_DFSResult_clock,set_DFSResult_finished,set_DFSResult_components]
  · simp [conHeap,con6,con5,con4,con3,con2,con1,con0,initial,
      ObjectValue.asInt,field_DFSResult_finished,is_DFSResult,set_DFSResult_color,set_DFSResult_parent,set_DFSResult_discover,
      set_DFSResult_finish,set_DFSResult_order,set_DFSResult_component,
      set_DFSResult_clock,set_DFSResult_finished,set_DFSResult_components]
  · simp [conHeap,con6,con5,con4,con3,con2,con1,con0,initial,
      ObjectValue.asInt,field_DFSResult_components,is_DFSResult,set_DFSResult_color,set_DFSResult_parent,set_DFSResult_discover,
      set_DFSResult_finish,set_DFSResult_order,set_DFSResult_component,
      set_DFSResult_clock,set_DFSResult_finished,set_DFSResult_components]
  · intro i; fin_cases i <;> funext j <;>
      simp [Nat.add_assoc,conHeap,con6,con5,con4,con3,con2,con1,con0,initial,ref,Heap.read,Heap.allocate,
        set_DFSResult_color,set_DFSResult_parent,set_DFSResult_discover,
        set_DFSResult_finish,set_DFSResult_order,set_DFSResult_component,
        set_DFSResult_clock,set_DFSResult_finished,set_DFSResult_components]

theorem ready_cost (h : Heap) : (readyHeap h).clocks "graph_work" = h.clocks "graph_work" + 3 := by
  simp [readyHeap,conHeap,con6,con5,con4,con3,con2,con1,con0,
    set_DFSResult_color,set_DFSResult_parent,set_DFSResult_discover,
    set_DFSResult_finish,set_DFSResult_order,set_DFSResult_component,
    set_DFSResult_clock,set_DFSResult_finished,set_DFSResult_components]

theorem constructor_execution (h : Heap) (graph : ObjectRef) (q : SeqRef) (stack : Stack) :
    Reaches Step (.active h (Frame.fn_dfs_ordered 26 {v0 := graph,v1 := q}) stack)
      (.active (readyHeap h)
        (Frame.fn_dfs_ordered 5 {v0 := graph,v1 := q,v2 := h.nextObject,t16 := h.nextObject}) stack) := by
  apply Reaches.prepend (Step.dfs_ordered_pc26 _ _ _)
  apply Reaches.prepend (Step.dfs_ordered_pc25 _ _ _)
  apply Reaches.prepend (Step.DFSResult_pc6 _ _ _)
  apply Reaches.prepend (Step.DFSResult_pc5 _ _ _)
  apply Reaches.prepend (Step.DFSResult_pc4 _ _ _)
  apply Reaches.prepend (Step.DFSResult_pc3 _ _ _)
  apply Reaches.prepend (Step.DFSResult___init___pc30 _ _ _)
  apply Reaches.prepend (Step.DFSResult___init___pc29 _ _ _)
  apply Reaches.prepend (Step.DFSResult___init___pc28 _ _ _)
  apply Reaches.prepend (Step.DFSResult___init___pc27 _ _ _)
  apply Reaches.prepend (Step.DFSResult___init___pc26 _ _ _ (by simp [is_DFSResult,set_DFSResult_color,set_DFSResult_parent,set_DFSResult_discover,
    set_DFSResult_finish,set_DFSResult_order,set_DFSResult_component,set_DFSResult_clock,
    set_DFSResult_finished,set_DFSResult_components]))
  apply Reaches.prepend (Step.DFSResult___init___pc25 _ _ _)
  apply Reaches.prepend (Step.DFSResult___init___pc24 _ _ _)
  apply Reaches.prepend (Step.DFSResult___init___pc23 _ _ _)
  apply Reaches.prepend (Step.DFSResult___init___pc22 _ _ _ (by simp [is_DFSResult,set_DFSResult_color,set_DFSResult_parent,set_DFSResult_discover,
    set_DFSResult_finish,set_DFSResult_order,set_DFSResult_component,set_DFSResult_clock,
    set_DFSResult_finished,set_DFSResult_components]))
  apply Reaches.prepend (Step.DFSResult___init___pc21 _ _ _)
  apply Reaches.prepend (Step.DFSResult___init___pc20 _ _ _)
  apply Reaches.prepend (Step.DFSResult___init___pc19 _ _ _)
  apply Reaches.prepend (Step.DFSResult___init___pc18 _ _ _ (by simp [is_DFSResult,set_DFSResult_color,set_DFSResult_parent,set_DFSResult_discover,
    set_DFSResult_finish,set_DFSResult_order,set_DFSResult_component,set_DFSResult_clock,
    set_DFSResult_finished,set_DFSResult_components]))
  apply Reaches.prepend (Step.DFSResult___init___pc17 _ _ _)
  apply Reaches.prepend (Step.DFSResult___init___pc16 _ _ _)
  apply Reaches.prepend (Step.DFSResult___init___pc15 _ _ _)
  apply Reaches.prepend (Step.DFSResult___init___pc14 _ _ _ (by simp [is_DFSResult,set_DFSResult_color,set_DFSResult_parent,set_DFSResult_discover,
    set_DFSResult_finish,set_DFSResult_order,set_DFSResult_component,set_DFSResult_clock,
    set_DFSResult_finished,set_DFSResult_components]))
  apply Reaches.prepend (Step.DFSResult___init___pc13 _ _ _)
  apply Reaches.prepend (Step.DFSResult___init___pc12 _ _ _)
  apply Reaches.prepend (Step.DFSResult___init___pc11 _ _ _)
  apply Reaches.prepend (Step.DFSResult___init___pc10 _ _ _ (by simp [is_DFSResult,set_DFSResult_color,set_DFSResult_parent,set_DFSResult_discover,
    set_DFSResult_finish,set_DFSResult_order,set_DFSResult_component,set_DFSResult_clock,
    set_DFSResult_finished,set_DFSResult_components]))
  apply Reaches.prepend (Step.DFSResult___init___pc9 _ _ _)
  apply Reaches.prepend (Step.DFSResult___init___pc8 _ _ _)
  apply Reaches.prepend (Step.DFSResult___init___pc7 _ _ _)
  apply Reaches.prepend (Step.DFSResult___init___pc6 _ _ _ (by simp [is_DFSResult,set_DFSResult_color,set_DFSResult_parent,set_DFSResult_discover,
    set_DFSResult_finish,set_DFSResult_order,set_DFSResult_component,set_DFSResult_clock,
    set_DFSResult_finished,set_DFSResult_components]))
  apply Reaches.prepend (Step.DFSResult___init___pc5 _ _ _ (by simp [is_DFSResult,set_DFSResult_color,set_DFSResult_parent,set_DFSResult_discover,
    set_DFSResult_finish,set_DFSResult_order,set_DFSResult_component,set_DFSResult_clock,
    set_DFSResult_finished,set_DFSResult_components]))
  apply Reaches.prepend (Step.DFSResult___init___pc4 _ _ _ (by simp [is_DFSResult,set_DFSResult_color,set_DFSResult_parent,set_DFSResult_discover,
    set_DFSResult_finish,set_DFSResult_order,set_DFSResult_component,set_DFSResult_clock,
    set_DFSResult_finished,set_DFSResult_components]))
  apply Reaches.prepend (Step.DFSResult___init___pc3 _ _ _ (by simp [is_DFSResult,set_DFSResult_color,set_DFSResult_parent,set_DFSResult_discover,
    set_DFSResult_finish,set_DFSResult_order,set_DFSResult_component,set_DFSResult_clock,
    set_DFSResult_finished,set_DFSResult_components]))
  apply Reaches.prepend (Step.DFSResult___init___pc2 _ _ _)
  apply Reaches.prepend (Step.DFSResult___init___pc1 _ _ _)
  apply Reaches.prepend (Step.DFSResult_pc2 _ _ _)
  apply Reaches.prepend (Step.DFSResult_pc1 _ _ _ (con_rep h).valid)
  apply Reaches.prepend (Step.dfs_ordered_pc24 _ _ _)
  apply Reaches.prepend (Step.dfs_ordered_pc23 _ _ _)
  apply Reaches.prepend (Step.dfs_ordered_pc22 _ _ _)
  exact Reaches.refl _


theorem rep_post {before h : Heap} {g : Graph} {input : Seq} {a : Pure.State}
    (r : Rep before h a) (done : Completed g input a) :
    LocalPost before h before.nextObject g input := by
  obtain ⟨clock,finished,black,count,hcount,cb,cert⟩ := done
  have fresh : FreshArrays before h
      [ref before 0,ref before 1,ref before 2,ref before 3,ref before 4,ref before 5] := by
    constructor
    · simp [ref,List.pairwise_cons]
    · intro v mem
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨Nat.le_add_right _ _,r.allocated _⟩
  refine ⟨r.valid,⟨le_refl _,by rw [r.no]; exact Nat.lt_succ_self _⟩,r.preserves,
    ref before 0,ref before 1,ref before 2,ref before 3,ref before 4,ref before 5,
    r.color,r.parent,r.discover,r.finish,r.order,r.component,fresh,?_,?_,?_,count,?_,cb,?_⟩
  · rw [r.clock,clock]
  · rw [r.finished,finished]
  · intro v hv; rw [r.arrays]; exact black v hv
  · rw [r.count,hcount]
  · simpa only [r.arrays] using cert

end DFSSim

theorem solution
    (before : Heap) (graph : ObjectRef) (g : Graph) (inputOrder : SeqRef)
    (represented : GraphRep before graph g)
    (orderAllocated : inputOrder < before.nextRef)
    (orderValid : VertexOrder g (before.read inputOrder)) :
    ∃ (after : Heap) (result : ObjectRef),
      Algo.dfs.dfs_ordered.Call before (graph, inputOrder) after result ∧
      LocalPost before after result g (before.read inputOrder) ∧
      work before after ≤ 4 + 6 * g.size + 2 * edgeCount g := by
  obtain ⟨values,perm,vals⟩ := orderValid
  obtain ⟨a,k,ev,done,bound⟩ := CLRS.DFS.pure_execution_certificate g (before.read inputOrder) values perm vals
  have len : values.length = g.size := by simpa using perm.length_eq
  obtain ⟨h,r,cost,run⟩ := DFSSim.realizes before graph g inputOrder values represented orderAllocated len vals ev
    (DFSSim.readyHeap before) ((DFSSim.con_rep before).tick 1)
  refine ⟨h.tick "graph_work" 1,before.nextObject,?_,DFSSim.rep_post (r.tick 1) done,?_⟩
  · refine ⟨⟨represented.1,orderAllocated⟩,?_⟩
    intro stack
    obtain ⟨sf,sf2,loop⟩ := run
      {v0 := graph,v1 := inputOrder,v2 := before.nextObject,t16 := before.nextObject}
      [] stack rfl rfl rfl rfl rfl
    apply (DFSSim.constructor_execution before graph inputOrder stack).trans (loop.trans ?_)
    apply Reaches.prepend (Step.dfs_ordered_pc3 _ _ _)
    apply Reaches.prepend (Step.dfs_ordered_pc2 _ _ _)
    apply Reaches.prepend (Step.dfs_ordered_pc1 _ _ _ (by simpa only [sf2] using (r.tick 1).valid))
    simpa only [sf2] using Reaches.refl (step:=Step)
      (resumeConfig (h.tick "graph_work" 1) (.fn_dfs_ordered before.nextObject) stack)
  · rw [DFSSim.ready_cost] at cost
    simp only [work,Heap.cost,Heap.clocks_tick_same,cost]
    omega
