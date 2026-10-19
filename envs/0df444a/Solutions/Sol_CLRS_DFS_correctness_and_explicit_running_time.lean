-- Prove2me | solution 1 for CLRS.DFS.correctness_and_explicit_running_time
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:23:02.120968+00:00
-- url     : https://prove2.me/submissions/31ff0d0e-344c-48ba-abd8-2585ffdd6845

import Theorems.Thm_CLRS_DFS_ordered_correctness_and_explicit_running_time
import Mathlib.Data.List.Range

set_option autoImplicit false

open Algo2LeanGenerated CLRS.GraphTraversal CLRS.DFS
open Algo.dfs.Algo2LeanGenerated Algo2LeanCore

namespace DFSWrapper

def loopHeap (h : Heap) : Nat → Heap
  | 0 => ((h.tick "graph_work" 1).allocate (fun _ => 0)).tick "graph_work" 1
  | k + 1 => (((loopHeap h k).tick "graph_work" 1).write h.nextRef k k).tick "graph_work" 1

@[simp] theorem heap_meta (h : Heap) (k : Nat) :
    (loopHeap h k).nextRef = h.nextRef + 1 ∧
    (loopHeap h k).nextObject = h.nextObject ∧
    (loopHeap h k).nextCollection = h.nextCollection ∧
    (loopHeap h k).objects = h.objects ∧
    (loopHeap h k).collections = h.collections ∧
    (loopHeap h k).clocks "graph_work" = h.clocks "graph_work" + 2 + 2*k := by
  induction k with
  | zero => simp [loopHeap, Heap.allocate, Heap.tick]
  | succ k ih => simp only [loopHeap, Heap.tick_nextRef, Heap.write_nextRef,
      Heap.tick_nextObject, Heap.write_nextObject, Heap.tick_nextCollection,
      Heap.write_nextCollection, Heap.tick_objects, Heap.write_objects,
      Heap.tick_collections, Heap.write_collections, Heap.clocks_tick_same,
      Heap.write_clocks]; rcases ih with ⟨a,b,c,d,e,f⟩; simp_all; omega

theorem old_read (h : Heap) (k : Nat) (r : SeqRef) (hr : r < h.nextRef) :
    (loopHeap h k).read r = h.read r := by
  funext i
  induction k with
  | zero => simp [loopHeap, Heap.allocate, Heap.read, Nat.ne_of_lt hr]
  | succ k ih => simpa [loopHeap, Heap.read_write_other_ref, Nat.ne_of_lt hr] using ih

theorem identity_read (h : Heap) (k j : Nat) (hj : j < k) :
    (loopHeap h k).read h.nextRef j = j := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases eq : j = k
    · subst j; simp [loopHeap]
    · have lt : j < k := by omega
      have ne : (j : Int) ≠ (k : Int) := by omega
      simpa [loopHeap, Heap.read_write_other_index, ne] using ih lt

theorem other_clock (h : Heap) (k : Nat) (name : String) (hn : name ≠ "graph_work") :
    (loopHeap h k).clocks name = h.clocks name := by
  induction k with
  | zero => simp [loopHeap, Heap.clocks_tick_other, hn]
  | succ k ih => simpa [loopHeap, Heap.clocks_tick_other, hn] using ih

theorem prepared_preserves (h : Heap) (k : Nat) :
    Preserves h ((loopHeap h k).tick "graph_work" 1) := by
  rcases heap_meta h k with ⟨a,b,c,d,e,f⟩
  constructor
  · intro r hr; exact old_read h k r hr
  · intro r _; simpa only [Heap.tick_objects, d]
  · intro r _; simpa only [Heap.tick_collections, e]
  · simp [a]
  · simp [b]
  · simp [c]
  · simp only [Heap.clocks_tick_same, f]; omega
  · intro name hn; simpa [Heap.clocks_tick_other, hn] using other_clock h k name hn

theorem preserves_trans {a b c : Heap} (ab : Preserves a b) (bc : Preserves b c) :
    Preserves a c := by
  constructor
  · intro r hr; exact (bc.sequences r (lt_of_lt_of_le hr ab.sequenceAllocation)).trans (ab.sequences r hr)
  · intro r hr; exact (bc.objects r (lt_of_lt_of_le hr ab.objectAllocation)).trans (ab.objects r hr)
  · intro r hr; exact (bc.collections r (lt_of_lt_of_le hr ab.collectionAllocation)).trans (ab.collections r hr)
  · exact ab.sequenceAllocation.trans bc.sequenceAllocation
  · exact ab.objectAllocation.trans bc.objectAllocation
  · exact ab.collectionAllocation.trans bc.collectionAllocation
  · exact ab.workMonotone.trans bc.workMonotone
  · intro n hn; exact (bc.otherClocks n hn).trans (ab.otherClocks n hn)

theorem graph_prepared (h : Heap) (k : Nat) (r : ObjectRef) (g : Graph)
    (hg : GraphRep h r g) :
    GraphRep ((loopHeap h k).tick "graph_work" 1) r g := by
  rcases heap_meta h k with ⟨a,b,c,d,e,f⟩
  have objs : ((loopHeap h k).tick "graph_work" 1).objects = h.objects := by simp [d]
  have colls : ((loopHeap h k).tick "graph_work" 1).collections = h.collections := by simp [e]
  have fields : ∀ ref field, ((loopHeap h k).tick "graph_work" 1).readField ref field = h.readField ref field := by
    intros; simp [Heap.readField, objs]
  have classes : ∀ ref, ((loopHeap h k).tick "graph_work" 1).objectClass ref = h.objectClass ref := by
    intros; simp [Heap.objectClass, objs]
  unfold GraphRep at hg ⊢
  simp only [Algo.graph_input.Algo2LeanGenerated.is_UnweightedGraph,
    Algo.graph_input.Algo2LeanGenerated.field_UnweightedGraph_size,
    Algo.graph_input.Algo2LeanGenerated.field_UnweightedGraph_adj,
    Algo.graph_input.Algo2LeanGenerated.field_UnweightedGraph_degree,
    Heap.tick_nextObject, b, classes, fields] at hg ⊢
  rcases hg with ⟨valid,size,adj,degree,ha,hd,hav,hdv,rows⟩
  refine ⟨valid,size,adj,degree,ha,hd,?_,?_,?_⟩
  · simpa [SequenceType.valid, Algo.graph_input.Algo2LeanGenerated.seq_Seq_Int, Heap.validSequence,
      Heap.sequenceType, colls, Heap.tick_nextCollection, c] using hav
  · simp only [Heap.tick_nextRef, a]; exact lt_trans hdv (Nat.lt_succ_self _) 
  · intro u hu
    rcases rows u hu with ⟨deg,row,get,rv,vals⟩
    refine ⟨?_,row,?_,?_,?_⟩
    · simpa [old_read h k degree hdv] using deg
    · simpa [SequenceType.get,
        SequenceType.valid, Algo.graph_input.Algo2LeanGenerated.seq_Seq_Int, Heap.validSequence,
        Heap.sequenceType, Heap.readElement, colls, Heap.tick_nextCollection, c] using get
    · simp only [Heap.tick_nextRef, a]; exact lt_trans rv (Nat.lt_succ_self _) 
    · intro j hj; simpa [old_read h k row rv] using vals j hj

theorem loop_execution (h : Heap) (graph : ObjectRef) (g : Graph)
    (hg : GraphRep h graph g) (k : Nat) (hk : k ≤ g.size) (stack : Stack) :
    ∃ s : State_dfs, s.v0 = graph ∧ s.v1 = h.nextRef ∧ s.v2 = (k : Int) ∧
      Reaches Step (.active h (Frame.fn_dfs 17 {v0 := graph}) stack)
        (.active (loopHeap h k) (Frame.fn_dfs 7 s) stack) := by
  induction k with
  | zero =>
    refine ⟨{v0 := graph, v1 := h.nextRef, t7 := h.nextRef}, rfl, rfl, rfl, ?_⟩
    apply Reaches.prepend (Step.dfs_pc17 _ _ _)
    apply Reaches.prepend (Step.dfs_pc16 _ _ _)
    apply Reaches.prepend (Step.dfs_pc15 _ _ _)
    apply Reaches.prepend (Step.dfs_pc14 _ _ _)
    apply Reaches.prepend (Step.dfs_pc13 _ _ _)
    apply Reaches.prepend (Step.dfs_pc12 _ _ _)
    exact Reaches.refl _
  | succ k ih =>
    obtain ⟨s,sv0,sv1,sv2,run⟩ := ih (by omega)
    have size : field__a2l_import_0_UnweightedGraph_size (loopHeap h k) s.v0 = some (g.size : Int) := by
      rw [sv0]; exact (graph_prepared h k graph g hg).2.1
    have cond : decide (s.v2 < (field__a2l_import_0_UnweightedGraph_size (loopHeap h k) s.v0).getD 0) = true := by
      simp only [size, Option.getD_some, sv2, decide_eq_true_eq]; omega
    refine ⟨{s with t6 := true, v2 := s.v2 + 1}, sv0, sv1, ?_, run.trans ?_⟩
    · simp [sv2]
    · apply Reaches.prepend (Step.dfs_pc7 _ _ _ (by simp [size]))
      apply Reaches.prepend (Step.dfs_pc6_true _ _ _ cond)
      apply Reaches.prepend (Step.dfs_pc11 _ _ _)
      apply Reaches.prepend (Step.dfs_pc10 _ _ _ (by simp [sv1, (heap_meta h k).1]))
      apply Reaches.prepend (Step.dfs_pc9 _ _ _)
      apply Reaches.prepend (Step.dfs_pc8 _ _ _)
      change Reaches Step
        (.active ((((loopHeap h k).tick "graph_work" 1).write s.v1 s.v2 s.v2).tick "graph_work" 1)
          (Frame.fn_dfs 7 {s with t6 := decide (s.v2 < (field__a2l_import_0_UnweightedGraph_size (loopHeap h k) s.v0).getD 0), v2 := s.v2 + 1}) stack) _
      rw [cond]
      simpa only [loopHeap, sv1, sv2] using
        (Reaches.refl (.active (loopHeap h (k+1))
          (Frame.fn_dfs 7 {s with t6 := true, v2 := s.v2 + 1}) stack) : Reaches Step _ _)

theorem call_wrapper (h : Heap) (graph : ObjectRef) (g : Graph)
    (hg : GraphRep h graph g) (after : Heap) (result : ObjectRef)
    (call : Algo.dfs.dfs_ordered.Call ((loopHeap h g.size).tick "graph_work" 1)
      (graph, h.nextRef) after result)
    (validResult : is_DFSResult after result) :
    Algo.dfs.dfs.Call h graph after result := by
  refine ⟨hg.1, ?_⟩
  intro stack
  obtain ⟨s,sv0,sv1,sv2,run⟩ := loop_execution h graph g hg g.size (by rfl) stack
  have size : field__a2l_import_0_UnweightedGraph_size (loopHeap h g.size) s.v0 = some (g.size : Int) := by
    rw [sv0]; exact (graph_prepared h g.size graph g hg).2.1
  refine run.trans ?_
  apply Reaches.prepend (Step.dfs_pc7 _ _ _ (by simp [size]))
  apply Reaches.prepend (Step.dfs_pc6_false _ _ _ (by simp [size, sv2]))
  apply Reaches.prepend (Step.dfs_pc5 _ _ _)
  apply Reaches.prepend (Step.dfs_pc4 _ _ _)
  apply Reaches.prepend (Step.dfs_pc3 _ _ _)
  apply Reaches.prepend (Step.dfs_pc2 _ _ _)
  have ordered := call.2 ((fun value => match value with
    | .fn_dfs_ordered result => Frame.fn_dfs 1 {s with
        t6 := false, t4 := graph, t5 := h.nextRef, t3 := result}
    | _ => .invalid) :: stack)
  have tailRun := Reaches.single (Step.dfs_pc1 after
    {s with t6 := false, t4 := graph, t5 := h.nextRef, t3 := result} stack validResult)
  have sizeGraph : field__a2l_import_0_UnweightedGraph_size (loopHeap h g.size) graph = some (g.size : Int) := by
    rw [← sv0]; exact size
  convert ordered.trans tailRun using 1 <;>
    simp [sv0, sv1, sizeGraph, sv2, resumeConfig]
  funext value
  cases value <;> rfl

theorem forest_identity (g : Graph) (q p d f o c : Seq) (count : Nat)
    (hq : ∀ i : Nat, i < g.size → q i = i)
    (forest : Forest g q p d f o c count) :
    Forest g (fun i => i) p d f o c count := by
  have rootP : ∀ i : Nat, i < g.size → p i = -1 →
      ∀ j : Nat, j < i → f j < d i := by
    intro i hi hp j hj
    have hjn : j < g.size := lt_trans hj hi
    simpa only [hq i hi, hq j hjn] using
      forest.rootPriority i hi (by simpa only [hq i hi] using hp) j hj
  exact { forest with rootPriority := rootP }

theorem post_wrapper (h after : Heap) (g : Graph) (result : ObjectRef)
    (post : Post ((loopHeap h g.size).tick "graph_work" 1) after result g
      (((loopHeap h g.size).tick "graph_work" 1).read h.nextRef)) :
    Post h after result g (fun i => i) := by
  let mid := (loopHeap h g.size).tick "graph_work" 1
  have pre : Preserves h mid := prepared_preserves h g.size
  rcases post with ⟨valid,fresh,preserves,color,parent,discover,finish,order,component,
    hc,hp,hd,hf,ho,hb,arrays,clock,finished,black,count,hcount,cn,forest⟩
  refine ⟨valid,?_,preserves_trans pre preserves,color,parent,discover,finish,order,component,
    hc,hp,hd,hf,ho,hb,?_,clock,finished,black,count,hcount,cn,?_⟩
  · exact ⟨pre.objectAllocation.trans fresh.1, fresh.2⟩
  · exact ⟨arrays.1,fun r hr => ⟨pre.sequenceAllocation.trans (arrays.2 r hr).1, (arrays.2 r hr).2⟩⟩
  · apply forest_identity _ _ _ _ _ _ _ _ _ forest
    intro i hi
    exact identity_read h g.size i hi

end DFSWrapper

open DFSWrapper

theorem solution (before : Heap) (graph : ObjectRef) (g : Graph)
    (represented : GraphRep before graph g) :
    ∃ (after : Heap) (result : ObjectRef),
      Algo.dfs.dfs.Call before graph after result ∧
      Post before after result g (fun i : Int => i) ∧
      work before after ≤ 7 + 8 * g.size + 2 * edgeCount g := by
  let mid := (loopHeap before g.size).tick "graph_work" 1
  have prepared : GraphRep mid graph g := graph_prepared before g.size graph g represented
  have allocated : before.nextRef < mid.nextRef := by
    simp [mid, (heap_meta before g.size).1]
  have orderValid : VertexOrder g (mid.read before.nextRef) := by
    refine ⟨(List.range g.size).map Int.ofNat, List.Perm.refl _, ?_⟩
    intro j hj
    change (loopHeap before g.size).read before.nextRef j = _
    rw [identity_read before g.size j hj]
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  obtain ⟨after,result,call,post,bound⟩ :=
    CLRS.DFS.ordered_correctness_and_explicit_running_time mid graph g before.nextRef
      prepared allocated orderValid
  refine ⟨after,result,call_wrapper before graph g represented after result call post.1,
    post_wrapper before after g result post,?_⟩
  have baseClock : mid.clocks "graph_work" = before.clocks "graph_work" + 3 + 2*g.size := by
    simp only [mid, Heap.clocks_tick_same, (heap_meta before g.size).2.2.2.2.2]; omega
  have mono := post.2.2.1.workMonotone
  simp only [work, Heap.cost] at bound ⊢
  rw [baseClock] at bound mono
  omega
