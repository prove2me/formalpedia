-- Prove2me | solution 1 for CLRS.SCC.scc_correctness_and_running_time
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T03:00:47.443038+00:00
-- url     : https://prove2.me/submissions/e8798f1e-512d-4174-8b6d-c51555f60d9a

import Theorems.Thm_CLRS_SCC_transpose_correctness_and_running_time
import Theorems.Thm_CLRS_DFS_correctness_and_explicit_running_time
import Theorems.Thm_CLRS_DFS_ordered_correctness_and_explicit_running_time
import Theorems.Thm_CLRS_SCC_kosaraju_forest_components
import Mathlib.Data.List.Range

set_option autoImplicit false
open Algo2LeanGenerated CLRS.GraphTraversal Algo2LeanCore
open Algo.scc.Algo2LeanGenerated

namespace SCCComposition

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

theorem preserves_tick (h : Heap) : Preserves h (h.tick "graph_work" 1) := by
  constructor
  · intros; rfl
  all_goals simp [Heap.tick]

theorem classes_preserved {a b : Heap} (h : Preserves a b) (r : ObjectRef)
    (hr : r < a.nextObject) : b.objectClass r = a.objectClass r := by
  simp [Heap.objectClass, h.objects r hr]

theorem fields_preserved {a b : Heap} (h : Preserves a b) (r : ObjectRef)
    (hr : r < a.nextObject) (field : String) : b.readField r field = a.readField r field := by
  simp [Heap.readField, h.objects r hr]

theorem graph_preserved {a b : Heap} (pres : Preserves a b) (r : ObjectRef) (g : Graph)
    (hg : GraphRep a r g) : GraphRep b r g := by
  have allocated := hg.1.1
  have cls := classes_preserved pres r allocated
  have fields := fields_preserved pres r allocated
  have valid : Algo.graph_input.Algo2LeanGenerated.is_UnweightedGraph b r :=
    ⟨lt_of_lt_of_le allocated pres.objectAllocation, by rw [cls]; exact hg.1.2⟩
  have get_fields : ∀ field, b.readField r field = a.readField r field := fields
  rcases hg with ⟨av,size,adj,degree,ha,hd,hav,hdv,rows⟩
  have colValid : Algo.graph_input.Algo2LeanGenerated.seq_Seq_Int.valid b adj := by
    unfold SequenceType.valid Algo.graph_input.Algo2LeanGenerated.seq_Seq_Int Heap.validSequence at hav ⊢
    have ca : adj < a.nextCollection := hav.1
    simpa only [Heap.sequenceType, pres.collections adj ca] using
      (And.intro (lt_of_lt_of_le ca pres.collectionAllocation) hav.2)
  refine ⟨valid,?_,adj,degree,?_,?_,colValid,lt_of_lt_of_le hdv pres.sequenceAllocation,?_⟩
  · simpa [Algo.graph_input.Algo2LeanGenerated.field_UnweightedGraph_size,
      valid, av, get_fields] using size
  · simpa [Algo.graph_input.Algo2LeanGenerated.field_UnweightedGraph_adj,
      valid, av, get_fields] using ha
  · simpa [Algo.graph_input.Algo2LeanGenerated.field_UnweightedGraph_degree,
      valid, av, get_fields] using hd
  · intro u hu
    rcases rows u hu with ⟨deg,row,get,rv,vals⟩
    refine ⟨?_,row,?_,lt_of_lt_of_le rv pres.sequenceAllocation,?_⟩
    · simpa [pres.sequences degree hdv] using deg
    · have ca : adj < a.nextCollection := hav.1
      simpa only [SequenceType.get, colValid, hav, if_pos, Heap.readElement,
        pres.collections adj ca] using get
    · intro j hj; simpa [pres.sequences row rv] using vals j hj

-- One fresh array, filled from right to left in the first pass's finish order.
def loopHeap (h : Heap) (n : Nat) (order : Seq) : Nat → Heap
  | 0 => ((h.tick "graph_work" 1).allocate (fun _ => -1)).tick "graph_work" 1
  | k + 1 => (((loopHeap h n order k).tick "graph_work" 1).write h.nextRef k
      (order ((n : Int) - 1 - k))).tick "graph_work" 1

@[simp] theorem heap_meta (h : Heap) (n k : Nat) (order : Seq) :
    (loopHeap h n order k).nextRef = h.nextRef + 1 ∧
    (loopHeap h n order k).nextObject = h.nextObject ∧
    (loopHeap h n order k).nextCollection = h.nextCollection ∧
    (loopHeap h n order k).objects = h.objects ∧
    (loopHeap h n order k).collections = h.collections ∧
    (loopHeap h n order k).clocks "graph_work" = h.clocks "graph_work" + 2 + 2*k := by
  induction k with
  | zero => simp [loopHeap, Heap.allocate, Heap.tick]
  | succ k ih =>
    simp only [loopHeap, Heap.tick_nextRef, Heap.write_nextRef,
      Heap.tick_nextObject, Heap.write_nextObject, Heap.tick_nextCollection,
      Heap.write_nextCollection, Heap.tick_objects, Heap.write_objects,
      Heap.tick_collections, Heap.write_collections, Heap.clocks_tick_same,
      Heap.write_clocks]
    rcases ih with ⟨a,b,c,d,e,f⟩; simp_all; omega

theorem old_read (h : Heap) (n k : Nat) (order : Seq) (r : SeqRef) (hr : r < h.nextRef) :
    (loopHeap h n order k).read r = h.read r := by
  funext i
  induction k with
  | zero => simp [loopHeap, Heap.allocate, Heap.read, Nat.ne_of_lt hr]
  | succ k ih => simpa [loopHeap, Heap.read_write_other_ref, Nat.ne_of_lt hr] using ih

theorem reversed_read (h : Heap) (n k j : Nat) (order : Seq) (hj : j < k) :
    (loopHeap h n order k).read h.nextRef j = order ((n : Int) - 1 - j) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases eq : j = k
    · subst j; simp [loopHeap]
    · have lt : j < k := by omega
      have ne : (j : Int) ≠ (k : Int) := by omega
      simpa [loopHeap, Heap.read_write_other_index, ne] using ih lt

theorem other_clock (h : Heap) (n k : Nat) (order : Seq) (name : String) (hn : name ≠ "graph_work") :
    (loopHeap h n order k).clocks name = h.clocks name := by
  induction k with
  | zero => simp [loopHeap, Heap.clocks_tick_other, hn]
  | succ k ih => simpa [loopHeap, Heap.clocks_tick_other, hn] using ih

theorem loop_preserves (h : Heap) (n k : Nat) (order : Seq) :
    Preserves h (loopHeap h n order k) := by
  rcases heap_meta h n k order with ⟨a,b,c,d,e,f⟩
  constructor
  · exact old_read h n k order
  · intro r _; rw [d]
  · intro r _; rw [e]
  · omega
  · omega
  · omega
  · omega
  · exact other_clock h n k order

theorem result_order_preserved {a b : Heap} (pres : Preserves a b)
    (r order : Nat) (valid : Algo.dfs.Algo2LeanGenerated.is_DFSResult a r)
    (field : field__a2l_import_1_DFSResult_order a r = some order) :
    field__a2l_import_1_DFSResult_order b r = some order := by
  have valid' : Algo.dfs.Algo2LeanGenerated.is_DFSResult b r :=
    ⟨lt_of_lt_of_le valid.1 pres.objectAllocation, by
      rw [classes_preserved pres r valid.1]; exact valid.2⟩
  simpa [field__a2l_import_1_DFSResult_order,
    Algo.dfs.Algo2LeanGenerated.field_DFSResult_order, valid, valid',
    fields_preserved pres r valid.1] using field

theorem loop_execution (h : Heap) (graph first ord : Nat) (g : Graph)
    (hg : GraphRep h graph g)
    (valid : Algo.dfs.Algo2LeanGenerated.is_DFSResult h first)
    (fo : field__a2l_import_1_DFSResult_order h first = some ord)
    (oa : ord < h.nextRef) (transposed : ObjectRef)
    (initial : State_scc) (init0 : initial.v0 = graph)
    (init1 : initial.v1 = first) (init2 : initial.v2 = transposed)
    (k : Nat) (hk : k ≤ g.size) (stack : Stack) :
    ∃ s : State_scc, s.v0 = graph ∧ s.v1 = first ∧ s.v2 = transposed ∧
      s.v3 = h.nextRef ∧ s.v4 = (k : Int) ∧
      Reaches Step (.active h (Frame.fn_scc 17 initial) stack)
        (.active (loopHeap h g.size (h.read ord) k) (Frame.fn_scc 7 s) stack) := by
  induction k with
  | zero =>
    refine ⟨{initial with v3 := h.nextRef,v4 := 0,t9 := h.nextRef,t10 := -1},
      init0,init1,init2,rfl,rfl,?_⟩
    apply Reaches.prepend (Step.scc_pc17 _ _ _)
    apply Reaches.prepend (Step.scc_pc16 _ _ _)
    apply Reaches.prepend (Step.scc_pc15 _ _ _)
    apply Reaches.prepend (Step.scc_pc14 _ _ _)
    apply Reaches.prepend (Step.scc_pc13 _ _ _)
    apply Reaches.prepend (Step.scc_pc12 _ _ _)
    exact Reaches.refl _
  | succ k ih =>
    obtain ⟨s,sv0,sv1,sv2,sv3,sv4,run⟩ := ih (by omega)
    let mid := loopHeap h g.size (h.read ord) k
    have pre : Preserves h mid := loop_preserves _ _ _ _
    have size : field__a2l_import_0_UnweightedGraph_size mid s.v0 = some (g.size : Int) := by
      rw [sv0]; exact (graph_preserved pre graph g hg).2.1
    have ordField : field__a2l_import_1_DFSResult_order mid s.v1 = some ord := by
      rw [sv1]; exact result_order_preserved pre first ord valid fo
    have cond : decide (s.v4 < (field__a2l_import_0_UnweightedGraph_size mid s.v0).getD 0) = true := by
      simp only [size,Option.getD_some,sv4,decide_eq_true_eq]; omega
    refine ⟨{s with t8 := true,v4 := s.v4+1},sv0,sv1,sv2,sv3,?_,run.trans ?_⟩
    · simp [sv4]
    · apply Reaches.prepend (Step.scc_pc7 mid s stack (by rw [size]; rfl))
      apply Reaches.prepend (Step.scc_pc6_true _ _ _ cond)
      apply Reaches.prepend (Step.scc_pc11 _ _ _)
      have st : field__a2l_import_0_UnweightedGraph_size (mid.tick "graph_work" 1) s.v0 = some (g.size : Int) := size
      have ot : field__a2l_import_1_DFSResult_order (mid.tick "graph_work" 1) s.v1 = some ord := ordField
      apply Reaches.prepend (Step.scc_pc10 (mid.tick "graph_work" 1) _ stack (by
        change ((field__a2l_import_1_DFSResult_order (mid.tick "graph_work" 1) s.v1).isSome = true ∧
          (field__a2l_import_0_UnweightedGraph_size (mid.tick "graph_work" 1) s.v0).isSome = true ∧
          ((field__a2l_import_1_DFSResult_order (mid.tick "graph_work" 1) s.v1).getD 0 <
            (mid.tick "graph_work" 1).nextRef)) ∧ (s.v3 < (mid.tick "graph_work" 1).nextRef)
        simp [st,ot,sv3,mid]
        exact Nat.lt_succ_of_lt oa))
      apply Reaches.prepend (Step.scc_pc9 _ _ _)
      apply Reaches.prepend (Step.scc_pc8 _ _ _)
      change Reaches Step (.active _ (Frame.fn_scc 7 _) stack) _
      simp only [st,ot,Option.getD_some,Heap.read_tick]
      rw [show mid.read ord = h.read ord from old_read h g.size k (h.read ord) ord oa]
      simp only [cond]
      simpa only [loopHeap,sv3,sv4] using
        (Reaches.refl (.active (loopHeap h g.size (h.read ord) (k+1))
          (Frame.fn_scc 7 {s with t8 := true,v4 := s.v4+1}) stack) : Reaches Step _ _)


theorem reverse_order (g t : Graph) (ht : t.size = g.size) (order q : Seq)
    (ho : VertexOrder g order)
    (hq : ∀ i : Nat, i < g.size → q i = order ((g.size : Int) - 1 - i)) :
    VertexOrder t q := by
  obtain ⟨values,perm,vals⟩ := ho
  have len : values.length = g.size := by simpa using perm.length_eq
  refine ⟨values.reverse,?_,?_⟩
  · simpa only [ht] using (List.reverse_perm values).trans perm
  · intro i hi
    have hin : i < g.size := by omega
    have index : g.size - 1 - i < g.size := by omega
    have cast : ((g.size - 1 - i : Nat) : Int) = (g.size : Int) - 1 - i := by omega
    rw [hq i hin, ← cast, vals _ index]
    simp only [List.getElem!_eq_getElem?_getD,
      List.getElem?_reverse (by omega : i < values.length),len]

theorem call_compose (before h₁ h₂ after : Heap) (graph first transposed result ord : Nat)
    (g : Graph) (represented : GraphRep before graph g)
    (firstCall : Algo.dfs.dfs.Call (before.tick "graph_work" 1) graph h₁ first)
    (transposeCall : Algo.scc.transpose.Call (h₁.tick "graph_work" 1) graph h₂ transposed)
    (hg₂ : GraphRep h₂ graph g)
    (valid₁ : Algo.dfs.Algo2LeanGenerated.is_DFSResult h₂ first)
    (fo : field__a2l_import_1_DFSResult_order h₂ first = some ord)
    (oa : ord < h₂.nextRef)
    (secondCall : Algo.dfs.dfs_ordered.Call
      ((loopHeap h₂ g.size (h₂.read ord) g.size).tick "graph_work" 1)
      (transposed,h₂.nextRef) after result)
    (valid₂ : Algo.dfs.Algo2LeanGenerated.is_DFSResult after result) :
    Algo.scc.scc.Call before graph after result := by
  refine ⟨represented.1,?_⟩
  intro stack
  apply Reaches.prepend (Step.scc_pc25 _ _ _)
  apply Reaches.prepend (Step.scc_pc24 _ _ _)
  apply Reaches.prepend (Step.scc_pc23 _ _ _)
  let s₁ : State_scc := {v0 := graph,t14 := graph,t13 := first}
  refine (ModuleCall.summary import_1_simulates
    (fun value => match value with
      | .fn_dfs r => Frame.fn_scc 22 {v0 := graph,t14 := graph,t13 := r}
      | _ => .invalid) stack firstCall.2).trans ?_
  change Reaches Step (.active h₁ (Frame.fn_scc 22 s₁) stack) _
  apply Reaches.prepend (Step.scc_pc22 _ _ _)
  apply Reaches.prepend (Step.scc_pc21 _ _ _)
  apply Reaches.prepend (Step.scc_pc20 _ _ _)
  apply Reaches.prepend (Step.scc_pc19 _ _ _)
  have transposeRun := transposeCall.2 ((fun value => match value with
    | .fn_transpose r => Frame.fn_scc 18 {s₁ with v1 := first,t12 := graph,t11 := r}
    | _ => .invalid) :: stack)
  refine transposeRun.trans ?_
  change Reaches Step (.active h₂ (Frame.fn_scc 18 _) stack) _
  apply Reaches.prepend (Step.scc_pc18 _ _ _)
  let initial : State_scc := {s₁ with v1 := first,t12 := graph,t11 := transposed,v2 := transposed}
  change Reaches Step (.active h₂ (Frame.fn_scc 17 initial) stack) _
  obtain ⟨s,sv0,sv1,sv2,sv3,sv4,run⟩ := loop_execution h₂ graph first ord g
    hg₂ valid₁ fo oa transposed initial rfl rfl rfl g.size (by rfl) stack
  refine run.trans ?_
  let mid := loopHeap h₂ g.size (h₂.read ord) g.size
  have size : field__a2l_import_0_UnweightedGraph_size mid s.v0 = some (g.size : Int) := by
    rw [sv0]; exact (graph_preserved (loop_preserves _ _ _ _) graph g hg₂).2.1
  apply Reaches.prepend (Step.scc_pc7 mid s stack (by rw [size]; rfl))
  apply Reaches.prepend (Step.scc_pc6_false _ _ _ (by simp [size,sv4]))
  apply Reaches.prepend (Step.scc_pc5 _ _ _)
  apply Reaches.prepend (Step.scc_pc4 _ _ _)
  apply Reaches.prepend (Step.scc_pc3 _ _ _)
  apply Reaches.prepend (Step.scc_pc2 _ _ _)
  have imported := ModuleCall.summary import_1_simulates
    (fun value => match value with
      | .fn_dfs_ordered r => Frame.fn_scc 1 {s with t8 := false,t6 := transposed,t7 := h₂.nextRef,t5 := r}
      | _ => .invalid) stack secondCall.2
  have returned := Reaches.single (Step.scc_pc1 after
    {s with t8 := false,t6 := transposed,t7 := h₂.nextRef,t5 := result} stack valid₂)
  convert imported.trans returned using 1 <;>
    simp [sv2,sv3,size,sv4,mid,Algo.dfs.entry_dfs_ordered]
  funext value
  cases value <;> rfl

end SCCComposition

open SCCComposition

theorem solution :
    ∃ C : Nat, 0 < C ∧
      ∀ (before : Heap) (graph : ObjectRef) (g : Graph),
        GraphRep before graph g →
        ∃ after result,
          Algo.scc.scc.Call before graph after result ∧
          CLRS.SCC.Post before after result g ∧
          work before after ≤ C * (1 + g.size + edgeCount g) := by
  obtain ⟨C,hC,transpose⟩ := CLRS.SCC.transpose_correctness_and_running_time
  refine ⟨C+16,by omega,?_⟩
  intro before graph g represented
  have p₀ := preserves_tick before
  obtain ⟨h₁,first,call₁,post₁,bound₁⟩ := CLRS.DFS.correctness_and_explicit_running_time
    (before.tick "graph_work" 1) graph g (graph_preserved p₀ graph g represented)
  have p₁ := post₁.2.2.1
  have graph₁ := graph_preserved p₁ graph g (graph_preserved p₀ graph g represented)
  have ptick := preserves_tick h₁
  obtain ⟨h₂,transposed,callT,postT,boundT⟩ := transpose (h₁.tick "graph_work" 1) graph g
    (graph_preserved ptick graph g graph₁)
  obtain ⟨freshT,pT,t,trep,ht,edges⟩ := postT
  have p₁₂ := preserves_trans ptick pT
  have graph₂ := graph_preserved p₁₂ graph g graph₁
  rcases post₁ with ⟨valid₁,fresh₁,p₁',color₁,parent₁,discover₁,finish₁,order₁,component₁,
    hc₁,hp₁,hd₁,hf₁,ho₁,hb₁,arrays₁,clock₁,finished₁,black₁,k₁,hk₁,kn₁,forest₁⟩
  have oa₁ : order₁ < h₁.nextRef := (arrays₁.2 order₁ (by simp)).2
  have oa₂ : order₁ < h₂.nextRef := lt_of_lt_of_le oa₁ p₁₂.sequenceAllocation
  have orderEq : h₂.read order₁ = h₁.read order₁ := p₁₂.sequences order₁ oa₁
  have valid₁₂ : Algo.dfs.Algo2LeanGenerated.is_DFSResult h₂ first :=
    ⟨lt_of_lt_of_le valid₁.1 p₁₂.objectAllocation, by
      rw [classes_preserved p₁₂ first valid₁.1]; exact valid₁.2⟩
  have orderField := result_order_preserved p₁₂ first order₁ valid₁ ho₁
  let mid := (loopHeap h₂ g.size (h₂.read order₁) g.size).tick "graph_work" 1
  have prep : Preserves h₂ mid := preserves_trans (loop_preserves _ _ _ _) (preserves_tick _)
  have allocated : h₂.nextRef < mid.nextRef := by
    simp [mid]
  have reverse : ∀ i : Nat, i < g.size → mid.read h₂.nextRef i =
      h₁.read order₁ ((g.size : Int) - 1 - i) := by
    intro i hi
    simpa only [mid,Heap.read_tick,orderEq] using
      reversed_read h₂ g.size g.size i (h₂.read order₁) hi
  have orderValid := reverse_order g t ht.1 (h₁.read order₁) (mid.read h₂.nextRef)
    forest₁.finishOrder reverse
  obtain ⟨after,result,call₂,post₂,bound₂⟩ := CLRS.DFS.ordered_correctness_and_explicit_running_time
    mid transposed t h₂.nextRef (graph_preserved prep transposed t trep) allocated orderValid
  have p₂ := post₂.2.2.1
  have pre : Preserves before mid := preserves_trans p₀
    (preserves_trans p₁ (preserves_trans p₁₂ prep))
  refine ⟨after,result,call_compose before h₁ h₂ after graph first transposed result order₁ g
    represented call₁ callT graph₂ valid₁₂ orderField oa₂ call₂ post₂.1,?_,?_⟩
  · rcases post₂ with ⟨valid₂,fresh₂,p₂',color₂,parent₂,discover₂,finish₂,order₂,component₂,
      hc₂,hp₂,hd₂,hf₂,ho₂,hb₂,arrays₂,clock₂,finished₂,black₂,k₂,hk₂,kn₂,forest₂⟩
    have componentEq := CLRS.SCC.kosaraju_forest_components g t ht
      (fun i => i) (h₁.read parent₁) (h₁.read discover₁) (h₁.read finish₁)
      (h₁.read order₁) (h₁.read component₁) (mid.read h₂.nextRef)
      (after.read parent₂) (after.read discover₂) (after.read finish₂)
      (after.read order₂) (after.read component₂) k₁ k₂ forest₁ forest₂ reverse
    have vertexEq : ∀ v, Vertex t v ↔ Vertex g v := by
      intro v; simp only [Vertex,ht.1]
    refine ⟨valid₂,⟨pre.objectAllocation.trans fresh₂.1,fresh₂.2⟩,
      preserves_trans pre p₂,component₂,k₂,hb₂,hk₂,?_,?_,?_,?_,?_,componentEq⟩
    · refine ⟨by simp,?_⟩
      intro r hr
      have eq : r = component₂ := by simpa using hr
      subst r
      exact ⟨pre.sequenceAllocation.trans (arrays₂.2 component₂ (by simp)).1,
        (arrays₂.2 component₂ (by simp)).2⟩
    · simpa only [ht.1] using kn₂
    · constructor
      · intro zero
        by_contra ne
        have v0 : Vertex t 0 := by simp only [Vertex,ht.1]; omega
        have range := forest₂.componentRange 0 v0
        simp only [zero,Int.natCast_zero] at range
        omega
      · intro zero; rw [ht.1,zero] at kn₂; omega
    · intro v hv; exact forest₂.componentRange v ((vertexEq v).mpr hv)
    · intro label hl
      obtain ⟨v,hv,eq⟩ := forest₂.componentCoverage label hl
      exact ⟨v,(vertexEq v).mp hv,eq⟩
  · have baseClock : mid.clocks "graph_work" = h₂.clocks "graph_work" + 3 + 2*g.size := by
      simp only [mid,Heap.clocks_tick_same,(heap_meta h₂ g.size g.size (h₂.read order₁)).2.2.2.2.2]
      omega
    have mono₁ := p₁.workMonotone
    have monoT := pT.workMonotone
    have mono₂ := p₂.workMonotone
    simp only [work,Heap.cost,Heap.clocks_tick_same] at bound₁ boundT bound₂ mono₁ monoT mono₂ ⊢
    rw [ht.1,edges,baseClock] at bound₂
    rw [baseClock] at mono₂
    have total : after.clocks "graph_work" - before.clocks "graph_work" ≤
        C*(1+g.size+edgeCount g)+16+16*g.size+4*edgeCount g := by omega
    exact total.trans (by simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one]; omega)
