-- Prove2me | solution 1 for CLRS.BFS.correctness_and_explicit_running_time
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T03:41:47.205+00:00
-- url     : https://prove2.me/submissions/d2f27b64-3e2d-49ed-8e75-ce1014130c75

import Definitions.Def_CLRS_BFS_Program
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Ring.Nat

set_option autoImplicit false
open Algo2LeanGenerated CLRS.GraphTraversal CLRS.BFS Algo2LeanCore
open Algo.bfs.Algo2LeanGenerated

namespace BFSProof

structure Data where
  d : Seq
  p : Seq
  q : List Int

def add (a : Data) (u v : Int) : Data :=
  if a.d v = -1 then
    ⟨Function.update a.d v (a.d u + 1), Function.update a.p v u, a.q ++ [v]⟩
  else a

structure Inv (g : Graph) (s : Int) (head : Nat) (a : Data) : Prop where
  nodup : a.q.Nodup
  valid : ∀ v ∈ a.q, Vertex g v
  head_le : head ≤ a.q.length
  source_mem : s ∈ a.q
  source_d : a.d s = 0
  source_p : a.p s = -1
  unseen : ∀ v, v ∉ a.q → a.d v = -1 ∧ a.p v = -1
  nonneg : ∀ v ∈ a.q, 0 ≤ a.d v
  paths : ∀ v ∈ a.q, Walk g (a.d v).toNat s v
  parent : ∀ v ∈ a.q, v ≠ s → Edge g (a.p v) v ∧ a.d (a.p v) + 1 = a.d v
  sorted : ∀ i j : Nat, i ≤ j → j < a.q.length → a.d a.q[i]! ≤ a.d a.q[j]!
  layers : ∀ i j : Nat, head ≤ i → i ≤ j → j < a.q.length →
    a.d a.q[i]! ≤ a.d a.q[j]! ∧ a.d a.q[j]! ≤ a.d a.q[i]! + 1
  scanned : ∀ i : Nat, i < head → ∀ v, Edge g a.q[i]! v →
    v ∈ a.q ∧ a.d v ≤ a.d a.q[i]! + 1

structure Ext (a b : Data) : Prop where
  initial_segment : a.q <+: b.q
  distance : ∀ v ∈ a.q, b.d v = a.d v
  parent : ∀ v ∈ a.q, b.p v = a.p v

theorem ext_refl (a : Data) : Ext a a := ⟨by exact ⟨[],by simp⟩,by intros; rfl,by intros; rfl⟩
theorem ext_trans {a b c : Data} (ab : Ext a b) (bc : Ext b c) : Ext a c := by
  refine ⟨ab.initial_segment.trans bc.initial_segment,?_,?_⟩
  · intro v hv; rw [bc.distance v (ab.initial_segment.subset hv),ab.distance v hv]
  · intro v hv; rw [bc.parent v (ab.initial_segment.subset hv),ab.parent v hv]

theorem walk_append_edge {g : Graph} {n : Nat} {s u v : Int}
    (w : Walk g n s u) (e : Edge g u v) : Walk g (n+1) s v := by
  induction w with
  | zero _ _ => exact .cons e (.zero v e.2.1)
  | cons f w ih => exact .cons f (ih e)

theorem get_mem {xs : List Int} {i : Nat} (hi : i < xs.length) : xs[i]! ∈ xs := by
  rw [getElem!_pos xs i hi]
  exact List.getElem_mem hi

@[simp] theorem get_append_last (xs : List Int) (v : Int) : (xs++[v])[xs.length]! = v := by
  simp [List.getElem!_eq_getElem?_getD,List.getElem?_append]

theorem queued_get {g : Graph} {s : Int} {head : Nat} {a : Data} (h : Inv g s head a)
    (i : Nat) (hi : i < a.q.length) : a.q[i]! ∈ a.q := get_mem hi

theorem add_ext {g : Graph} {s : Int} {head : Nat} {a : Data} (h : Inv g s head a)
    (u v : Int) : Ext a (add a u v) := by
  unfold add
  split_ifs with hv
  · have absent : v ∉ a.q := by intro mem; have := h.nonneg v mem; omega
    refine ⟨List.prefix_append _ _,?_,?_⟩
    · intro w hw; have ne : w ≠ v := by rintro rfl; exact absent hw
      simp [Function.update, ne]
    · intro w hw; have ne : w ≠ v := by rintro rfl; exact absent hw
      simp [Function.update, ne]
  · exact ext_refl a

theorem add_inv {g : Graph} {s : Int} {head : Nat} {a : Data} (h : Inv g s head a)
    (active : head < a.q.length) (v : Int) (edge : Edge g a.q[head]! v) :
    Inv g s head (add a a.q[head]! v) ∧
      v ∈ (add a a.q[head]! v).q ∧
      (add a a.q[head]! v).d v ≤ (add a a.q[head]! v).d a.q[head]! + 1 := by
  let u := a.q[head]!
  have um : u ∈ a.q := get_mem active
  have un := h.nonneg u um
  have extension := add_ext h u v
  by_cases old : v ∈ a.q
  · have vn := h.nonneg v old
    have same : add a u v = a := by simp [add, show a.d v ≠ -1 by omega]
    rw [same]
    refine ⟨h,old,?_⟩
    obtain ⟨j,hj,jv⟩ := List.getElem_of_mem old
    by_cases before : j < head
    · have lower := h.sorted j head (by omega) active
      have jv' : a.q[j]! = v := by simpa only [getElem!_pos a.q j hj] using jv
      rw [jv'] at lower
      omega
    · have layer := h.layers head j (le_refl _) (by omega) hj
      have jv' : a.q[j]! = v := by simpa only [getElem!_pos a.q j hj] using jv
      simpa [u,jv'] using layer.2
  · have dv : a.d v = -1 := (h.unseen v old).1
    have vu : v ≠ u := by rintro rfl; exact old um
    have vs : v ≠ s := by rintro rfl; exact old h.source_mem
    have simp_add : add a u v =
        ⟨Function.update a.d v (a.d u+1),Function.update a.p v u,a.q++[v]⟩ := by simp [add,dv]
    rw [simp_add]
    have d_old : ∀ w ∈ a.q, Function.update a.d v (a.d u+1) w = a.d w := by
      intro w hw; exact Function.update_of_ne (by rintro rfl; exact old hw) _ _
    have p_old : ∀ w ∈ a.q, Function.update a.p v u w = a.p w := by
      intro w hw; exact Function.update_of_ne (by rintro rfl; exact old hw) _ _
    have get_old : ∀ i, i < a.q.length → (a.q++[v])[i]! = a.q[i]! := by
      intro i hi; simp [List.getElem!_eq_getElem?_getD,List.getElem?_append,hi]
    dsimp only
    constructor
    · constructor <;> dsimp only
      · simpa using h.nodup.append (List.nodup_singleton v) (by simpa using old)
      · intro w hw; simp only [List.mem_append,List.mem_singleton] at hw
        rcases hw with hw | rfl
        · exact h.valid w hw
        · exact edge.2.1
      · simp; omega
      · simp [h.source_mem]
      · exact (d_old s h.source_mem).trans h.source_d
      · exact (p_old s h.source_mem).trans h.source_p
      · intro w hw
        have wq : w ∉ a.q := by intro mem; exact hw (List.mem_append_left _ mem)
        have wv : w ≠ v := by rintro rfl; exact hw (by simp)
        simpa [Function.update,wv] using h.unseen w wq
      · intro w hw; simp only [List.mem_append,List.mem_singleton] at hw
        rcases hw with hw | rfl
        · rw [d_old w hw]; exact h.nonneg w hw
        · simp; omega
      · intro w hw; simp only [List.mem_append,List.mem_singleton] at hw
        rcases hw with hw | rfl
        · rw [d_old w hw]; exact h.paths w hw
        · simp only [Function.update_self]
          have len : (a.d u+1).toNat = (a.d u).toNat + 1 := by omega
          rw [len]; exact walk_append_edge (h.paths u um) edge
      · intro w hw ws; simp only [List.mem_append,List.mem_singleton] at hw
        rcases hw with hw | rfl
        · rw [p_old w hw,d_old w hw]
          obtain ⟨e,pd⟩ := h.parent w hw ws
          have np : a.p w ≠ v := by
            intro eq; rw [eq,dv] at pd
            have wn := h.nonneg w hw
            have wp := h.paths w hw
            -- A discovered nonsource vertex has positive distance.
            have zero_ne : a.d w ≠ 0 := by
              intro z; rw [z] at wp; cases wp; exact ws rfl
            omega
          simpa [Function.update,np] using And.intro e pd
        · simp only [Function.update_self]
          exact ⟨edge,by rw [d_old u um]⟩
      · intro i j hij hj
        have ji : j ≤ a.q.length := by simp only [List.length_append,List.length_singleton] at hj; omega
        by_cases jl : j < a.q.length
        · rw [get_old i (by omega),get_old j jl,d_old _ (get_mem (by omega)),d_old _ (get_mem jl)]
          exact h.sorted i j hij jl
        · have je : j = a.q.length := by omega
          subst j; rw [get_append_last,Function.update_self]
          by_cases il : i < a.q.length
          · rw [get_old i il,d_old _ (get_mem il)]
            by_cases ih : i < head
            · have le := h.sorted i head (by omega) active; change a.d a.q[i]! ≤ a.d u at le; omega
            · have le := h.layers head i (le_refl _) (by omega) il; change a.d u ≤ a.d a.q[i]! ∧ a.d a.q[i]! ≤ a.d u+1 at le; omega
          · have ie : i = a.q.length := by omega
            subst i; rw [get_append_last,Function.update_self]
      · intro i j hi hij hj
        have ji : j ≤ a.q.length := by simp only [List.length_append,List.length_singleton] at hj; omega
        by_cases jl : j < a.q.length
        · rw [get_old i (by omega),get_old j jl,d_old _ (get_mem (by omega)),
            d_old _ (get_mem jl)]
          exact h.layers i j hi hij jl
        · have je : j = a.q.length := by omega
          subst j
          rw [get_append_last,Function.update_self]
          by_cases il : i < a.q.length
          · rw [get_old i il,d_old _ (get_mem il)]
            have lay := h.layers head i (le_refl _) hi il
            change a.d u ≤ a.d a.q[i]! ∧ a.d a.q[i]! ≤ a.d u+1 at lay
            exact ⟨by omega,by omega⟩
          · have ie : i = a.q.length := by omega
            subst i; simp
      · intro i hi w ew
        rw [get_old i (by omega)] at ew ⊢
        obtain ⟨wm,wl⟩ := h.scanned i hi w ew
        refine ⟨List.mem_append_left _ wm,?_⟩
        rw [d_old w wm,d_old _ (get_mem (by omega))]; exact wl
    · simp only [List.mem_append,List.mem_singleton,or_true,true_and,Function.update_self]
      rw [d_old u um]


theorem ext_get {a b : Data} (h : Ext a b) {i : Nat} (hi : i < a.q.length) :
    b.q[i]! = a.q[i]! := by
  rw [getElem!_pos a.q i hi,getElem!_pos b.q i (lt_of_lt_of_le hi h.initial_segment.length_le)]
  exact (h.initial_segment.getElem hi).symm

def scan (u : Int) : List Nat → Data → Data
  | [],a => a
  | v::vs,a => scan u vs (add a u v)

theorem scan_inv {g : Graph} {s : Int} {head : Nat} {a : Data} (h : Inv g s head a)
    (active : head < a.q.length) (vs : List Nat)
    (edges : ∀ v ∈ vs, Edge g a.q[head]! v) :
    Inv g s head (scan a.q[head]! vs a) ∧ Ext a (scan a.q[head]! vs a) ∧
      ∀ v ∈ vs, (v : Int) ∈ (scan a.q[head]! vs a).q ∧
        (scan a.q[head]! vs a).d v ≤ (scan a.q[head]! vs a).d a.q[head]! + 1 := by
  induction vs generalizing a with
  | nil => exact ⟨h,ext_refl a,by simp⟩
  | cons v vs ih =>
    let b := add a a.q[head]! v
    have ex : Ext a b := add_ext h _ _
    have bh : Inv g s head b := (add_inv h active v (edges v (by simp))).1
    have ba : head < b.q.length := lt_of_lt_of_le active ex.initial_segment.length_le
    have eq : b.q[head]! = a.q[head]! := ext_get ex active
    have es : ∀ w ∈ vs, Edge g b.q[head]! w := by intro w hw; rw [eq]; exact edges w (by simp [hw])
    obtain ⟨ch,cx,ce⟩ := ih bh ba es
    rw [eq] at ch cx ce
    refine ⟨ch,ext_trans ex cx,?_⟩
    intro w hw
    rcases List.mem_cons.mp hw with hw | hw
    · subst w
      obtain ⟨_,vm,vl⟩ := add_inv h active v (edges v (by simp))
      refine ⟨cx.initial_segment.subset vm,?_⟩
      change (scan a.q[head]! vs b).d v ≤ (scan a.q[head]! vs b).d a.q[head]! + 1
      rw [cx.distance _ vm,cx.distance _ (ex.initial_segment.subset (get_mem active))]
      exact vl
    · exact ce w hw

theorem scan_next {g : Graph} {s : Int} {head : Nat} {a : Data} (h : Inv g s head a)
    (active : head < a.q.length) :
    Inv g s (head+1) (scan a.q[head]! (g.neighbors a.q[head]!.toNat) a) ∧
      Ext a (scan a.q[head]! (g.neighbors a.q[head]!.toNat) a) := by
  have uvalid := h.valid _ (get_mem active)
  have es : ∀ v ∈ g.neighbors a.q[head]!.toNat, Edge g a.q[head]! v := by
    intro v hv
    exact ⟨uvalid,⟨by omega,by have := g.bounded _ (by rcases uvalid with ⟨_,_⟩; omega) v hv; omega⟩,by simpa using hv⟩
  obtain ⟨bh,ex,be⟩ := scan_inv h active _ es
  refine ⟨{ bh with head_le := ?_, layers := ?_,scanned := ?_ },ex⟩
  · have := ex.initial_segment.length_le; omega
  · intro i j hi hij hj; exact bh.layers i j (by omega) hij hj
  · intro i hi v ev
    by_cases old : i < head
    · exact bh.scanned i old v ev
    · have eqi : i = head := by omega
      subst i
      rw [ext_get ex active] at ev ⊢
      have := be v.toNat ev.2.2
      simpa only [Int.toNat_of_nonneg ev.2.1.1] using this

def start (s : Int) : Data :=
  ⟨Function.update (fun _ => -1) s 0, fun _ => -1,[s]⟩

theorem start_inv (g : Graph) (s : Int) (hs : Vertex g s) : Inv g s 0 (start s) := by
  refine {
    nodup := by simp [start]
    valid := ?_
    head_le := by simp [start]
    source_mem := by simp [start]
    source_d := by simp [start]
    source_p := rfl
    unseen := ?_
    nonneg := ?_
    paths := ?_
    parent := ?_
    sorted := ?_
    layers := ?_
    scanned := ?_ }
  · intro v hv; have : v = s := by simpa [start] using hv
    simpa [this] using hs
  · intro v hv; have ne : v ≠ s := by simpa [start] using hv
    simp [start,Function.update,ne]
  · intro v hv; have : v = s := by simpa [start] using hv
    simp [this,start]
  · intro v hv; have : v = s := by simpa [start] using hv
    simpa [this,start] using Walk.zero s hs
  · intro v hv ne; have : v = s := by simpa [start] using hv
    exact False.elim (ne this)
  · intro i j hij hj; have ji : i=0 ∧ j=0 := by simp only [start,List.length_singleton] at hj; omega
    rcases ji with ⟨rfl,rfl⟩; simp
  · intro i j hi hij hj; have ji : i=0 ∧ j=0 := by simp only [start,List.length_singleton] at hj; omega
    rcases ji with ⟨rfl,rfl⟩; simp
  · intro i hi; omega

def run (g : Graph) : Nat → Nat → Data → Data
  | 0,_,a => a
  | fuel+1,head,a => if head < a.q.length then
      run g fuel (head+1) (scan a.q[head]! (g.neighbors a.q[head]!.toNat) a)
    else a

theorem queue_bound {g : Graph} {s : Int} {head : Nat} {a : Data} (h : Inv g s head a) :
    a.q.length ≤ g.size := by
  have sub : a.q ⊆ (List.range g.size).map Int.ofNat := by
    intro v hv
    have vv := h.valid v hv
    apply List.mem_map.mpr
    exact ⟨v.toNat,List.mem_range.mpr (by rcases vv with ⟨_,_⟩; omega),Int.toNat_of_nonneg vv.1⟩
  simpa using h.nodup.length_le_of_subset sub

theorem run_inv {g : Graph} {s : Int} {head fuel : Nat} {a : Data} (h : Inv g s head a)
    (enough : g.size ≤ head + fuel) :
    ∃ finalHead, Inv g s finalHead (run g fuel head a) ∧
      finalHead = (run g fuel head a).q.length ∧ Ext a (run g fuel head a) := by
  induction fuel generalizing head a with
  | zero => exact ⟨head,h,by change head = a.q.length; have := queue_bound h; have := h.head_le; omega,ext_refl a⟩
  | succ fuel ih =>
    by_cases active : head < a.q.length
    · obtain ⟨bh,ex⟩ := scan_next h active
      obtain ⟨k,kh,ke,kx⟩ := ih bh (by omega)
      exact ⟨k,by simpa [run,active] using kh,by simpa [run,active] using ke,
        by simpa [run,active] using ext_trans ex kx⟩
    · exact ⟨head,by simpa [run,active] using h,by simpa [run,active] using h.head_le.antisymm (by omega),
        by simpa [run,active] using ext_refl a⟩

theorem finished_edge {g : Graph} {s : Int} {head : Nat} {a : Data} (h : Inv g s head a)
    (done : head = a.q.length) {u v : Int} (um : u ∈ a.q) (e : Edge g u v) :
    v ∈ a.q ∧ a.d v ≤ a.d u + 1 := by
  obtain ⟨i,hi,eq⟩ := List.getElem_of_mem um
  have eq' : a.q[i]! = u := by simpa only [getElem!_pos a.q i hi] using eq
  have := h.scanned i (by omega) v (by simpa [eq'] using e)
  simpa [eq'] using this

theorem finished_walk {g : Graph} {s : Int} {head : Nat} {a : Data} (h : Inv g s head a)
    (done : head = a.q.length) {u v : Int} {n : Nat} (w : Walk g n u v) :
    u ∈ a.q → v ∈ a.q ∧ a.d v ≤ a.d u + (n : Int) := by
  induction w with
  | zero v hv => intro vm; exact ⟨vm,by omega⟩
  | cons e w ih =>
    intro um
    obtain ⟨vm,vl⟩ := finished_edge h done um e
    obtain ⟨wm,wl⟩ := ih vm
    exact ⟨wm,by push_cast; omega⟩

theorem finished_correct {g : Graph} {s : Int} {head : Nat} {a : Data} (h : Inv g s head a)
    (done : head = a.q.length) : ∀ v, Vertex g v →
      -1 ≤ a.d v ∧ (a.d v = -1 ↔ ¬ Reachable g s v) ∧
      (0 ≤ a.d v → Shortest g s v (a.d v).toNat) ∧
      (a.d v = -1 → a.p v = -1) ∧
      (v ≠ s → 0 ≤ a.d v → Edge g (a.p v) v ∧ a.d (a.p v)+1 = a.d v) := by
  intro v vv
  by_cases vm : v ∈ a.q
  · have vn := h.nonneg v vm
    have vp := h.paths v vm
    refine ⟨by omega,?_,?_,by omega,by intros ne _; exact h.parent v vm ne⟩
    · constructor
      · omega
      · intro nr; exact False.elim (nr ⟨_,vp⟩)
    · intro _; refine ⟨vp,?_⟩
      intro n w
      have le := (finished_walk h done w h.source_mem).2
      rw [h.source_d] at le; omega
  · obtain ⟨dv,pv⟩ := h.unseen v vm
    refine ⟨by omega,?_,by omega,by intro _; exact pv,by omega⟩
    constructor
    · intro _ ⟨n,w⟩; exact vm (finished_walk h done w h.source_mem).1
    · intro _; exact dv


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


@[simp] theorem result_tick (h : Heap) (r : ObjectRef) (k : Nat) :
    is_BFSResult (h.tick "graph_work" k) r ↔ is_BFSResult h r := Iff.rfl
@[simp] theorem result_write (h : Heap) (r : ObjectRef) (ref : SeqRef) (i v : Int) :
    is_BFSResult (h.write ref i v) r ↔ is_BFSResult h r := Iff.rfl
@[simp] theorem dist_tick (h : Heap) (r : ObjectRef) (k : Nat) :
    field_BFSResult_distance (h.tick "graph_work" k) r = field_BFSResult_distance h r := rfl
@[simp] theorem dist_write (h : Heap) (r : ObjectRef) (ref : SeqRef) (i v : Int) :
    field_BFSResult_distance (h.write ref i v) r = field_BFSResult_distance h r := rfl
@[simp] theorem par_tick (h : Heap) (r : ObjectRef) (k : Nat) :
    field_BFSResult_parent (h.tick "graph_work" k) r = field_BFSResult_parent h r := rfl
@[simp] theorem par_write (h : Heap) (r : ObjectRef) (ref : SeqRef) (i v : Int) :
    field_BFSResult_parent (h.write ref i v) r = field_BFSResult_parent h r := rfl

structure Rep (before h : Heap) (result distance parent queue : Nat) (a : Data) : Prop where
  preserves : Preserves before h
  fresh : FreshArrays before h [distance,parent,queue]
  fresh_result : FreshObject before h result
  valid : is_BFSResult h result
  dist_field : field_BFSResult_distance h result = some distance
  par_field : field_BFSResult_parent h result = some parent
  dist : h.read distance = a.d
  par : h.read parent = a.p
  queued : ∀ i : Nat, i < a.q.length → h.read queue i = a.q[i]!

theorem Rep.tick {before h : Heap} {r d p q : Nat} {a : Data} (rep : Rep before h r d p q a)
    (k : Nat) : Rep before (h.tick "graph_work" k) r d p q a := by
  exact ⟨preserves_trans rep.preserves (preserves_tick _ _),rep.fresh,rep.fresh_result,
    rep.valid,rep.dist_field,rep.par_field,rep.dist,rep.par,rep.queued⟩

theorem Rep.sep {before h : Heap} {r d p q : Nat} {a : Data} (rep : Rep before h r d p q a) :
    d ≠ p ∧ d ≠ q ∧ p ≠ q := by
  have t : (d ≠ p ∧ d ≠ q) ∧ p ≠ q := by simpa [FreshArrays,List.pairwise_cons] using rep.fresh.1
  exact ⟨t.1.1,t.1.2,t.2⟩

def edgeHeap (h : Heap) (d p q : Nat) (a : Data) (u v : Int) : Heap :=
  if a.d v = -1 then
    (((((h.tick "graph_work" 1).tick "graph_work" 1).write d v (a.d u+1)).write p v u).write q a.q.length v).tick "graph_work" 1
  else (h.tick "graph_work" 1).tick "graph_work" 1

theorem edge_rep {before h : Heap} {r d p q : Nat} {a : Data} {g : Graph} {s : Int} {head : Nat}
    (rep : Rep before h r d p q a) (inv : Inv g s head a) (u v : Int) :
    Rep before (edgeHeap h d p q a u v) r d p q (add a u v) := by
  by_cases dv : a.d v = -1
  · have ne := rep.sep
    have vm : v ∉ a.q := by intro mem; have := inv.nonneg v mem; omega
    have fr : ∀ ref ∈ [d,p,q], before.nextRef ≤ ref := fun ref mem => (rep.fresh.2 ref mem).1
    have pr := preserves_write (preserves_write (preserves_write
      (preserves_trans (preserves_trans rep.preserves (preserves_tick _ 1)) (preserves_tick _ 1))
      d (fr d (by simp)) v (a.d u+1)) p (fr p (by simp)) v u) q (fr q (by simp)) a.q.length v
    simp only [edgeHeap,if_pos dv]
    refine ⟨preserves_trans pr (preserves_tick _ 1),rep.fresh,rep.fresh_result,rep.valid,
      rep.dist_field,rep.par_field,?_,?_,?_⟩
    · funext w
      simp only [edgeHeap,if_pos dv,add,Heap.read_tick]
      rw [Heap.read_write_other_ref _ d q _ _ _ ne.2.1,
        Heap.read_write_other_ref _ d p _ _ _ ne.1]
      by_cases eq : w = v
      · subst w; simp
      · rw [Heap.read_write_other_index _ _ _ _ _ eq]
        simp [Function.update,eq,rep.dist]
    · funext w
      simp only [edgeHeap,if_pos dv,add,Heap.read_tick]
      rw [Heap.read_write_other_ref _ p q _ _ _ ne.2.2]
      by_cases eq : w = v
      · subst w; simp
      · rw [Heap.read_write_other_index _ _ _ _ _ eq,Heap.read_write_other_ref _ p d _ _ _ ne.1.symm]
        simp [Function.update,eq,rep.par]
    · intro i hi
      simp only [add,if_pos dv,List.length_append,List.length_singleton] at hi ⊢
      simp only [edgeHeap,if_pos dv,Heap.read_tick]
      by_cases eq : i = a.q.length
      · subst i; rw [Heap.read_write_same]; exact (get_append_last _ _).symm
      · have il : i < a.q.length := by omega
        rw [Heap.read_write_other_index _ _ _ _ _ (by omega),
          Heap.read_write_other_ref _ q p _ _ _ ne.2.2.symm,
          Heap.read_write_other_ref _ q d _ _ _ ne.2.1.symm,Heap.read_tick,Heap.read_tick,rep.queued i il]
        simp [List.getElem!_eq_getElem?_getD,List.getElem?_append,il]
  · simpa [edgeHeap,add,dv] using (rep.tick 1).tick 1

theorem edge_clock {h : Heap} {d p q : Nat} {a : Data} {g : Graph} {s : Int} {head : Nat}
    (inv : Inv g s head a) (u v : Int) :
    (edgeHeap h d p q a u v).clocks "graph_work" + a.q.length =
      h.clocks "graph_work" + 2 + (add a u v).q.length := by
  by_cases hv : a.d v = -1 <;> simp [edgeHeap,add,hv] <;> omega

def scanHeap (d p q : Nat) (u : Int) : List Nat → Data → Heap → Heap
  | [],_,h => h
  | v::vs,a,h => scanHeap d p q u vs (add a u v) (edgeHeap h d p q a u v)

theorem scan_rep {before h : Heap} {r d p q : Nat} {a : Data} {g : Graph} {s : Int} {head : Nat}
    (rep : Rep before h r d p q a) (inv : Inv g s head a) (active : head < a.q.length)
    (vs : List Nat) (edges : ∀ v ∈ vs, Edge g a.q[head]! v) :
    Rep before (scanHeap d p q a.q[head]! vs a h) r d p q (scan a.q[head]! vs a) ∧
      (scanHeap d p q a.q[head]! vs a h).clocks "graph_work" + a.q.length =
        h.clocks "graph_work" + 2*vs.length + (scan a.q[head]! vs a).q.length := by
  induction vs generalizing a h with
  | nil => exact ⟨rep,by simp [scanHeap,scan]⟩
  | cons v vs ih =>
    let b := add a a.q[head]! v
    have ex : Ext a b := add_ext inv _ _
    have bh := (add_inv inv active v (edges v (by simp))).1
    have ba : head < b.q.length := lt_of_lt_of_le active ex.initial_segment.length_le
    have eq : b.q[head]! = a.q[head]! := ext_get ex active
    obtain ⟨rp,rc⟩ := ih (edge_rep rep inv _ _) bh ba
      (by intro w hw; rw [eq]; exact edges w (by simp [hw]))
    rw [eq] at rp rc
    refine ⟨rp,?_⟩
    have ec := edge_clock (h:=h) (d:=d) (p:=p) (q:=q) inv a.q[head]! v
    change _ + a.q.length = _
    dsimp only [scanHeap,scan,List.length_cons]
    omega


@[simp] theorem get_tick (h : Heap) (r : CollectionRef) (i : Int) (k : Nat) :
    seq_Seq_Int.get (h.tick "graph_work" k) r i = seq_Seq_Int.get h r i := rfl
@[simp] theorem get_write (h : Heap) (r : CollectionRef) (i : Int) (a : SeqRef) (j v : Int) :
    seq_Seq_Int.get (h.write a j v) r i = seq_Seq_Int.get h r i := rfl
@[simp] theorem adj_tick (h : Heap) (r : ObjectRef) (k : Nat) :
    field__a2l_import_0_UnweightedGraph_adj (h.tick "graph_work" k) r = field__a2l_import_0_UnweightedGraph_adj h r := rfl

theorem scan_execution (before h : Heap) (g : Graph) (r d p q : Nat) (a : Data)
    (s : State_bfs) (head : Nat) (rep : Rep before h r d p q a) (inv : Inv g s.v1 head a)
    (active : head < a.q.length) (hg : GraphRep before s.v0 g)
    (sr : s.v2 = r) (sq : s.v4 = q) (su : s.v3 = a.q[head]!)
    (tail : s.v6 = (a.q.length : Int)) (vs pre : List Nat)
    (row : g.neighbors a.q[head]!.toNat = pre ++ vs) (index : s.v7 = (pre.length : Int))
    (stack : Stack) :
    ∃ s' : State_bfs,
      s'.v0 = s.v0 ∧ s'.v1 = s.v1 ∧ s'.v2 = r ∧ s'.v3 = s.v3 ∧ s'.v4 = q ∧
      s'.v5 = s.v5 ∧ s'.v6 = ((scan a.q[head]! vs a).q.length : Int) ∧
      Reaches Step (.active h (Frame.fn_bfs 8 s) stack)
        (.active ((scanHeap d p q a.q[head]! vs a h).tick "graph_work" 1)
          (Frame.fn_bfs 5 s') stack) := by
  induction vs generalizing h a s pre with
  | nil =>
    have curr := graph_preserved rep.preserves hg
    obtain ⟨adj,deg,ha,hd,hav,hdv,rows⟩ := curr.2.2
    have uv := inv.valid _ (get_mem active)
    have du := (rows a.q[head]!.toNat (by rcases uv with ⟨_,_⟩; omega)).1
    rw [Int.toNat_of_nonneg uv.1] at du
    have cond : decide (s.v7 < h.read ((field__a2l_import_0_UnweightedGraph_degree h s.v0).getD 0) s.v3) = false := by
      simp only [hd,Option.getD_some,su,du,index,row,List.append_nil]; simp
    refine ⟨{s with t11 := false},rfl,rfl,sr,rfl,sq,rfl,by simpa [scan] using tail,?_⟩
    apply Reaches.prepend (Step.bfs_pc8 _ _ _ (by simp [hd,hdv]))
    apply Reaches.prepend (Step.bfs_pc7_false _ _ _ cond)
    apply Reaches.prepend (Step.bfs_pc6 _ _ _)
    simpa only [cond,scanHeap] using (Reaches.refl (step:=Step) (.active (h.tick "graph_work" 1) (Frame.fn_bfs 5 {s with t11 := false}) stack))
  | cons v vs ih =>
    have curr := graph_preserved rep.preserves hg
    obtain ⟨adj,deg,ha,hd,hav,hdv,rows⟩ := curr.2.2
    have uv := inv.valid _ (get_mem active)
    obtain ⟨du,rr,getr,rv,vals⟩ := rows a.q[head]!.toNat (by rcases uv with ⟨_,_⟩; omega)
    rw [Int.toNat_of_nonneg uv.1] at du getr
    have getb : seq_Seq_Int.get h adj a.q[head]! = some rr := getr
    have atj : h.read rr s.v7 = (v : Int) := by
      rw [index,vals pre.length (by rw [row]; simp)]
      rw [row]
      simp
    have cond : decide (s.v7 < h.read ((field__a2l_import_0_UnweightedGraph_degree h s.v0).getD 0) s.v3) = true := by
      simp only [hd,Option.getD_some,su,du,index,row,List.length_append,List.length_cons]
      simp
    have vm : v ∈ g.neighbors a.q[head]!.toNat := by rw [row]; simp
    have vb := g.bounded a.q[head]!.toNat (by rcases uv with ⟨_,_⟩; omega) v vm
    have edge : Edge g a.q[head]! v := ⟨uv,⟨by omega,by omega⟩,by simpa using vm⟩
    have cond' : decide (s.v7 < h.read ((field__a2l_import_0_UnweightedGraph_degree h s.v0).getD 0) a.q[head]!) = true := by simpa only [su] using cond
    let b := add a a.q[head]! v
    let h' := edgeHeap h d p q a a.q[head]! v
    have ex : Ext a b := add_ext inv _ _
    have bh := (add_inv inv active v edge).1
    have ba : head < b.q.length := lt_of_lt_of_le active ex.initial_segment.length_le
    have beq : b.q[head]! = a.q[head]! := ext_get ex active
    have rep' : Rep before h' r d p q b := edge_rep rep inv _ _
    have row' : g.neighbors b.q[head]!.toNat = (pre++[v]) ++ vs := by rw [beq,row]; simp
    have dv := rep.dist_field
    have pv := rep.par_field
    have da := (rep.fresh.2 d (by simp)).2
    have pa := (rep.fresh.2 p (by simp)).2
    have qa := (rep.fresh.2 q (by simp)).2
    by_cases unseen : a.d v = -1
    · let sn : State_bfs := {s with t11 := true, t12 := true, v8 := v, v6 := s.v6+1,v7 := s.v7+1}
      have sn_tail : sn.v6 = (b.q.length : Int) := by simp [sn,b,add,unseen,tail]
      obtain ⟨sf,s0,s1,s2,s3,s4,s5,s6,run⟩ := ih h' b sn rep'
        (by simpa only [sn] using bh) ba (by simpa [sn] using hg)
        (by simpa [sn] using sr) (by simpa [sn] using sq)
        (by simpa [sn,beq] using su) sn_tail (pre++[v]) row' (by simp [sn,index])
      refine ⟨sf,by simpa [sn] using s0,by simpa [sn] using s1,s2,
        by simpa [sn] using s3,s4,by simpa [sn] using s5,by simpa only [beq,scan] using s6,?_⟩
      apply Reaches.prepend (Step.bfs_pc8 _ _ _ (by simp [hd,hdv]))
      apply Reaches.prepend (Step.bfs_pc7_true _ _ _ cond)
      apply Reaches.prepend (Step.bfs_pc19 _ _ _)
      apply Reaches.prepend (Step.bfs_pc18 _ _ _ (by simpa only [adj_tick,get_tick,ha,su,Option.getD_some,getb,Option.isSome_some,true_and,Heap.tick_nextRef] using rv))
      apply Reaches.prepend (Step.bfs_pc17 _ _ _ (by simp [sr,dv,da]))
      apply Reaches.prepend (Step.bfs_pc16_true _ _ _ (by simp only [adj_tick,get_tick,ha,su,getb,atj,sr,dv,dist_tick,Option.getD_some,Heap.read_tick,rep.dist,unseen]; rfl))
      apply Reaches.prepend (Step.bfs_pc15 _ _ _)
      apply Reaches.prepend (Step.bfs_pc14 _ _ _ (by simp [sr,dv,da]))
      apply Reaches.prepend (Step.bfs_pc13 _ _ _ (by simp [sr,pv,pa]))
      apply Reaches.prepend (Step.bfs_pc12 _ _ _ (by simpa [sq] using qa))
      apply Reaches.prepend (Step.bfs_pc11 _ _ _)
      apply Reaches.prepend (Step.bfs_pc10 _ _ _)
      apply Reaches.prepend (Step.bfs_pc9 _ _ _)
      simpa only [scanHeap,scan,h',b,edgeHeap,if_pos unseen,sn,sr,sq,su,adj_tick,get_tick,ha,getb,atj,dv,pv,
        dist_tick,dist_write,par_tick,par_write,Option.getD_some,Heap.read_tick,rep.dist,tail,
        cond,cond',show decide (a.d v = -1) = true by simp [unseen],beq] using run
    · let sn : State_bfs := {s with t11 := true,t12 := false,v8 := v,v7 := s.v7+1}
      have same : b = a := by simp [b,add,unseen]
      have sn_tail : sn.v6 = (b.q.length : Int) := by simp [sn,same,tail]
      obtain ⟨sf,s0,s1,s2,s3,s4,s5,s6,run⟩ := ih h' b sn rep'
        (by simpa only [sn] using bh) ba (by simpa [sn] using hg)
        (by simpa [sn] using sr) (by simpa [sn] using sq)
        (by simpa [sn,beq] using su) sn_tail (pre++[v]) row' (by simp [sn,index])
      refine ⟨sf,by simpa [sn] using s0,by simpa [sn] using s1,s2,
        by simpa [sn] using s3,s4,by simpa [sn] using s5,by simpa only [beq,scan] using s6,?_⟩
      apply Reaches.prepend (Step.bfs_pc8 _ _ _ (by simp [hd,hdv]))
      apply Reaches.prepend (Step.bfs_pc7_true _ _ _ cond)
      apply Reaches.prepend (Step.bfs_pc19 _ _ _)
      apply Reaches.prepend (Step.bfs_pc18 _ _ _ (by simpa only [adj_tick,get_tick,ha,su,Option.getD_some,getb,Option.isSome_some,true_and,Heap.tick_nextRef] using rv))
      apply Reaches.prepend (Step.bfs_pc17 _ _ _ (by simp [sr,dv,da]))
      apply Reaches.prepend (Step.bfs_pc16_false _ _ _ (by simp only [adj_tick,get_tick,ha,su,getb,atj,sr,dv,dist_tick,Option.getD_some,Heap.read_tick,rep.dist,unseen]; rfl))
      apply Reaches.prepend (Step.bfs_pc10 _ _ _)
      apply Reaches.prepend (Step.bfs_pc9 _ _ _)
      simpa only [scanHeap,scan,h',b,edgeHeap,if_neg unseen,add,if_neg unseen,sn,sr,sq,su,
        adj_tick,get_tick,ha,getb,atj,dv,dist_tick,Option.getD_some,Heap.read_tick,rep.dist,tail,
        cond,cond',show decide (a.d v = -1) = false by simp [unseen],beq] using run


def mass (g : Graph) (xs : List Int) : Nat := (xs.map fun v => (g.neighbors v.toNat).length).sum

def runHeap (g : Graph) (d p q : Nat) : Nat → Nat → Data → Heap → Heap
  | 0,_,_,h => h
  | fuel+1,head,a,h => if head < a.q.length then
      runHeap g d p q fuel (head+1) (scan a.q[head]! (g.neighbors a.q[head]!.toNat) a)
        ((scanHeap d p q a.q[head]! (g.neighbors a.q[head]!.toNat) a
          ((h.tick "graph_work" 1).tick "graph_work" 1)).tick "graph_work" 1)
    else h

theorem run_rep {before h : Heap} {r d p q : Nat} {a : Data} {g : Graph} {s : Int} {head fuel : Nat}
    (rep : Rep before h r d p q a) (inv : Inv g s head a) (enough : g.size ≤ head + fuel) :
    Rep before (runHeap g d p q fuel head a h) r d p q (run g fuel head a) ∧
      (runHeap g d p q fuel head a h).clocks "graph_work" + a.q.length + 3*head =
        h.clocks "graph_work" + 4*(run g fuel head a).q.length +
          2*mass g ((run g fuel head a).q.drop head) := by
  induction fuel generalizing head a h with
  | zero =>
    have done : head = a.q.length := by have := inv.head_le; have := queue_bound inv; omega
    exact ⟨rep,by simp [runHeap,run,done,mass]; omega⟩
  | succ fuel ih =>
    by_cases active : head < a.q.length
    · have uv := inv.valid _ (get_mem active)
      have edges : ∀ v ∈ g.neighbors a.q[head]!.toNat, Edge g a.q[head]! v := by
        intro v hv
        have vb := g.bounded a.q[head]!.toNat (by rcases uv with ⟨_,_⟩; omega) v hv
        exact ⟨uv,⟨by omega,by omega⟩,by simpa using hv⟩
      obtain ⟨rep',clock'⟩ := scan_rep ((rep.tick 1).tick 1) inv active _ edges
      obtain ⟨inv',ext'⟩ := scan_next inv active
      obtain ⟨rep'',clock''⟩ := ih (rep'.tick 1) inv' (by omega)
      refine ⟨by simpa only [runHeap,run,if_pos active] using rep'',?_⟩
      let b := scan a.q[head]! (g.neighbors a.q[head]!.toNat) a
      let f := run g fuel (head+1) b
      obtain ⟨k,fh,fd,fx⟩ := run_inv inv' (by omega : g.size ≤ head+1+fuel)
      have ex : Ext a f := ext_trans ext' fx
      have fa : head < f.q.length := lt_of_lt_of_le active ex.initial_segment.length_le
      have fm : mass g (f.q.drop head) = (g.neighbors a.q[head]!.toNat).length + mass g (f.q.drop (head+1)) := by
        rw [List.drop_eq_getElem_cons fa]
        change (g.neighbors f.q[head].toNat).length + mass g (f.q.drop (head+1)) = _
        have eq : f.q[head] = a.q[head]! := by rw [← getElem!_pos f.q head fa]; exact ext_get ex active
        rw [eq]
      simp only [runHeap,run,if_pos active]
      change _ + a.q.length + 3*head = h.clocks "graph_work" + 4*f.q.length + 2*mass g (f.q.drop head)
      rw [fm]
      simp only [Heap.clocks_tick_same] at clock' clock''
      change _ + b.q.length + 3*(head+1) = (scanHeap d p q a.q[head]! (g.neighbors a.q[head]!.toNat) a ((h.tick "graph_work" 1).tick "graph_work" 1)).clocks "graph_work" + 1 + 4*f.q.length + 2*mass g (f.q.drop (head+1)) at clock''
      change _ + a.q.length = h.clocks "graph_work" + 1+1 + 2*(g.neighbors a.q[head]!.toNat).length + b.q.length at clock'
      omega
    · have done : head = a.q.length := inv.head_le.antisymm (by omega)
      exact ⟨by simpa [runHeap,run,active] using rep,
        by simp [runHeap,run,active,done,mass]; omega⟩

theorem mass_bound {g : Graph} {s : Int} {head : Nat} {a : Data} (h : Inv g s head a) :
    mass g a.q ≤ edgeCount g := by
  have sub : a.q ⊆ (List.range g.size).map Int.ofNat := by
    intro v hv
    have vv := h.valid v hv
    exact List.mem_map.mpr ⟨v.toNat,List.mem_range.mpr (by rcases vv with ⟨_,_⟩; omega),Int.toNat_of_nonneg vv.1⟩
  have perm := h.nodup.subperm sub
  rcases List.subperm_iff.mp perm with ⟨xs,hperm,hsub⟩
  have le := (hsub.map (fun v : Int => (g.neighbors v.toNat).length)).sum_le_sum (by intros; exact Nat.zero_le _)
  rw [(hperm.map (fun v : Int => (g.neighbors v.toNat).length)).sum_eq] at le
  simpa [mass,edgeCount,List.map_map,Function.comp_def] using le


theorem exit_execution (h : Heap) (s : State_bfs) (stop : s.v5 = s.v6) (stack : Stack) :
    Reaches Step (.active h (Frame.fn_bfs 5 s) stack)
      (.active h (Frame.fn_bfs 3 {s with t10 := false}) stack) := by
  apply Reaches.prepend (Step.bfs_pc5 _ _ _)
  apply Reaches.prepend (Step.bfs_pc4_false _ _ _ (by simp [stop]))
  simpa [stop] using Reaches.refl (step:=Step) (.active h (Frame.fn_bfs 3 {s with t10 := false}) stack)

theorem run_execution (before h : Heap) (g : Graph) (r d p q : Nat) (a : Data)
    (s : State_bfs) (head fuel : Nat) (rep : Rep before h r d p q a)
    (inv : Inv g s.v1 head a) (enough : g.size ≤ head+fuel)
    (hg : GraphRep before s.v0 g) (sr : s.v2 = r) (sq : s.v4 = q)
    (sh : s.v5 = (head : Int)) (st : s.v6 = (a.q.length : Int)) (stack : Stack) :
    ∃ sf : State_bfs, sf.v2 = r ∧
      Reaches Step (.active h (Frame.fn_bfs 5 s) stack)
        (.active (runHeap g d p q fuel head a h) (Frame.fn_bfs 3 sf) stack) := by
  induction fuel generalizing a h head s with
  | zero =>
    have done : head = a.q.length := by have := inv.head_le; have := queue_bound inv; omega
    exact ⟨{s with t10 := false},sr,exit_execution h s (by rw [sh,st,done]) stack⟩
  | succ fuel ih =>
    by_cases active : head < a.q.length
    · let b := scan a.q[head]! (g.neighbors a.q[head]!.toNat) a
      let h2 := (h.tick "graph_work" 1).tick "graph_work" 1
      let h3 := (scanHeap d p q a.q[head]! (g.neighbors a.q[head]!.toNat) a h2).tick "graph_work" 1
      let sn : State_bfs := {s with t10 := true,v3 := a.q[head]!,v5 := s.v5+1,v7 := 0}
      obtain ⟨si,s0,s1,s2,s3,s4,s5,s6,scanRun⟩ := scan_execution before h2 g r d p q a sn head
        ((rep.tick 1).tick 1) (by simpa only [sn] using inv) active
        (by simpa only [sn] using hg) sr sq rfl st _ [] rfl rfl stack
      have uv := inv.valid _ (get_mem active)
      have edges : ∀ v ∈ g.neighbors a.q[head]!.toNat, Edge g a.q[head]! v := by
        intro v hv
        have vb := g.bounded a.q[head]!.toNat (by rcases uv with ⟨_,_⟩; omega) v hv
        exact ⟨uv,⟨by omega,by omega⟩,by simpa using hv⟩
      have rep3 : Rep before h3 r d p q b := ((scan_rep ((rep.tick 1).tick 1) inv active _ edges).1).tick 1
      have inv3 : Inv g si.v1 (head+1) b := by rw [s1]; exact (scan_next inv active).1
      obtain ⟨sf,sf2,rest⟩ := ih h3 b si (head+1) rep3 inv3 (by omega)
        (by rw [s0]; exact hg) s2 s4 (by rw [s5]; simp only [sn,sh]; omega) s6
      refine ⟨sf,sf2,?_⟩
      apply Reaches.prepend (Step.bfs_pc5 _ _ _)
      have cond : decide (s.v5 < s.v6) = true := by simp [sh,st,active]
      apply Reaches.prepend (Step.bfs_pc4_true _ _ _ cond)
      apply Reaches.prepend (Step.bfs_pc24 _ _ _)
      apply Reaches.prepend (Step.bfs_pc23 _ _ _ (by simpa only [sq,Heap.tick_nextRef] using (rep.fresh.2 q (by simp)).2))
      apply Reaches.prepend (Step.bfs_pc22 _ _ _)
      apply Reaches.prepend (Step.bfs_pc21 _ _ _)
      apply Reaches.prepend (Step.bfs_pc20 _ _ _)
      have scanRun' : Reaches Step _ (.active h3 (Frame.fn_bfs 5 si) stack) := scanRun
      apply Reaches.trans ?_ (by simpa only [runHeap,if_pos active] using rest)
      simpa only [h2,sn,cond,Heap.read_tick,sq,sh,st,rep.queued head active,show decide ((head : Int) < (a.q.length : Int)) = true by simp [active]] using scanRun'
    · refine ⟨{s with t10 := false},sr,?_⟩
      have done : head = a.q.length := inv.head_le.antisymm (by omega)
      simpa only [runHeap,if_neg active] using exit_execution h s (by rw [sh,st,done]) stack


def conHeap (h : Heap) : Heap :=
  let h1 := (h.tick "graph_work" 1).allocateObject "bfs.BFSResult"
  let h2 := (h1.tick "graph_work" 1).allocate (fun _ => -1)
  let h3 := set_BFSResult_distance h2 h.nextObject h.nextRef
  let h4 := h3.allocate (fun _ => -1)
  set_BFSResult_parent h4 h.nextObject (h.nextRef+1)

@[simp] theorem con_meta (h : Heap) :
    (conHeap h).nextRef = h.nextRef+2 ∧ (conHeap h).nextObject = h.nextObject+1 ∧
    (conHeap h).nextCollection = h.nextCollection ∧
    (conHeap h).clocks "graph_work" = h.clocks "graph_work"+2 := by
  simp [conHeap,set_BFSResult_distance,set_BFSResult_parent]

theorem con_props (h : Heap) :
    is_BFSResult (conHeap h) h.nextObject ∧
    field_BFSResult_distance (conHeap h) h.nextObject = some h.nextRef ∧
    field_BFSResult_parent (conHeap h) h.nextObject = some (h.nextRef+1) ∧
    (conHeap h).read h.nextRef = (fun _ => -1) ∧
    (conHeap h).read (h.nextRef+1) = (fun _ => -1) ∧
    Preserves h (conHeap h) := by
  have cls : is_BFSResult (conHeap h) h.nextObject := by
    simp [conHeap,is_BFSResult,Heap.objectClass,Heap.allocateObject,set_BFSResult_distance,
      set_BFSResult_parent,Heap.writeField]
  refine ⟨cls,?_,?_,?_,?_,?_⟩
  · unfold field_BFSResult_distance
    rw [if_pos cls]
    simp [conHeap,set_BFSResult_distance,set_BFSResult_parent,
      Heap.readField,Heap.writeField,Heap.allocateObject,ObjectValue.asSeq]
  · unfold field_BFSResult_parent
    rw [if_pos cls]
    simp [conHeap,set_BFSResult_distance,set_BFSResult_parent,
      Heap.readField,Heap.writeField,Heap.allocateObject,ObjectValue.asSeq]
  · funext i; simp [conHeap,set_BFSResult_distance,set_BFSResult_parent,Heap.read,Heap.allocate]
  · funext i; simp [conHeap,set_BFSResult_distance,set_BFSResult_parent,Heap.read,Heap.allocate]
  · constructor
    · intro ref hr; funext i
      simp [conHeap,set_BFSResult_distance,set_BFSResult_parent,Heap.read,Heap.allocate,
        show ref ≠ h.nextRef by omega,show ref ≠ h.nextRef+1 by omega]
    · intro ref hr
      simp [conHeap,set_BFSResult_distance,set_BFSResult_parent,Heap.writeField,Heap.allocateObject,
        show ref ≠ h.nextObject by omega]
    · intros; rfl
    · rw [(con_meta h).1]; omega
    · rw [(con_meta h).2.1]; omega
    · exact le_refl _
    · rw [(con_meta h).2.2.2]; omega
    · intro name hn; simp [conHeap,set_BFSResult_distance,set_BFSResult_parent,Heap.clocks_tick_other,hn]

def initHeap (h : Heap) : Nat → Heap
  | 0 => (conHeap h).tick "graph_work" 1
  | n+1 => ((((initHeap h n).tick "graph_work" 1).write h.nextRef n (-1)).write (h.nextRef+1) n (-1)).tick "graph_work" 1

theorem init_props (h : Heap) (n : Nat) :
    (initHeap h n).nextRef = h.nextRef+2 ∧ (initHeap h n).nextObject = h.nextObject+1 ∧
    (initHeap h n).read h.nextRef = (fun _ => -1) ∧
    (initHeap h n).read (h.nextRef+1) = (fun _ => -1) ∧
    is_BFSResult (initHeap h n) h.nextObject ∧
    field_BFSResult_distance (initHeap h n) h.nextObject = some h.nextRef ∧
    field_BFSResult_parent (initHeap h n) h.nextObject = some (h.nextRef+1) ∧
    Preserves h (initHeap h n) ∧
    (initHeap h n).clocks "graph_work" = h.clocks "graph_work"+3+2*n := by
  induction n with
  | zero =>
    obtain ⟨cl,df,pf,dv,pv,pr⟩ := con_props h
    exact ⟨(con_meta h).1,(con_meta h).2.1,dv,pv,cl,df,pf,
      preserves_trans pr (preserves_tick _ 1),by simp [initHeap,(con_meta h).2.2.2]⟩
  | succ n ih =>
    obtain ⟨nr,no,dv,pv,cl,df,pf,pr,cost⟩ := ih
    refine ⟨by simpa [initHeap] using nr,by simpa [initHeap] using no,?_,?_,cl,df,pf,?_,?_⟩
    · funext i; by_cases eq : i = (n : Int)
      · subst i; simp [initHeap,Heap.read_write_other_ref,show h.nextRef ≠ h.nextRef+1 by omega]
      · simp [initHeap,Heap.read_write_other_ref,Heap.read_write_other_index,eq,dv,
          show h.nextRef ≠ h.nextRef+1 by omega]
    · funext i; by_cases eq : i = (n : Int)
      · subst i; simp [initHeap]
      · simp [initHeap,Heap.read_write_other_ref,Heap.read_write_other_index,eq,pv,
          show h.nextRef+1 ≠ h.nextRef by omega]
    · exact preserves_trans (preserves_write (preserves_write
        (preserves_trans pr (preserves_tick _ 1)) _ (by omega) _ _) _ (by omega) _ _) (preserves_tick _ 1)
    · simp only [initHeap,Heap.clocks_tick_same,Heap.write_clocks,cost]; omega

theorem constructor_execution (h : Heap) (graph : ObjectRef) (source : Int) (stack : Stack) :
    Reaches Step (.active h (Frame.fn_bfs 45 {v0 := graph,v1 := source}) stack)
      (.active (conHeap h) (Frame.fn_bfs 42 {v0 := graph,v1 := source,v2 := h.nextObject,t16 := h.nextObject}) stack) := by
  apply Reaches.prepend (Step.bfs_pc45 _ _ _)
  apply Reaches.prepend (Step.bfs_pc44 _ _ _)
  apply Reaches.prepend (Step.BFSResult_pc6 _ _ _)
  apply Reaches.prepend (Step.BFSResult_pc5 _ _ _)
  apply Reaches.prepend (Step.BFSResult_pc4 _ _ _)
  apply Reaches.prepend (Step.BFSResult_pc3 _ _ _)
  apply Reaches.prepend (Step.BFSResult___init___pc11 _ _ _)
  apply Reaches.prepend (Step.BFSResult___init___pc10 _ _ _)
  apply Reaches.prepend (Step.BFSResult___init___pc9 _ _ _)
  apply Reaches.prepend (Step.BFSResult___init___pc8 _ _ _)
  apply Reaches.prepend (Step.BFSResult___init___pc7 _ _ _ (by
    simp [is_BFSResult,Heap.objectClass,Heap.allocateObject]))
  apply Reaches.prepend (Step.BFSResult___init___pc6 _ _ _)
  apply Reaches.prepend (Step.BFSResult___init___pc5 _ _ _)
  apply Reaches.prepend (Step.BFSResult___init___pc4 _ _ _)
  apply Reaches.prepend (Step.BFSResult___init___pc3 _ _ _ (by
    simp [is_BFSResult,Heap.objectClass,Heap.allocateObject,set_BFSResult_distance,Heap.writeField]))
  apply Reaches.prepend (Step.BFSResult___init___pc2 _ _ _)
  apply Reaches.prepend (Step.BFSResult___init___pc1 _ _ _)
  apply Reaches.prepend (Step.BFSResult_pc2 _ _ _)
  apply Reaches.prepend (Step.BFSResult_pc1 _ _ _ (con_props h).1)
  apply Reaches.prepend (Step.bfs_pc43 _ _ _)
  exact Reaches.refl _

theorem init_execution (h : Heap) (graph : ObjectRef) (source : Int) (g : Graph)
    (hg : GraphRep h graph g) (k : Nat) (hk : k ≤ g.size) (stack : Stack) :
    ∃ st : State_bfs, st.v0 = graph ∧ st.v1 = source ∧ st.v2 = h.nextObject ∧ st.v3 = (k : Int) ∧
      Reaches Step (.active (conHeap h) (Frame.fn_bfs 42 {v0 := graph,v1 := source,v2 := h.nextObject,t16 := h.nextObject}) stack)
        (.active (initHeap h k) (Frame.fn_bfs 35 st) stack) := by
  induction k with
  | zero =>
    refine ⟨{v0 := graph,v1 := source,v2 := h.nextObject,t16 := h.nextObject},rfl,rfl,rfl,rfl,?_⟩
    apply Reaches.prepend (Step.bfs_pc42 _ _ _)
    apply Reaches.prepend (Step.bfs_pc41 _ _ _)
    exact Reaches.refl _
  | succ k ih =>
    obtain ⟨st,s0,s1,s2,s3,run⟩ := ih (by omega)
    obtain ⟨nr,no,dv,pv,cl,df,pf,pr,cost⟩ := init_props h k
    have size := (graph_preserved pr hg).2.1
    have cond : decide (st.v3 < ((field__a2l_import_0_UnweightedGraph_size (initHeap h k) st.v0).getD 0)) = true := by
      simp only [s0,size,Option.getD_some,s3]; simp [show k < g.size by omega]
    refine ⟨{st with t15 := true,v3 := st.v3+1},s0,s1,s2,by simp only [s3]; omega,?_⟩
    apply run.trans
    apply Reaches.prepend (Step.bfs_pc35 _ _ _ (by simp only [s0,size,Option.isSome_some]))
    apply Reaches.prepend (Step.bfs_pc34_true _ _ _ cond)
    apply Reaches.prepend (Step.bfs_pc40 _ _ _)
    apply Reaches.prepend (Step.bfs_pc39 _ _ _ (by simp [s2,df,nr]))
    apply Reaches.prepend (Step.bfs_pc38 _ _ _ (by simp [s2,pf,nr]))
    apply Reaches.prepend (Step.bfs_pc37 _ _ _)
    apply Reaches.prepend (Step.bfs_pc36 _ _ _)
    simpa only [initHeap,s0,size,s2,s3,dist_tick,par_tick,par_write,df,pf,Option.getD_some,show decide ((k : Int) < (g.size : Int)) = true by simp [show k < g.size by omega]] using
      Reaches.refl (step:=Step) (.active (initHeap h (k+1)) (Frame.fn_bfs 35 {st with t15:=true,v3:=st.v3+1}) stack)


@[simp] theorem result_allocate (h : Heap) (r : ObjectRef) (a : Seq) :
    is_BFSResult (h.allocate a) r ↔ is_BFSResult h r := Iff.rfl
@[simp] theorem dist_allocate (h : Heap) (r : ObjectRef) (a : Seq) :
    field_BFSResult_distance (h.allocate a) r = field_BFSResult_distance h r := rfl
@[simp] theorem par_allocate (h : Heap) (r : ObjectRef) (a : Seq) :
    field_BFSResult_parent (h.allocate a) r = field_BFSResult_parent h r := rfl

def readyHeap (h : Heap) (n : Nat) (source : Int) : Heap :=
  (((((initHeap h n).tick "graph_work" 1).allocate (fun _ => -1)).write
    (h.nextRef+2) 0 source).write h.nextRef source 0).tick "graph_work" 1

theorem ready_rep (h : Heap) (n : Nat) (s : Int) :
    Rep h (readyHeap h n s) h.nextObject h.nextRef (h.nextRef+1) (h.nextRef+2) (start s) ∧
    (readyHeap h n s).clocks "graph_work" = h.clocks "graph_work" + 5+2*n := by
  obtain ⟨nr,no,dv,pv,cl,df,pf,pr,cost⟩ := init_props h n
  have prese := preserves_trans pr (preserves_tick _ 1)
  have prese' := preserves_trans prese (preserves_allocate _ (fun _ => -1))
  have pr' := preserves_trans (preserves_write (preserves_write prese' (h.nextRef+2) (by omega) 0 s)
    h.nextRef (by omega) s 0) (preserves_tick _ 1)
  have dq : h.nextRef ≠ h.nextRef+2 := by omega
  have pd : h.nextRef+1 ≠ h.nextRef := by omega
  have pq : h.nextRef+1 ≠ h.nextRef+2 := by omega
  have da : h.nextRef < ((initHeap h n).tick "graph_work" 1).nextRef := by simp only [Heap.tick_nextRef,nr]; omega
  have pa : h.nextRef+1 < ((initHeap h n).tick "graph_work" 1).nextRef := by simp only [Heap.tick_nextRef,nr]; omega
  have hnr : (readyHeap h n s).nextRef = h.nextRef+3 := by simp [readyHeap,nr]
  refine ⟨⟨pr',?_,?_,?_,?_,?_,?_,?_,?_⟩,?_⟩
  · constructor
    · simp [List.pairwise_cons]
    · intro ref mem; simp only [List.mem_cons,List.mem_nil_iff,or_false] at mem
      rw [hnr]
      rcases mem with eq | eq | eq
      · rw [eq]; exact ⟨le_refl _,Nat.lt_add_of_pos_right (by decide)⟩
      · rw [eq]; exact ⟨Nat.le_add_right _ _,Nat.add_lt_add_left (by decide : 1 < 3) _⟩
      · rw [eq]; exact ⟨Nat.le_add_right _ _,Nat.add_lt_add_left (by decide : 2 < 3) _⟩
  · simp [FreshObject,readyHeap,no]
  · simpa [readyHeap] using cl
  · simpa [readyHeap] using df
  · simpa [readyHeap] using pf
  · funext i
    change (readyHeap h n s).read h.nextRef i = Function.update (fun _ => -1) s 0 i
    simp only [readyHeap,Heap.read_tick]
    by_cases eq : i = s
    · subst i; simp
    · rw [Heap.read_write_other_index _ _ _ _ _ eq,
        Heap.read_write_other_ref _ h.nextRef (h.nextRef+2) _ _ _ dq,
        Heap.read_allocate_old _ (fun _ => -1) h.nextRef i da,Heap.read_tick,dv]
      simp [Function.update,eq]
  · funext i
    change (readyHeap h n s).read (h.nextRef+1) i = -1
    simp only [readyHeap,Heap.read_tick]
    rw [Heap.read_write_other_ref _ (h.nextRef+1) h.nextRef _ _ _ pd,
      Heap.read_write_other_ref _ (h.nextRef+1) (h.nextRef+2) _ _ _ pq,
      Heap.read_allocate_old _ (fun _ => -1) (h.nextRef+1) i pa,Heap.read_tick,pv]
  · intro i hi
    have iz : i = 0 := by simp only [start,List.length_singleton] at hi; omega
    subst i
    simp [readyHeap,Heap.read_write_other_ref,show h.nextRef+2 ≠ h.nextRef by omega,start]
  · simp only [readyHeap,Heap.clocks_tick_same,Heap.write_clocks,Heap.allocate_clocks,cost]; omega

theorem ready_execution (h : Heap) (graph : ObjectRef) (source : Int) (g : Graph)
    (hg : GraphRep h graph g) (st : State_bfs)
    (s0 : st.v0 = graph) (s1 : st.v1 = source) (s2 : st.v2 = h.nextObject) (s3 : st.v3 = (g.size : Int))
    (stack : Stack) :
    ∃ sf : State_bfs, sf.v0 = graph ∧ sf.v1 = source ∧ sf.v2 = h.nextObject ∧
      sf.v4 = h.nextRef+2 ∧ sf.v5 = 0 ∧ sf.v6 = 1 ∧
      Reaches Step (.active (initHeap h g.size) (Frame.fn_bfs 35 st) stack)
        (.active (readyHeap h g.size source) (Frame.fn_bfs 5 sf) stack) := by
  obtain ⟨nr,no,dv,pv,cl,df,pf,pr,cost⟩ := init_props h g.size
  have size := (graph_preserved pr hg).2.1
  let sf : State_bfs := {st with t15 := false,t14 := -1,t13 := h.nextRef+2,v4 := h.nextRef+2,v5 := 0,v6 := 1}
  refine ⟨sf,s0,s1,s2,rfl,rfl,rfl,?_⟩
  apply Reaches.prepend (Step.bfs_pc35 _ _ _ (by simp [s0,size]))
  apply Reaches.prepend (Step.bfs_pc34_false _ _ _ (by simp [s0,size,s3]))
  apply Reaches.prepend (Step.bfs_pc33 _ _ _)
  apply Reaches.prepend (Step.bfs_pc32 _ _ _)
  apply Reaches.prepend (Step.bfs_pc31 _ _ _)
  apply Reaches.prepend (Step.bfs_pc30 _ _ _)
  apply Reaches.prepend (Step.bfs_pc29 _ _ _)
  apply Reaches.prepend (Step.bfs_pc28 _ _ _)
  apply Reaches.prepend (Step.bfs_pc27 _ _ _ (by simp))
  apply Reaches.prepend (Step.bfs_pc26 _ _ _ (by simp only [s2,dist_write,dist_allocate,dist_tick,df,Option.isSome_some,Option.getD_some,Heap.write_nextRef,Heap.allocate_nextRef,Heap.tick_nextRef,nr,true_and]; exact Nat.lt_succ_of_le (Nat.le_add_right _ 2)))
  apply Reaches.prepend (Step.bfs_pc25 _ _ _)
  have cond : decide (st.v3 < (field__a2l_import_0_UnweightedGraph_size (initHeap h g.size) st.v0).getD 0) = false := by simp [s0,size,s3]
  simpa only [readyHeap,sf,s2,s1,cond,nr,Heap.tick_nextRef,dist_write,dist_allocate,dist_tick,df,Option.getD_some] using
    Reaches.refl (step:=Step) (.active (readyHeap h g.size source) (Frame.fn_bfs 5 sf) stack)


theorem complete (before : Heap) (graph : ObjectRef) (g : Graph) (source : Int)
    (represented : GraphRep before graph g) (sourceValid : Vertex g source) :
    ∃ after result, Algo.bfs.bfs.Call before (graph,source) after result ∧
      Post before after result g source ∧ work before after ≤ 6*g.size+2*edgeCount g+5 := by
  let a := start source
  let h := readyHeap before g.size source
  let f := run g g.size 0 a
  let hf := runHeap g before.nextRef (before.nextRef+1) (before.nextRef+2) g.size 0 a h
  have inv : Inv g source 0 a := start_inv g source sourceValid
  have rep : Rep before h before.nextObject before.nextRef (before.nextRef+1) (before.nextRef+2) a :=
    (ready_rep before g.size source).1
  obtain ⟨rp,cost⟩ := run_rep (fuel:=g.size) rep inv (by omega)
  obtain ⟨k,fh,fd,fx⟩ := run_inv (fuel:=g.size) inv (by omega)
  have rf : Rep before (hf.tick "graph_work" 1) before.nextObject before.nextRef (before.nextRef+1) (before.nextRef+2) f := rp.tick 1
  refine ⟨hf.tick "graph_work" 1,before.nextObject,?_,?_,?_⟩
  · refine ⟨represented.1,?_⟩
    intro stack
    obtain ⟨st,s0,s1,s2,s3,ini⟩ := init_execution before graph source g represented g.size (le_refl _) stack
    obtain ⟨sn,n0,n1,n2,n4,n5,n6,ready⟩ := ready_execution before graph source g represented st s0 s1 s2 s3 stack
    obtain ⟨sf,sf2,main⟩ := run_execution before h g before.nextObject before.nextRef (before.nextRef+1)
      (before.nextRef+2) a sn 0 g.size rep (by rw [n1]; exact inv) (by omega)
      (by rw [n0]; exact represented) n2 n4 n5 (by simpa only [a,start,List.length_singleton,Int.natCast_one] using n6) stack
    apply (constructor_execution before graph source stack).trans
    apply ini.trans
    apply ready.trans
    apply main.trans
    apply Reaches.prepend (Step.bfs_pc3 _ _ _)
    apply Reaches.prepend (Step.bfs_pc2 _ _ _)
    have final := Reaches.single (Step.bfs_pc1 (hf.tick "graph_work" 1) {sf with t9 := sf.v2} stack
      (by change is_BFSResult (hf.tick "graph_work" 1) sf.v2; rw [sf2]; exact rf.valid))
    simpa only [sf2] using final
  · refine ⟨rf.valid,rf.fresh_result,rf.preserves,before.nextRef,before.nextRef+1,
      rf.dist_field,rf.par_field,?_,?_,?_,?_⟩
    · refine ⟨by simp [List.pairwise_cons],?_⟩
      intro ref mem
      exact rf.fresh.2 ref (by simp only [List.mem_cons,List.mem_singleton] at mem ⊢; tauto)
    · rw [rf.dist]; exact fh.source_d
    · rw [rf.par]; exact fh.source_p
    · simpa only [rf.dist,rf.par] using finished_correct fh fd
  · have vertices := queue_bound fh
    have edges := mass_bound fh
    have hc := (ready_rep before g.size source).2
    change hf.clocks "graph_work" + 1 = h.clocks "graph_work" + 4*f.q.length + 2*mass g f.q at cost
    change hf.clocks "graph_work" + 1 - before.clocks "graph_work" ≤ _
    change f.q.length ≤ g.size at vertices
    change mass g f.q ≤ edgeCount g at edges
    change h.clocks "graph_work" = before.clocks "graph_work"+5+2*g.size at hc
    omega

end BFSProof

theorem solution (before : Heap) (graph : ObjectRef) (g : Graph) (source : Int)
    (represented : GraphRep before graph g) (sourceValid : Vertex g source) :
    ∃ after result,
      Algo.bfs.bfs.Call before (graph, source) after result ∧
      Post before after result g source ∧
      work before after ≤ 6 * g.size + 2 * edgeCount g + 5 :=
  BFSProof.complete before graph g source represented sourceValid
