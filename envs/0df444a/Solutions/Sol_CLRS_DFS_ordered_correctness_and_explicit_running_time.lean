-- Prove2me | solution 1 for CLRS.DFS.ordered_correctness_and_explicit_running_time
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T03:18:09.811484+00:00
-- url     : https://prove2.me/submissions/33bf7ee2-fc84-41e6-a96d-974f4423b814

import Theorems.Thm_CLRS_DFS_ordered_local_certificate

set_option autoImplicit false

open Algo2LeanGenerated CLRS.GraphTraversal CLRS.DFS

namespace DFSLocalReduction

variable {g : Graph} {inputOrder parent discover finish order component : Seq} {count : Nat}
variable (cert : LocalCertificate g inputOrder parent discover finish order component count)
include cert

lemma parent_interval {u v : Int} (path : ParentPath g parent u v) :
    discover u ≤ discover v ∧ finish v ≤ finish u := by
  induction path with
  | refl hu => exact ⟨le_rfl, le_rfl⟩
  | @step v w path hw hp ih =>
    rcases cert.parentCases w hw with root | ⟨edge, hd, hf⟩
    · have hv : Vertex g v := by
        cases path with
        | refl h => exact h
        | step _ h _ => exact h
      rw [hp] at root
      have := hv.1
      omega
    · rw [hp] at hd hf
      exact ⟨ih.1.trans hd.le, hf.le.trans ih.2⟩

lemma interval_parent {u v : Int} (hu : Vertex g u) (hv : Vertex g v)
    (hd : discover u ≤ discover v) (hf : finish v ≤ finish u) : ParentPath g parent u v := by
  generalize hn : (discover v - discover u).toNat = n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases huv : u = v
    · subst v; exact .refl hu
    have hdn : discover u ≠ discover v := fun h => huv (cert.discoveryDistinct u v hu hv h)
    have hfn : finish v ≠ finish u := fun h => huv (cert.finishDistinct v u hv hu h).symm
    have hdl : discover u < discover v := by omega
    have hfl : finish v < finish u := by omega
    obtain ⟨hpv, hpd, hpf⟩ := cert.parentNearest u v hu hv hdl hfl
    rcases cert.parentCases v hv with root | ⟨edge, hpdv, hfpv⟩
    · rw [root] at hpv; have := hpv.1; omega
    · have hsmall : (discover (parent v) - discover u).toNat < n := by omega
      exact .step (ih _ hsmall hpv hpd hpf rfl) hv rfl

lemma ancestors {u v : Int} (hu : Vertex g u) (hv : Vertex g v) :
    ParentPath g parent u v ↔ discover u ≤ discover v ∧ finish v ≤ finish u :=
  ⟨parent_interval cert, fun h => interval_parent cert hu hv h.1 h.2⟩

lemma parent_allowed {u v : Int} (path : ParentPath g parent u v) :
    AllowedWalk g (fun w => discover u ≤ discover w) u v := by
  have append_edge {a b c : Int} {allowed : Int → Prop}
      (path : AllowedWalk g allowed a b) (edge : Edge g b c) (hc : allowed c) :
      AllowedWalk g allowed a c := by
    induction path with
    | refl hv ha => exact .step edge ha (.refl edge.2.1 hc)
    | step e ha p ih => exact .step e ha (ih edge)
  induction path with
  | refl hu => exact .refl hu le_rfl
  | @step v w path hw hp ih =>
    rcases cert.parentCases w hw with root | ⟨edge, hd, hf⟩
    · have hv : Vertex g v := by
        cases path with
        | refl h => exact h
        | step _ h _ => exact h
      rw [hp] at root; have := hv.1; omega
    · rw [hp] at edge
      exact append_edge ih edge (parent_interval cert (.step path hw hp)).1

lemma allowed_interval {u v : Int} (hu : Vertex g u) (_hv : Vertex g v)
    (path : AllowedWalk g (fun w => discover u ≤ discover w) u v) :
    discover u ≤ discover v ∧ finish v ≤ finish u := by
  have closed {a b : Int} (ha : Vertex g a) (hb : Vertex g b)
      (hia : discover u ≤ discover a ∧ finish a ≤ finish u)
      (e : Edge g a b) (hwhite : discover u ≤ discover b) :
      discover u ≤ discover b ∧ finish b ≤ finish u := by
    have scan := cert.edgeScanned a b e
    have tb := cert.times b hb
    rcases cert.parentheses u b hu hb with h | h | h | h
    · omega
    · omega
    · exact h
    · have eq : u = b := cert.discoveryDistinct u b hu hb (by omega)
      subst b; exact ⟨le_rfl, le_rfl⟩
  have go {a b : Int} (p : AllowedWalk g (fun w => discover u ≤ discover w) a b) :
      (discover u ≤ discover a ∧ finish a ≤ finish u) →
      discover u ≤ discover b ∧ finish b ≤ finish u := by
    induction p with
    | refl ha hw => exact id
    | @step a b c e hw p ih =>
      intro ha
      have hb : Vertex g b ∧ discover u ≤ discover b := by
        cases p with
        | refl h w => exact ⟨h,w⟩
        | step edge w _ => exact ⟨edge.1,w⟩
      exact ih (closed e.1 hb.1 ha e hb.2)
  exact go path ⟨le_rfl, le_rfl⟩

lemma white_paths {u v : Int} (hu : Vertex g u) (hv : Vertex g v) :
    ParentPath g parent u v ↔ AllowedWalk g (fun w => discover u ≤ discover w) u v := by
  exact ⟨parent_allowed cert, fun h => (ancestors cert hu hv).mpr (allowed_interval cert hu hv h)⟩

lemma parent_component {u v : Int} (path : ParentPath g parent u v) : component u = component v := by
  induction path with
  | refl _ => rfl
  | @step v w path hw hp ih =>
    have hv : Vertex g v := by
      cases path with
      | refl h => exact h
      | step _ h _ => exact h
    have hne : parent w ≠ -1 := by rw [hp]; have := hv.1; omega
    exact ih.trans (by simpa [hp] using cert.parentLabel w hw hne)

lemma exists_root {v : Int} (hv : Vertex g v) :
    ∃ r : Int, RootOf g parent r v := by
  generalize hn : (discover v).toNat = n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    rcases cert.parentCases v hv with root | ⟨edge, hd, hf⟩
    · exact ⟨v,hv,root,.refl hv⟩
    · have tp := cert.times (parent v) edge.1
      have small : (discover (parent v)).toNat < n := by omega
      obtain ⟨r,hr,hroot,hpath⟩ := ih _ small edge.1 rfl
      exact ⟨r,hr,hroot,.step hpath hv rfl⟩

lemma root_unique {r s : Int} (hr : Vertex g r) (hs : Vertex g s)
    (hpr : parent r = -1) (hps : parent s = -1)
    (hcomp : component r = component s) : r = s := by
  have hrs := cert.componentOrder r s hr hs hpr hps
  have hsr := cert.componentOrder s r hs hr hps hpr
  have hnrs : ¬ discover r < discover s := fun h => by
    have := hrs.mpr h; omega
  have hnsr : ¬ discover s < discover r := fun h => by
    have := hsr.mpr h; omega
  exact cert.discoveryDistinct r s hr hs (by omega)

lemma component_trees {u v : Int} (hu : Vertex g u) (hv : Vertex g v) :
    component u = component v ↔
      ∃ root : Int, RootOf g parent root u ∧ RootOf g parent root v := by
  constructor
  · intro hc
    obtain ⟨r,hr,hpr,hru⟩ := exists_root cert hu
    obtain ⟨s,hs,hps,hsv⟩ := exists_root cert hv
    have hrs : component r = component s :=
      (parent_component cert hru).trans (hc.trans (parent_component cert hsv).symm)
    have eq := root_unique cert hr hs hpr hps hrs
    subst s
    exact ⟨r,⟨hr,hpr,hru⟩,⟨hr,hpr,hsv⟩⟩
  · rintro ⟨r,⟨hr,hpr,hru⟩,⟨_,_,hrv⟩⟩
    exact (parent_component cert hru).symm.trans (parent_component cert hrv)

lemma forest : Forest g inputOrder parent discover finish order component count := by
  refine {
    parentEdges := ?_
    times := cert.times
    discoveryDistinct := cert.discoveryDistinct
    finishDistinct := cert.finishDistinct
    eventDistinct := cert.eventDistinct
    parentheses := cert.parentheses
    ancestors := fun _ _ hu hv => ancestors cert hu hv
    whitePaths := fun _ _ hu hv => white_paths cert hu hv
    rootPriority := cert.rootPriority
    finishOrder := cert.finishOrder
    finishIncreasing := cert.finishIncreasing
    componentRange := cert.componentRange
    componentCoverage := cert.componentCoverage
    componentTrees := fun _ _ hu hv => component_trees cert hu hv
    componentOrder := cert.componentOrder }
  intro v hv
  exact (cert.parentCases v hv).imp_right (fun h => h.1)

omit cert in
lemma post {before after : Heap} {result : ObjectRef} {q : Seq}
    (h : LocalPost before after result g q) : Post before after result g q := by
  rcases h with ⟨valid,fresh,preserve,c,p,d,f,o,b,hc,hp,hd,hf,ho,hb,ha,ht,hn,black,
    count,hcount,bound,hlocal⟩
  exact ⟨valid,fresh,preserve,c,p,d,f,o,b,hc,hp,hd,hf,ho,hb,ha,ht,hn,black,
    count,hcount,bound,forest hlocal⟩

end DFSLocalReduction

theorem solution
    (before : Heap) (graph : ObjectRef) (g : Graph) (inputOrder : SeqRef)
    (represented : GraphRep before graph g)
    (orderAllocated : inputOrder < before.nextRef)
    (orderValid : VertexOrder g (before.read inputOrder)) :
    ∃ (after : Heap) (result : ObjectRef),
      Algo.dfs.dfs_ordered.Call before (graph, inputOrder) after result ∧
      Post before after result g (before.read inputOrder) ∧
      work before after ≤ 4 + 6 * g.size + 2 * edgeCount g := by
  obtain ⟨after,result,call,hlocal,cost⟩ :=
    CLRS.DFS.ordered_local_certificate before graph g inputOrder represented orderAllocated orderValid
  exact ⟨after,result,call,DFSLocalReduction.post hlocal,cost⟩
