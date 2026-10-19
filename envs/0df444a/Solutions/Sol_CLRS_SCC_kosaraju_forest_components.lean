-- Prove2me | solution 1 for CLRS.SCC.kosaraju_forest_components
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T03:06:40.123111+00:00
-- url     : https://prove2.me/submissions/a44d3033-897e-491d-a7ba-92c66274eeea

import Definitions.Def_CLRS_DFS_Program
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Count

set_option autoImplicit false
open Algo2LeanGenerated CLRS.GraphTraversal CLRS.DFS

namespace KosarajuProof

lemma walk_start {g : Graph} {n : Nat} {u v : Int} (h : Walk g n u v) : Vertex g u := by
  cases h with
  | zero _ hv => exact hv
  | cons e _ => exact e.1

lemma walk_end {g : Graph} {n : Nat} {u v : Int} (h : Walk g n u v) : Vertex g v := by
  induction h with
  | zero _ hv => exact hv
  | cons _ _ ih => exact ih

lemma reach_refl {g : Graph} {u : Int} (hu : Vertex g u) : Reachable g u u :=
  ⟨0, Walk.zero u hu⟩

lemma reach_trans {g : Graph} {u v w : Int}
    (a : Reachable g u v) (b : Reachable g v w) : Reachable g u w := by
  obtain ⟨n,h⟩ := a
  induction h with
  | zero => exact b
  | cons e _ ih =>
    obtain ⟨k,hk⟩ := ih b
    exact ⟨k+1, Walk.cons e hk⟩

lemma reach_edge {g : Graph} {u v : Int} (e : Edge g u v) : Reachable g u v :=
  ⟨1, Walk.cons e (Walk.zero v e.2.1)⟩

lemma sc_refl {g : Graph} {u : Int} (hu : Vertex g u) : StronglyConnected g u u :=
  ⟨reach_refl hu, reach_refl hu⟩

lemma sc_symm {g : Graph} {u v : Int} (h : StronglyConnected g u v) :
    StronglyConnected g v u := ⟨h.2,h.1⟩

lemma sc_trans {g : Graph} {u v w : Int}
    (a : StronglyConnected g u v) (b : StronglyConnected g v w) :
    StronglyConnected g u w := ⟨reach_trans a.1 b.1, reach_trans b.2 a.2⟩

lemma parent_start {g : Graph} {p : Seq} {u v : Int} (h : ParentPath g p u v) :
    Vertex g u := by
  induction h with
  | refl hv => exact hv
  | step _ _ _ ih => exact ih

lemma parent_end {g : Graph} {p : Seq} {u v : Int} (h : ParentPath g p u v) :
    Vertex g v := by
  cases h with
  | refl hv => exact hv
  | step _ hv _ => exact hv

lemma parent_trans {g : Graph} {p : Seq} {u v w : Int}
    (a : ParentPath g p u v) (b : ParentPath g p v w) : ParentPath g p u w := by
  induction b with
  | refl => exact a
  | step _ hw hp ih => exact ParentPath.step ih hw hp

lemma parent_reach {g : Graph} {q p d f o c : Seq} {k : Nat}
    (forest : Forest g q p d f o c k) {u v : Int} (h : ParentPath g p u v) :
    Reachable g u v := by
  induction h with
  | refl hv => exact reach_refl hv
  | @step v w path hw hp ih =>
    have hv := parent_end path
    have e : Edge g v w := by
      rcases forest.parentEdges w hw with root | edge
      · have := hv.1
        omega
      · simpa only [hp] using edge
    exact reach_trans ih (reach_edge e)

lemma parent_label {g : Graph} {q p d f o c : Seq} {k : Nat}
    (forest : Forest g q p d f o c k) {u v : Int} (h : ParentPath g p u v) : c u = c v := by
  have hu := parent_start h
  have hv := parent_end h
  obtain ⟨r,hr,_⟩ := (forest.componentTrees u u hu hu).mp rfl
  exact (forest.componentTrees u v hu hv).mpr
    ⟨r, hr, hr.1, hr.2.1, parent_trans hr.2.2 h⟩

lemma allowed_path {g : Graph} {a u v : Int} {n : Nat} {allowed : Int → Prop}
    (path : Walk g n u v) (pre : Reachable g a u) (back : Reachable g v a)
    (all : ∀ w, Vertex g w → StronglyConnected g a w → allowed w) :
    AllowedWalk g allowed u v := by
  induction path with
  | zero _ hv => exact AllowedWalk.refl hv (all _ hv ⟨pre,back⟩)
  | @cons n u w v e rest ih =>
    have sc : StronglyConnected g a u :=
      ⟨pre, reach_trans ⟨n+1,Walk.cons e rest⟩ back⟩
    exact AllowedWalk.step e (all _ e.1 sc) (ih (reach_trans pre (reach_edge e)) back)

lemma sc_same_label {g : Graph} {q p d f o c : Seq} {k : Nat}
    (forest : Forest g q p d f o c k) {u v : Int}
    (hu : Vertex g u) (hv : Vertex g v) (sc : StronglyConnected g u v) : c u = c v := by
  classical
  let vertices := (Finset.range g.size).filter (fun i : Nat => StronglyConnected g u (i : Int))
  have mem_u : u.toNat ∈ vertices := by
    have cast : (u.toNat : Int) = u := Int.toNat_of_nonneg hu.1
    simp only [vertices,Finset.mem_filter,Finset.mem_range,cast]
    exact ⟨by rcases hu with ⟨_,_⟩; omega,sc_refl hu⟩
  obtain ⟨a,ha,minimal⟩ := Finset.exists_min_image vertices (fun i => d (i : Int)) ⟨_,mem_u⟩
  obtain ⟨ha_bound,ha_sc⟩ := Finset.mem_filter.mp ha
  have ha_vertex : Vertex g (a : Int) := ⟨by omega,by simpa using Finset.mem_range.mp ha_bound⟩
  have min_d : ∀ w, Vertex g w → StronglyConnected g (a : Int) w → d a ≤ d w := by
    intro w hw hsc
    have cast : (w.toNat : Int) = w := Int.toNat_of_nonneg hw.1
    have hw_mem : w.toNat ∈ vertices := by
      simp only [vertices,Finset.mem_filter,Finset.mem_range,cast]
      exact ⟨by rcases hw with ⟨_,_⟩; omega, sc_trans ha_sc hsc⟩
    simpa only [cast] using minimal _ hw_mem
  have ancestor : ∀ w, Vertex g w → StronglyConnected g (a : Int) w → ParentPath g p a w := by
    intro w hw hsc
    obtain ⟨n,path⟩ := hsc.1
    apply (forest.whitePaths a w ha_vertex hw).mpr
    exact allowed_path path (reach_refl ha_vertex) hsc.2 min_d
  have au := parent_label forest (ancestor u hu (sc_symm ha_sc))
  have av := parent_label forest (ancestor v hv (sc_trans (sc_symm ha_sc) sc))
  exact au.symm.trans av

lemma vertex_transpose {g t : Graph} (tr : IsTranspose g t) (v : Int) :
    Vertex t v ↔ Vertex g v := by simp only [Vertex,tr.1]

lemma edge_transpose {g t : Graph} (tr : IsTranspose g t) {u v : Int} :
    Edge t u v ↔ Edge g v u := by
  have sizes := tr.1
  constructor
  · intro ⟨hu,hv,mem⟩
    have hgu := (vertex_transpose tr u).mp hu
    have hgv := (vertex_transpose tr v).mp hv
    refine ⟨hgv,hgu,?_⟩
    have counts := tr.2 u.toNat v.toNat (by rcases hgu with ⟨_,_⟩; omega)
      (by rcases hgv with ⟨_,_⟩; omega)
    exact List.count_pos_iff.mp (by rw [← counts]; exact List.count_pos_iff.mpr mem)
  · intro ⟨hv,hu,mem⟩
    refine ⟨(vertex_transpose tr u).mpr hu,(vertex_transpose tr v).mpr hv,?_⟩
    have counts := tr.2 u.toNat v.toNat (by rcases hu with ⟨_,_⟩; omega)
      (by rcases hv with ⟨_,_⟩; omega)
    exact List.count_pos_iff.mp (by rw [counts]; exact List.count_pos_iff.mpr mem)

lemma reach_transpose {g t : Graph} (tr : IsTranspose g t) {u v : Int}
    (h : Reachable t u v) : Reachable g v u := by
  obtain ⟨n,path⟩ := h
  induction path with
  | zero _ hv => exact reach_refl ((vertex_transpose tr _).mp hv)
  | cons e _ ih => exact reach_trans ih (reach_edge ((edge_transpose tr).mp e))

lemma transpose_symm {g t : Graph} (tr : IsTranspose g t) : IsTranspose t g := by
  refine ⟨tr.1.symm,?_⟩
  intro u v hu hv
  have sizes := tr.1
  exact (tr.2 v u (by omega) (by omega)).symm

lemma order_covers {g : Graph} {o : Seq} (ho : VertexOrder g o)
    {v : Int} (hv : Vertex g v) : ∃ i : Nat, i < g.size ∧ o i = v := by
  obtain ⟨values,perm,vals⟩ := ho
  have mem : v ∈ values := by
    apply perm.mem_iff.mpr
    apply List.mem_map.mpr
    exact ⟨v.toNat,List.mem_range.mpr (by rcases hv with ⟨_,_⟩; omega),Int.toNat_of_nonneg hv.1⟩
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp mem
  have len : values.length = g.size := by simpa using perm.length_eq
  refine ⟨i,by omega,?_⟩
  rw [vals i (by omega),getElem!_pos values i hi]
  exact eq

/-- An incoming edge to a descendant stays in the ancestor's interval whenever
its source finishes no later than that ancestor. -/
lemma incoming_descendant {g : Graph} {q p d f o c : Seq} {k : Nat}
    (forest : Forest g q p d f o c k) {r v w : Int}
    (rv : ParentPath g p r v) (edge : Edge g w v) (bound : f w ≤ f r) :
    ParentPath g p r w := by
  have hr := parent_start rv
  have hv := parent_end rv
  have hw := edge.1
  have rv_times := (forest.ancestors r v hr hv).mp rv
  have rt := forest.times r hr
  have vt := forest.times v hv
  have wt := forest.times w hw
  by_cases eq : f w = f r
  · have wr := forest.finishDistinct w r hw hr eq
    subst w
    exact ParentPath.refl hr
  have strict : f w < f r := by omega
  rcases forest.parentheses r w hr hw with before | after | nested | outer
  · omega
  · have d_wv : d w ≤ d v := by omega
    have wv : ParentPath g p w v := (forest.whitePaths w v hw hv).mpr
      (AllowedWalk.step edge (le_refl _) (AllowedWalk.refl hv d_wv))
    have := (forest.ancestors w v hw hv).mp wv
    omega
  · exact (forest.ancestors r w hr hw).mpr nested
  · omega

/-- The reverse finish order makes each second-pass root maximal in first-pass
finish time throughout its returned tree. -/
lemma root_max_finish (g t : Graph) (tr : IsTranspose g t)
    (q₁ p₁ d₁ f₁ o₁ c₁ q₂ p₂ d₂ f₂ o₂ c₂ : Seq) (k₁ k₂ : Nat)
    (first : Forest g q₁ p₁ d₁ f₁ o₁ c₁ k₁)
    (second : Forest t q₂ p₂ d₂ f₂ o₂ c₂ k₂)
    (reversed : ∀ i : Nat, i < g.size → q₂ (i : Int) = o₁ ((g.size : Int) - 1 - i))
    {r v : Int} (hr : Vertex t r) (root : p₂ r = -1) (path : ParentPath t p₂ r v) :
    f₁ v ≤ f₁ r := by
  have hv := parent_end path
  have hgr := (vertex_transpose tr r).mp hr
  have hgv := (vertex_transpose tr v).mp hv
  obtain ⟨ir,hir,eqr⟩ := order_covers first.finishOrder hgr
  obtain ⟨iv,hiv,eqv⟩ := order_covers first.finishOrder hgv
  by_contra bad
  have less : f₁ r < f₁ v := by omega
  have indices : ir < iv := by
    by_contra not_lt
    rcases lt_or_eq_of_le (by omega : iv ≤ ir) with lt | eq
    · have inc := first.finishIncreasing iv ir lt hir
      rw [eqr,eqv] at inc
      omega
    · have same : r = v := by rw [← eqr,← eqv,eq]
      rw [same] at less
      omega
  let i := g.size - 1 - ir
  let j := g.size - 1 - iv
  have hi : i < g.size := by dsimp [i]; omega
  have hj : j < g.size := by dsimp [j]; omega
  have ji : j < i := by dsimp [i,j]; omega
  have casti : (g.size : Int) - 1 - (i : Int) = (ir : Int) := by dsimp [i]; omega
  have castj : (g.size : Int) - 1 - (j : Int) = (iv : Int) := by dsimp [j]; omega
  have qr : q₂ (i : Int) = r := by rw [reversed i hi,casti,eqr]
  have qv : q₂ (j : Int) = v := by rw [reversed j hj,castj,eqv]
  have sizes := tr.1
  have priority := second.rootPriority i (by omega) (by simpa only [qr] using root) j ji
  rw [qr,qv] at priority
  have ances := (second.ancestors r v hr hv).mp path
  have times := second.times v hv
  omega

lemma tree_first_ancestor (g t : Graph) (tr : IsTranspose g t)
    (q₁ p₁ d₁ f₁ o₁ c₁ q₂ p₂ d₂ f₂ o₂ c₂ : Seq) (k₁ k₂ : Nat)
    (first : Forest g q₁ p₁ d₁ f₁ o₁ c₁ k₁)
    (second : Forest t q₂ p₂ d₂ f₂ o₂ c₂ k₂)
    (reversed : ∀ i : Nat, i < g.size → q₂ (i : Int) = o₁ ((g.size : Int) - 1 - i))
    {r v : Int} (hr : Vertex t r) (root : p₂ r = -1) (path : ParentPath t p₂ r v) :
    ParentPath g p₁ r v := by
  induction path with
  | refl hv => exact ParentPath.refl ((vertex_transpose tr _).mp hv)
  | @step v w path hw hp ih =>
    have hv := parent_end path
    have edge : Edge t v w := by
      rcases second.parentEdges w hw with eq | edge
      · have := hv.1
        omega
      · simpa only [hp] using edge
    apply incoming_descendant first ih ((edge_transpose tr).mp edge)
    exact root_max_finish g t tr q₁ p₁ d₁ f₁ o₁ c₁ q₂ p₂ d₂ f₂ o₂ c₂ k₁ k₂
      first second reversed hr root (ParentPath.step path hw hp)

end KosarajuProof

open KosarajuProof

theorem solution
    (g t : Graph) (transposed : IsTranspose g t)
    (q₁ p₁ d₁ f₁ o₁ c₁ q₂ p₂ d₂ f₂ o₂ c₂ : Seq) (k₁ k₂ : Nat)
    (first : Forest g q₁ p₁ d₁ f₁ o₁ c₁ k₁)
    (second : Forest t q₂ p₂ d₂ f₂ o₂ c₂ k₂)
    (reversed : ∀ i : Nat, i < g.size → q₂ (i : Int) = o₁ ((g.size : Int) - 1 - i)) :
    ∀ u v : Int, Vertex g u → Vertex g v →
      (c₂ u = c₂ v ↔ StronglyConnected g u v) := by
  intro u v hu hv
  have htu := (vertex_transpose transposed u).mpr hu
  have htv := (vertex_transpose transposed v).mpr hv
  constructor
  · intro same
    obtain ⟨r,ru,rv⟩ := (second.componentTrees u v htu htv).mp same
    have ances : ∀ w, ParentPath t p₂ r w → ParentPath g p₁ r w := by
      intro w path
      exact tree_first_ancestor g t transposed q₁ p₁ d₁ f₁ o₁ c₁
        q₂ p₂ d₂ f₂ o₂ c₂ k₁ k₂ first second reversed ru.1 ru.2.1 path
    have ur := reach_transpose transposed (parent_reach second ru.2.2)
    have vr := reach_transpose transposed (parent_reach second rv.2.2)
    have ru' := parent_reach first (ances u ru.2.2)
    have rv' := parent_reach first (ances v rv.2.2)
    exact ⟨reach_trans ur rv',reach_trans vr ru'⟩
  · intro sc
    apply sc_same_label second htu htv
    exact ⟨reach_transpose (transpose_symm transposed) sc.2,
      reach_transpose (transpose_symm transposed) sc.1⟩

