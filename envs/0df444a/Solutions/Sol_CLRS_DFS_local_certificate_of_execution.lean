-- Prove2me | solution 1 for CLRS.DFS.local_certificate_of_execution
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:21:32.80399+00:00
-- url     : https://prove2.me/submissions/263147f7-6eed-4a90-a855-6f2f9a21be54

import Definitions.Def_CLRS_DFS_PureExecution
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Range
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 1500000
open Algo2LeanGenerated CLRS.GraphTraversal CLRS.DFS CLRS.DFS.Pure

namespace DFSMetadata

@[simp] lemma write_arrays (s : Pure.State) (a i : Fin 6) (u v x : Int) :
    (write s a u v).arrays i x = if i = a then if x = u then v else s.arrays i x
      else s.arrays i x := by
  by_cases h : i = a <;> by_cases hx : x = u <;> simp [write, h, hx]
@[simp] lemma enter_arrays (s : Pure.State) (u l : Int) (i : Fin 6) (v : Int) :
    (enter s u l).arrays i v =
      if i = 0 then if v = u then 1 else s.arrays i v
      else if i = 2 then if v = u then s.clock+1 else s.arrays i v
      else if i = 5 then if v = u then l else s.arrays i v
      else s.arrays i v := by
  fin_cases i <;> simp [enter]
@[simp] lemma leave_arrays (s : Pure.State) (u : Int) (i : Fin 6) (v : Int) :
    (leave s u).arrays i v =
      if i = 0 then if v = u then 2 else s.arrays i v
      else if i = 3 then if v = u then s.clock+1 else s.arrays i v
      else if i = 4 then if v = s.finished then u else s.arrays i v
      else s.arrays i v := by
  fin_cases i <;> simp [leave, write, Function.update_apply]
@[simp] lemma write_clock (s : Pure.State) (i : Fin 6) (u v : Int) :
    (write s i u v).clock = s.clock := rfl
@[simp] lemma write_finished (s : Pure.State) (i : Fin 6) (u v : Int) :
    (write s i u v).finished = s.finished := rfl
@[simp] lemma write_count (s : Pure.State) (i : Fin 6) (u v : Int) :
    (write s i u v).count = s.count := rfl
@[simp] lemma enter_count (s : Pure.State) (u l : Int) : (enter s u l).count = s.count := rfl
@[simp] lemma leave_count (s : Pure.State) (u : Int) : (leave s u).count = s.count := rfl
@[simp] lemma enter_clock (s : Pure.State) (u l : Int) : (enter s u l).clock = s.clock+1 := rfl
@[simp] lemma enter_finished (s : Pure.State) (u l : Int) : (enter s u l).finished = s.finished := rfl
@[simp] lemma leave_clock (s : Pure.State) (u : Int) : (leave s u).clock = s.clock+1 := rfl
@[simp] lemma leave_finished (s : Pure.State) (u : Int) : (leave s u).finished = s.finished+1 := rfl

structure Inv (g : Graph) (D F : Finset Int) (s : Pure.State) : Prop where
  valid : ∀ v ∈ D, Vertex g v
  sub : F ⊆ D
  color : ∀ v : Int, s.arrays 0 v = if v ∈ F then 2 else if v ∈ D then 1 else 0
  clock : s.clock = (D.card : Int) + F.card
  finished : s.finished = (F.card : Int)
  discovery : ∀ v ∈ D, 1 ≤ s.arrays 2 v ∧ s.arrays 2 v ≤ s.clock
  finish : ∀ v ∈ F, s.arrays 2 v < s.arrays 3 v ∧ s.arrays 3 v ≤ s.clock
  discoveryDistinct : ∀ u ∈ D, ∀ v ∈ D, s.arrays 2 u = s.arrays 2 v → u = v
  finishDistinct : ∀ u ∈ F, ∀ v ∈ F, s.arrays 3 u = s.arrays 3 v → u = v
  eventDistinct : ∀ u ∈ D, ∀ v ∈ F, s.arrays 2 u ≠ s.arrays 3 v
  orderMem : ∀ i : Nat, i < F.card → s.arrays 4 i ∈ F
  orderSurj : ∀ v ∈ F, ∃ i : Nat, i < F.card ∧ s.arrays 4 i = v
  orderIncreasing : ∀ i j : Nat, i < j → j < F.card →
    s.arrays 3 (s.arrays 4 i) < s.arrays 3 (s.arrays 4 j)

lemma white_iff {g : Graph} {D F : Finset Int} {s : Pure.State} (h : Inv g D F s) (v : Int) :
    s.arrays 0 v = 0 ↔ v ∉ D := by
  have sub : ∀ v ∈ F, v ∈ D := fun v hv => h.sub hv
  rw [h.color]; by_cases hf : v ∈ F <;> by_cases hd : v ∈ D <;> simp_all
lemma gray_iff {g : Graph} {D F : Finset Int} {s : Pure.State} (h : Inv g D F s) (v : Int) :
    s.arrays 0 v = 1 ↔ v ∈ D ∧ v ∉ F := by
  have sub : ∀ v ∈ F, v ∈ D := fun v hv => h.sub hv
  rw [h.color]; by_cases hf : v ∈ F <;> by_cases hd : v ∈ D <;> simp_all
lemma black_iff {g : Graph} {D F : Finset Int} {s : Pure.State} (h : Inv g D F s) (v : Int) :
    s.arrays 0 v = 2 ↔ v ∈ F := by
  have sub : ∀ v ∈ F, v ∈ D := fun v hv => h.sub hv
  rw [h.color]; by_cases hf : v ∈ F <;> by_cases hd : v ∈ D <;> simp_all

lemma inv_parent {g : Graph} {D F : Finset Int} {s : Pure.State} (h : Inv g D F s) (u v : Int) :
    Inv g D F (write s 1 u v) := by
  rcases h with ⟨hv,hs,hc,hk,hf,hd,ht,hdd,hff,hdf,hom,hos,hoi⟩
  exact ⟨hv,hs,by simpa using hc,hk,hf,by simpa using hd,by simpa using ht,
    by simpa using hdd,by simpa using hff,by simpa using hdf,
    by simpa using hom,by simpa using hos,by simpa using hoi⟩

lemma inv_nextTree {g : Graph} {D F : Finset Int} {s : Pure.State} (h : Inv g D F s) :
    Inv g D F (nextTree s) := by
  rcases h with ⟨hv,hs,hc,hk,hf,hd,ht,hdd,hff,hdf,hom,hos,hoi⟩
  exact ⟨hv,hs,hc,hk,hf,hd,ht,hdd,hff,hdf,hom,hos,hoi⟩

lemma inv_enter {g : Graph} {D F : Finset Int} {s : Pure.State} (h : Inv g D F s)
    (u l : Int) (hu : Vertex g u) (white : s.arrays 0 u = 0) :
    Inv g (insert u D) F (enter s u l) := by
  have nd : u ∉ D := (white_iff h u).mp white
  have nf : u ∉ F := fun hf => nd (h.sub hf)
  have card : (insert u D).card = D.card+1 := Finset.card_insert_of_notMem nd
  refine ⟨?_,?_,?_,?_,h.finished,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro v hv; rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hu
    · exact h.valid v hv
  · exact Finset.Subset.trans h.sub (Finset.subset_insert _ _)
  · intro v; by_cases he : v = u
    · simp [he,nf]
    · simpa [he] using h.color v
  · simp only [enter_clock, card, Nat.cast_add, Nat.cast_one]; rw [h.clock]; omega
  · intro v hv; rcases Finset.mem_insert.mp hv with rfl | hv
    · have hc : 0 ≤ s.clock := by rw [h.clock]; omega
      simp only [enter_arrays, Fin.reduceEq, reduceIte, enter_clock]; omega
    · have ne : v ≠ u := fun he => nd (he ▸ hv)
      simpa [ne] using And.intro (h.discovery v hv).1 (by have := (h.discovery v hv).2; omega : s.arrays 2 v ≤ s.clock+1)
  · intro v hv
    have ne : v ≠ u := fun he => nf (he ▸ hv)
    have hf := h.finish v hv
    simpa [ne] using And.intro hf.1 (by omega : s.arrays 3 v ≤ s.clock+1)
  · intro v hv w hw eq
    by_cases ve : v = u <;> by_cases we : w = u
    · exact ve.trans we.symm
    · have wd : w ∈ D := by simpa [we] using hw
      have := (h.discovery w wd).2
      simp only [enter_arrays, Fin.reduceEq, reduceIte, ve, if_pos rfl, if_neg we] at eq
      omega
    · have vd : v ∈ D := by simpa [ve] using hv
      have := (h.discovery v vd).2
      simp only [enter_arrays, Fin.reduceEq, reduceIte, we, if_pos rfl, if_neg ve] at eq
      omega
    · apply h.discoveryDistinct v (by simpa [ve] using hv) w (by simpa [we] using hw)
      simpa [ve,we] using eq
  · simpa using h.finishDistinct
  · intro v hv w hw
    by_cases ve : v = u
    · have := (h.finish w hw).2
      simp [ve]; omega
    · have vd : v ∈ D := by simpa [ve] using hv
      simpa [ve] using h.eventDistinct v vd w hw
  · simpa using h.orderMem
  · simpa using h.orderSurj
  · simpa using h.orderIncreasing

lemma inv_leave {g : Graph} {D F : Finset Int} {s : Pure.State} (h : Inv g D F s)
    (u : Int) (gray : s.arrays 0 u = 1) :
    Inv g D (insert u F) (leave s u) := by
  obtain ⟨ud,uf⟩ := (gray_iff h u).mp gray
  have card : (insert u F).card = F.card+1 := Finset.card_insert_of_notMem uf
  have old (v : Int) (hv : v ∈ F) : v ≠ u := fun he => uf (he ▸ hv)
  have orderOld (i : Nat) (hi : i < F.card) : (i : Int) ≠ s.finished := by rw [h.finished]; omega
  have orderNew : (leave s u).arrays 4 (F.card : Int) = u := by simp [h.finished]
  refine ⟨h.valid,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro v hv; rcases Finset.mem_insert.mp hv with rfl | hv
    · exact ud
    · exact h.sub hv
  · intro v; by_cases he : v = u
    · simp [he]
    · simpa [he] using h.color v
  · simp only [leave_clock, card, Nat.cast_add, Nat.cast_one]; rw [h.clock]; omega
  · simp [card,h.finished]
  · intro v hv
    simpa using And.intro (h.discovery v hv).1 (by have := (h.discovery v hv).2; omega : s.arrays 2 v ≤ s.clock+1)
  · intro v hv; rcases Finset.mem_insert.mp hv with rfl | hv
    · have := (h.discovery _ ud).2; simp; omega
    · have hf := h.finish v hv
      simpa [old v hv] using And.intro hf.1 (by omega : s.arrays 3 v ≤ s.clock+1)
  · simpa using h.discoveryDistinct
  · intro v hv w hw eq
    by_cases ve : v = u <;> by_cases we : w = u
    · exact ve.trans we.symm
    · have wf : w ∈ F := by simpa [we] using hw
      have := (h.finish w wf).2
      simp only [leave_arrays, Fin.reduceEq, reduceIte, ve, if_pos rfl, if_neg we] at eq
      omega
    · have vf : v ∈ F := by simpa [ve] using hv
      have := (h.finish v vf).2
      simp only [leave_arrays, Fin.reduceEq, reduceIte, we, if_pos rfl, if_neg ve] at eq
      omega
    · apply h.finishDistinct v (by simpa [ve] using hv) w (by simpa [we] using hw)
      simpa [ve,we] using eq
  · intro v hv w hw
    by_cases we : w = u
    · have := (h.discovery v hv).2; simp [we]; omega
    · have wf : w ∈ F := by simpa [we] using hw
      simpa [we] using h.eventDistinct v hv w wf
  · intro i hi
    rw [card] at hi
    by_cases he : i = F.card
    · rw [he,orderNew]; simp
    · have lt : i < F.card := by omega
      simpa [orderOld i lt] using Finset.mem_insert_of_mem (h.orderMem i lt)
  · intro v hv; rcases Finset.mem_insert.mp hv with rfl | hv
    · exact ⟨F.card,by omega,orderNew⟩
    · obtain ⟨i,hi,he⟩ := h.orderSurj v hv
      exact ⟨i,by omega,by simpa [orderOld i hi] using he⟩
  · intro i j hij hj
    rw [card] at hj
    have hi : i < F.card := by omega
    by_cases he : j = F.card
    · have oi := h.orderMem i hi
      have := (h.finish _ oi).2
      rw [he, orderNew]; simp only [leave_arrays, Fin.reduceEq, reduceIte, if_pos rfl, if_neg (orderOld i hi), if_neg (old _ oi)]; omega
    · have jl : j < F.card := by omega
      have oi := h.orderMem i hi; have oj := h.orderMem j jl
      simpa [orderOld i hi,orderOld j jl,old _ oi,old _ oj] using h.orderIncreasing i j hij jl

-- Each complete visit leaves every vertex that was already discovered unchanged.
def Stable (D : Finset Int) (a b : Pure.State) : Prop :=
  ∀ v ∈ D, ∀ i : Fin 6, i = 0 ∨ i = 2 ∨ i = 3 → b.arrays i v = a.arrays i v

lemma stable_refl (D : Finset Int) (a : Pure.State) : Stable D a a := by intro v hv i hi; rfl
lemma stable_trans {D E : Finset Int} {a b c : Pure.State}
    (sub : D ⊆ E) (ab : Stable D a b) (bc : Stable E b c) : Stable D a c := by
  intro v hv i hi; exact (bc v (sub hv) i hi).trans (ab v hv i hi)

-- A task's only additional precondition is that a newly entered vertex is white.
def Ready (task : Pure.Task) (s : Pure.State) : Prop :=
  match task with
  | .visit u _ => s.arrays 0 u = 0
  | _ => True

theorem metadata {g : Graph} {task : Pure.Task} {a b : Pure.State} {k : Nat}
    (run : Eval g task a b k) :
    ∀ D F, Inv g D F a → Ready task a →
      ∃ E H, Inv g E H b ∧ D ⊆ E ∧ Stable D a b := by
  induction run with
  | @visit u l a b k hu run ih =>
    intro D F inv white
    have entered := inv_enter inv u l hu white
    obtain ⟨E,H,out,sub,stable⟩ := ih _ _ entered trivial
    have gray : b.arrays 0 u = 1 := by
      rw [stable u (by simp) 0 (by simp)]; simp
    refine ⟨E,insert u H,inv_leave out u gray,?_,?_⟩
    · exact Finset.Subset.trans (Finset.subset_insert _ _) sub
    · intro v hv i hi
      have ne : v ≠ u := fun he => (white_iff inv u).mp white (he ▸ hv)
      have eq := stable v (Finset.mem_insert_of_mem hv) i hi
      rcases hi with rfl | rfl | rfl <;> simpa [ne] using eq
  | scan_nil =>
    intro D F inv _; exact ⟨D,F,inv,Finset.Subset.refl _,stable_refl _ _⟩
  | scan_seen _ _ ih => exact ih
  | @scan_fresh u l vs a b c j k v white call rest ihcall ihrest =>
    intro D F inv _
    obtain ⟨E,H,middle,sub,stable⟩ := ihcall D F (inv_parent inv v u) (by simpa [Ready] using white)
    obtain ⟨I,J,out,sub',stable'⟩ := ihrest E H middle trivial
    refine ⟨I,J,out,Finset.Subset.trans sub sub',?_⟩
    have stable0 : Stable D a b := by
      intro w hw i hi
      have eq := stable w hw i hi
      rcases hi with rfl | rfl | rfl <;> simpa using eq
    exact stable_trans sub stable0 stable'
  | roots_nil =>
    intro D F inv _; exact ⟨D,F,inv,Finset.Subset.refl _,stable_refl _ _⟩
  | roots_seen _ _ ih => exact ih
  | @roots_fresh u us a b c j k white call rest ihcall ihrest =>
    intro D F inv _
    obtain ⟨E,H,middle,sub,stable⟩ := ihcall D F inv white
    obtain ⟨I,J,out,sub',stable'⟩ := ihrest E H (inv_nextTree middle) trivial
    refine ⟨I,J,out,Finset.Subset.trans sub sub',?_⟩
    exact stable_trans sub stable stable'

lemma inv_initial (g : Graph) : Inv g ∅ ∅ initial := by
  constructor <;> simp [initial]


def Progress (a b : Pure.State) : Prop :=
  ∀ v : Int, b.arrays 0 v = a.arrays 0 v ∨ (a.arrays 0 v = 0 ∧ b.arrays 0 v = 2)
lemma progress_refl (s : Pure.State) : Progress s s := fun _ => Or.inl rfl
lemma progress_trans {a b c : Pure.State} (ab : Progress a b) (bc : Progress b c) : Progress a c := by
  intro v
  rcases bc v with hc | ⟨hb,hc⟩
  · rcases ab v with h | h
    · exact Or.inl (hc.trans h)
    · exact Or.inr ⟨h.1,hc.trans h.2⟩
  · rcases ab v with h | h
    · exact Or.inr ⟨h.symm.trans hb,hc⟩
    · omega
lemma progress_nonwhite {a b : Pure.State} (h : Progress a b) {v : Int}
    (hv : a.arrays 0 v ≠ 0) : b.arrays 0 v = a.arrays 0 v := by
  rcases h v with he | he
  · exact he
  · exact (hv he.1).elim

def Covered (task : Pure.Task) (s : Pure.State) : Prop :=
  match task with
  | .visit u _ => s.arrays 0 u = 2
  | .scan _ _ vs => ∀ v ∈ vs, s.arrays 0 (v : Int) ≠ 0
  | .roots vs => ∀ v ∈ vs, s.arrays 0 v ≠ 0

lemma progress_covered {g : Graph} {task : Pure.Task} {a b : Pure.State} {k : Nat}
    (run : Eval g task a b k) : Ready task a → Progress a b ∧ Covered task b := by
  induction run with
  | @visit u l a b k hu run ih =>
    intro white
    obtain ⟨pr,covered⟩ := ih trivial
    have gray : b.arrays 0 u = 1 := by
      have := progress_nonwhite pr (v := u) (by simp)
      simpa using this
    refine ⟨?_,by simp [Covered]⟩
    intro v; by_cases ne : v = u
    · exact Or.inr ⟨by simpa [Ready,ne] using white,by simp [ne]⟩
    · simpa [ne] using pr v
  | scan_nil => exact fun _ => ⟨progress_refl _,by simp [Covered]⟩
  | @scan_seen u l vs a b k v seen run ih =>
    intro _; obtain ⟨pr,cov⟩ := ih trivial
    refine ⟨pr,?_⟩
    intro w hw; rcases List.mem_cons.mp hw with rfl | hw
    · rw [progress_nonwhite pr seen]; exact seen
    · exact cov w hw
  | @scan_fresh u l vs a b c j k v white call rest ihcall ihrest =>
    intro _
    obtain ⟨ab,black⟩ := ihcall (by simpa [Ready] using white)
    obtain ⟨bc,cov⟩ := ihrest trivial
    have ab' : Progress a b := by intro w; simpa using ab w
    refine ⟨progress_trans ab' bc,?_⟩
    intro w hw; rcases List.mem_cons.mp hw with rfl | hw
    · have black' : b.arrays 0 (w : Int) = 2 := black
      rw [progress_nonwhite bc (by omega : b.arrays 0 (w : Int) ≠ 0),black']; omega
    · exact cov w hw
  | roots_nil => exact fun _ => ⟨progress_refl _,by simp [Covered]⟩
  | @roots_seen u us a b k seen run ih =>
    intro _; obtain ⟨pr,cov⟩ := ih trivial
    refine ⟨pr,?_⟩
    intro w hw; rcases List.mem_cons.mp hw with rfl | hw
    · rw [progress_nonwhite pr seen]; exact seen
    · exact cov w hw
  | @roots_fresh u us a b c j k white call rest ihcall ihrest =>
    intro _
    obtain ⟨ab,black⟩ := ihcall white
    obtain ⟨bc,cov⟩ := ihrest trivial
    refine ⟨progress_trans ab bc,?_⟩
    intro w hw; rcases List.mem_cons.mp hw with rfl | hw
    · have black' : b.arrays 0 w = 2 := black
      change Progress b c at bc
      rw [progress_nonwhite bc (by omega : b.arrays 0 w ≠ 0),black']; omega
    · exact cov w hw

noncomputable def vertices (g : Graph) : Finset Int := (Finset.range g.size).image Int.ofNat
@[simp] lemma mem_vertices (g : Graph) (v : Int) : v ∈ vertices g ↔ Vertex g v := by
  simp only [vertices, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n,hn,rfl⟩
    change 0 ≤ (n : Int) ∧ (n : Int) < (g.size : Int)
    exact ⟨by omega,by omega⟩
  · intro hv
    exact ⟨v.toNat,by have := hv.1; have := hv.2; omega,Int.toNat_of_nonneg hv.1⟩
@[simp] lemma vertices_card (g : Graph) : (vertices g).card = g.size := by
  rw [vertices, Finset.card_image_of_injective _ (by intro x y h; exact Int.ofNat_inj.mp h),Finset.card_range]

lemma final_metadata (g : Graph) (values : List Int)
    (permutation : values.Perm ((List.range g.size).map Int.ofNat))
    (a : Pure.State) (k : Nat) (execution : Eval g (.roots values) initial a k) :
    Inv g (vertices g) (vertices g) a := by
  obtain ⟨D,F,inv,_,_⟩ := metadata execution ∅ ∅ (inv_initial g) trivial
  obtain ⟨progress,covered⟩ := progress_covered execution trivial
  have allblack (v : Int) (hv : Vertex g v) : a.arrays 0 v = 2 := by
    have vm : v ∈ values := by
      apply permutation.mem_iff.mpr
      exact List.mem_map.mpr ⟨v.toNat,by simp only [List.mem_range]; have := hv.1; have := hv.2; omega,
        Int.toNat_of_nonneg hv.1⟩
    have nonwhite := covered v vm
    rcases progress v with he | ⟨_,he⟩
    · have z : a.arrays 0 v = 0 := by simpa [initial] using he
      exact (nonwhite z).elim
    · exact he
  have F_eq : F = vertices g := by
    ext v; constructor
    · intro hv; exact (mem_vertices g v).mpr (inv.valid v (inv.sub hv))
    · intro hv; exact (black_iff inv v).mp (allblack v ((mem_vertices g v).mp hv))
  have D_eq : D = vertices g := by
    apply Finset.Subset.antisymm
    · intro v hv; exact (mem_vertices g v).mpr (inv.valid v hv)
    · rw [← F_eq]; exact inv.sub
  simpa [D_eq,F_eq] using inv

lemma final_order {g : Graph} {a : Pure.State}
    (inv : Inv g (vertices g) (vertices g) a) : VertexOrder g (a.arrays 4) := by
  let vs := (List.range g.size).map (fun i : Nat => a.arrays 4 (i : Int))
  have inj : ∀ i < g.size, ∀ j < g.size, a.arrays 4 (i : Int) = a.arrays 4 (j : Int) → i = j := by
    intro i hi j hj eq
    by_contra ne
    rcases lt_or_gt_of_ne ne with lt | gt
    · have := inv.orderIncreasing i j lt (by simpa using hj); rw [eq] at this; omega
    · have := inv.orderIncreasing j i gt (by simpa using hi); rw [eq] at this; omega
  have nd : vs.Nodup := (List.nodup_range (n := g.size)).map_on (by
    intro i hi j hj eq
    exact inj i (List.mem_range.mp hi) j (List.mem_range.mp hj) eq)
  have nr : ((List.range g.size).map Int.ofNat).Nodup :=
    (List.nodup_range (n := g.size)).map (by intro x y h; exact Int.ofNat_inj.mp h)
  refine ⟨vs,(List.perm_ext_iff_of_nodup nd nr).mpr ?_,?_⟩
  · intro v
    have vv : v ∈ (List.range g.size).map Int.ofNat ↔ Vertex g v := by
      rw [← mem_vertices]
      change v ∈ (List.range g.size).map Int.ofNat ↔ v ∈ vertices g
      simp [vertices]
    rw [vv]
    constructor
    · intro hv
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hv
      exact (mem_vertices g _).mp (inv.orderMem i (by simpa using List.mem_range.mp hi))
    · intro hv
      obtain ⟨i,hi,he⟩ := inv.orderSurj v ((mem_vertices g v).mpr hv)
      exact List.mem_map.mpr ⟨i,List.mem_range.mpr (by simpa using hi),he⟩
  · intro j hj
    simp [vs,List.getElem!_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hj]


def Preserve (a b : Pure.State) : Prop :=
  ∀ v : Int, a.arrays 0 v ≠ 0 ∨ b.arrays 0 v = 0 →
    ∀ i : Fin 6, i ≠ 4 → b.arrays i v = a.arrays i v
lemma preserve_refl (s : Pure.State) : Preserve s s := by intro v hv i hi; rfl
lemma preserve_trans {a b c : Pure.State} (ab : Preserve a b) (bc : Preserve b c)
    (pab : Progress a b) (pbc : Progress b c) : Preserve a c := by
  intro v hv i hi
  rcases hv with ha | hc
  · have hb : b.arrays 0 v ≠ 0 := by rw [progress_nonwhite pab ha]; exact ha
    exact (bc v (Or.inl hb) i hi).trans (ab v (Or.inl ha) i hi)
  · have hb : b.arrays 0 v = 0 := by rcases pbc v with he | ⟨_,he⟩ <;> omega
    exact (bc v (Or.inr hc) i hi).trans (ab v (Or.inr hb) i hi)

lemma preserve {g : Graph} {task : Pure.Task} {a b : Pure.State} {k : Nat}
    (run : Eval g task a b k) : Ready task a → Preserve a b := by
  induction run with
  | @visit u l a b k hu run ih =>
    intro white v hv i hi
    obtain ⟨pr,_⟩ := progress_covered run trivial
    have gray : b.arrays 0 u = 1 := by
      have := progress_nonwhite pr (v := u) (by simp); simpa using this
    have ne : v ≠ u := by
      intro he; subst v
      rcases hv with hv | hv
      · exact hv white
      · simpa using hv
    have hv' : (enter a u l).arrays 0 v ≠ 0 ∨ b.arrays 0 v = 0 := by
      simpa [ne] using hv
    have eq := ih trivial v hv' i hi
    simpa [ne,hi] using eq
  | scan_nil => exact fun _ => preserve_refl _
  | scan_seen _ _ ih => exact ih
  | @scan_fresh u l vs a b c j k v white call rest ihcall ihrest =>
    intro _
    obtain ⟨pab,black⟩ := progress_covered call (by simpa [Ready] using white)
    obtain ⟨pbc,_⟩ := progress_covered rest trivial
    have ab : Preserve a b := by
      intro w hw i hi
      have ne : w ≠ (v : Int) := by
        intro he; subst w
        rcases hw with hw | hw
        · exact hw white
        · change b.arrays 0 (v : Int) = 2 at black; omega
      have hw' : (write a 1 (v : Int) u).arrays 0 w ≠ 0 ∨ b.arrays 0 w = 0 := by simpa using hw
      simpa [ne] using ihcall (by simpa [Ready] using white) w hw' i hi
    have pab' : Progress a b := by intro w; simpa using pab w
    exact preserve_trans ab (ihrest trivial) pab' pbc
  | roots_nil => exact fun _ => preserve_refl _
  | roots_seen _ _ ih => exact ih
  | @roots_fresh u us a b c j k white call rest ihcall ihrest =>
    intro _
    obtain ⟨pab,_⟩ := progress_covered call white
    obtain ⟨pbc,_⟩ := progress_covered rest trivial
    exact preserve_trans (ihcall white) (ihrest trivial) pab pbc

lemma count_same {g : Graph} {task : Pure.Task} {a b : Pure.State} {k : Nat}
    (run : Eval g task a b k) :
    match task with | .roots _ => True | _ => b.count = a.count := by
  induction run with
  | visit _ _ ih => simpa [leave,enter,write] using ih
  | scan_nil => rfl
  | scan_seen _ _ ih => exact ih
  | scan_fresh _ _ _ ih1 ih2 => exact ih2.trans ih1
  | roots_nil => trivial
  | roots_seen => trivial
  | roots_fresh => trivial


-- Labels are allocated in root-discovery order and inherited by recursive calls.
structure Labels (s : Pure.State) : Prop where
  count : 0 ≤ s.count
  range : ∀ v : Int, s.arrays 0 v ≠ 0 → 0 ≤ s.arrays 5 v ∧ s.arrays 5 v ≤ s.count
  coverage : ∀ label : Nat, (label : Int) < s.count →
    ∃ v : Int, s.arrays 0 v ≠ 0 ∧ s.arrays 5 v = (label : Int)
  parent : ∀ v : Int, s.arrays 0 v ≠ 0 → s.arrays 1 v ≠ -1 →
    s.arrays 0 (s.arrays 1 v) ≠ 0 ∧ s.arrays 5 (s.arrays 1 v) = s.arrays 5 v
  rootOrder : ∀ u v : Int, s.arrays 0 u ≠ 0 → s.arrays 0 v ≠ 0 →
    s.arrays 1 u = -1 → s.arrays 1 v = -1 →
    (s.arrays 5 u < s.arrays 5 v ↔ s.arrays 2 u < s.arrays 2 v)

def WhiteParents (s : Pure.State) : Prop := ∀ v : Int, s.arrays 0 v = 0 → s.arrays 1 v = -1

def LabelReady (g : Graph) (task : Pure.Task) (s : Pure.State) : Prop :=
  match task with
  | .visit u l => s.arrays 0 u = 0 ∧ l = s.count ∧
      (∀ v : Int, s.arrays 0 v = 0 → v ≠ u → s.arrays 1 v = -1) ∧
      ((s.arrays 1 u = -1 ∧ ∀ v : Int, s.arrays 0 v ≠ 0 → s.arrays 5 v < s.count) ∨
       (s.arrays 1 u ≠ -1 ∧ s.arrays 0 (s.arrays 1 u) ≠ 0 ∧ s.arrays 5 (s.arrays 1 u) = l))
  | .scan u l _ => WhiteParents s ∧ Vertex g u ∧ s.arrays 0 u = 1 ∧ s.arrays 5 u = l ∧ l = s.count
  | .roots _ => WhiteParents s ∧ ∀ v : Int, s.arrays 0 v ≠ 0 → s.arrays 5 v < s.count

lemma labels_parent {s : Pure.State} (h : Labels s) (u p : Int) (white : s.arrays 0 u = 0) :
    Labels (write s 1 u p) := by
  refine ⟨h.count,?_,?_,?_,?_⟩
  · simpa using h.range
  · simpa using h.coverage
  · intro v hv hp
    have hv' : s.arrays 0 v ≠ 0 := by simpa using hv
    have ne : v ≠ u := by intro he; subst v; exact hv' white
    have hp' : s.arrays 1 v ≠ -1 := by simpa [ne] using hp
    simpa [ne] using h.parent v hv' hp'
  · intro v w hv hw hp hq
    have hv' : s.arrays 0 v ≠ 0 := by simpa using hv
    have hw' : s.arrays 0 w ≠ 0 := by simpa using hw
    have vn : v ≠ u := by intro he; subst v; exact hv' white
    have wn : w ≠ u := by intro he; subst w; exact hw' white
    apply h.rootOrder v w hv' hw' (by simpa [vn] using hp) (by simpa [wn] using hq)

lemma labels_enter {g : Graph} {D F : Finset Int} {s : Pure.State} {u l : Int}
    (inv : Inv g D F s) (h : Labels s) (pre : LabelReady g (.visit u l) s) :
    Labels (enter s u l) ∧ WhiteParents (enter s u l) := by
  obtain ⟨white,lc,wp,parent⟩ := pre
  have oldNe (v : Int) (hv : s.arrays 0 v ≠ 0) : v ≠ u := by intro he; subst v; exact hv white
  have oldTime (v : Int) (hv : s.arrays 0 v ≠ 0) : s.arrays 2 v ≤ s.clock :=
    (inv.discovery v (by by_contra hn; exact hv ((white_iff inv v).mpr hn))).2
  have oldNonwhite (v : Int) (hv : (enter s u l).arrays 0 v ≠ 0) (ne : v ≠ u) : s.arrays 0 v ≠ 0 := by
    simpa [ne] using hv
  refine ⟨⟨h.count,?_,?_,?_,?_⟩,?_⟩
  · intro v hv
    by_cases ne : v = u
    · simpa [ne,lc] using And.intro h.count (le_refl s.count)
    · simpa [ne] using h.range v (oldNonwhite v hv ne)
  · intro tag ht
    obtain ⟨v,hv,he⟩ := h.coverage tag ht
    exact ⟨v,by simpa [oldNe v hv] using hv,by simpa [oldNe v hv] using he⟩
  · intro v hv hp
    by_cases ne : v = u
    · subst v
      have hp' : s.arrays 1 u ≠ -1 := by simpa using hp
      rcases parent with ⟨hp0,_⟩ | ⟨_,pn,pl⟩
      · exact (hp' hp0).elim
      · have pnu := oldNe _ pn
        simpa [pnu] using And.intro pn pl
    · have vn := oldNonwhite v hv ne
      have hp' : s.arrays 1 v ≠ -1 := by simpa using hp
      obtain ⟨pn,pl⟩ := h.parent v vn hp'
      simpa [ne,oldNe _ pn] using And.intro pn pl
  · intro v w hv hw hp hq
    have hp' : s.arrays 1 v = -1 := by simpa using hp
    have hq' : s.arrays 1 w = -1 := by simpa using hq
    by_cases ve : v = u <;> by_cases we : w = u
    · simp [ve,we]
    · have wn := oldNonwhite w hw we
      have wt := oldTime w wn
      have lt : s.arrays 5 w < s.count := by
        rcases parent with ⟨_,all⟩ | ⟨pu,_,_⟩
        · exact all w wn
        · exact (pu (ve ▸ hp')).elim
      simp only [enter_arrays,Fin.reduceEq,reduceIte,ve,if_pos rfl,if_neg we]
      rw [lc]; omega
    · have vn := oldNonwhite v hv ve
      have vt := oldTime v vn
      have lt : s.arrays 5 v < s.count := by
        rcases parent with ⟨_,all⟩ | ⟨pu,_,_⟩
        · exact all v vn
        · exact (pu (we ▸ hq')).elim
      simp only [enter_arrays,Fin.reduceEq,reduceIte,we,if_pos rfl,if_neg ve]
      rw [lc]; omega
    · simpa [ve,we] using h.rootOrder v w (oldNonwhite v hv ve) (oldNonwhite w hw we) hp' hq'
  · intro v hv
    have ne : v ≠ u := by intro he; subst v; simpa using hv
    have vw : s.arrays 0 v = 0 := by simpa [ne] using hv
    simpa using wp v vw ne

lemma labels_leave {s : Pure.State} {u : Int} (h : Labels s) (gray : s.arrays 0 u = 1)
    (wp : WhiteParents s) : Labels (leave s u) ∧ WhiteParents (leave s u) := by
  have nw (v : Int) : (leave s u).arrays 0 v ≠ 0 ↔ s.arrays 0 v ≠ 0 := by
    by_cases he : v = u <;> simp [he,gray]
  refine ⟨⟨h.count,?_,?_,?_,?_⟩,?_⟩
  · intro v hv; simpa using h.range v ((nw v).mp hv)
  · intro l hl
    obtain ⟨v,hv,he⟩ := h.coverage l hl
    exact ⟨v,(nw v).mpr hv,by simpa using he⟩
  · intro v hv hp
    have hp' : s.arrays 1 v ≠ -1 := by simpa using hp
    obtain ⟨pn,pl⟩ := h.parent v ((nw v).mp hv) hp'
    exact ⟨by simpa using (nw (s.arrays 1 v)).mpr pn,by simpa using pl⟩
  · intro v w hv hw hp hq
    simpa using h.rootOrder v w ((nw v).mp hv) ((nw w).mp hw) (by simpa using hp) (by simpa using hq)
  · intro v hv
    have vw : s.arrays 0 v = 0 := by
      by_cases he : v = u
      · simp [he] at hv
      · simpa [he] using hv
    simpa using wp v vw

lemma labels_nextTree {s : Pure.State} (h : Labels s) (u : Int)
    (nonwhite : s.arrays 0 u ≠ 0) (tag : s.arrays 5 u = s.count) : Labels (nextTree s) := by
  refine ⟨by change 0 ≤ s.count+1; have := h.count; omega,?_,?_,h.parent,h.rootOrder⟩
  · intro v hv
    have range := h.range v hv
    exact ⟨range.1,by change s.arrays 5 v ≤ s.count+1; omega⟩
  · intro l hl
    change (l : Int) < s.count+1 at hl
    by_cases eq : (l : Int) = s.count
    · exact ⟨u,nonwhite,tag.trans eq.symm⟩
    · exact h.coverage l (by omega)

lemma label_ready {g : Graph} {task : Pure.Task} {s : Pure.State}
    (h : LabelReady g task s) : Ready task s := by cases task <;> simp_all [Ready,LabelReady]

lemma label_run {g : Graph} {task : Pure.Task} {a b : Pure.State} {k : Nat}
    (run : Eval g task a b k) :
    ∀ D F, Inv g D F a → Labels a → LabelReady g task a → Labels b ∧ WhiteParents b := by
  induction run with
  | @visit u l a b k hu run ih =>
    intro D F inv lab pre
    have white := pre.1
    obtain ⟨entered,wp⟩ := labels_enter inv lab pre
    have entry := inv_enter inv u l hu white
    have ready : LabelReady g (.scan u l (g.neighbors u.toNat)) (enter a u l) := by
      exact ⟨wp,hu,by simp,by simp,pre.2.1⟩
    obtain ⟨lb,pb⟩ := ih _ _ entry entered ready
    have stable := preserve run trivial
    have gray : b.arrays 0 u = 1 := by
      rw [stable u (Or.inl (by simp)) 0 (by decide)]; simp
    exact labels_leave lb gray pb
  | scan_nil =>
    intro D F inv lab pre; exact ⟨lab,pre.1⟩
  | scan_seen _ _ ih => exact ih
  | @scan_fresh u l vs a b c j k v white call rest ihcall ihrest =>
    intro D F inv lab pre
    obtain ⟨wp,hu,gray,ul,lc⟩ := pre
    have un : u ≠ (v : Int) := by intro he; rw [he,white] at gray; omega
    have vu : (v : Int) ≠ u := Ne.symm un
    have pneq : u ≠ -1 := by have := hu.1; omega
    have parentLab := labels_parent lab (v : Int) u white
    have childReady : LabelReady g (.visit (v : Int) l) (write a 1 (v : Int) u) := by
      refine ⟨by simpa using white,lc,?_,Or.inr ?_⟩
      · intro w hw wn
        have ww : a.arrays 0 w = 0 := by simpa using hw
        simpa [wn] using wp w ww
      · exact ⟨by simpa using pneq,by simp [gray],by simpa using ul⟩
    obtain ⟨lb,pb⟩ := ihcall D F (inv_parent inv v u) parentLab childReady
    obtain ⟨E,H,ib,_,_⟩ := metadata call D F (inv_parent inv v u) (by simpa [Ready] using white)
    have stable := preserve call (by simpa [Ready] using white)
    have sn : (write a 1 (v : Int) u).arrays 0 u ≠ 0 := by simp [gray]
    have sourceGray : b.arrays 0 u = 1 := by
      rw [stable u (Or.inl sn) 0 (by decide)]; simpa using gray
    have sourceLabel : b.arrays 5 u = l := by
      rw [stable u (Or.inl sn) 5 (by decide)]; simpa using ul
    have same : b.count = a.count := count_same call
    exact ihrest E H ib lb ⟨pb,hu,sourceGray,sourceLabel,lc.trans same.symm⟩
  | roots_nil =>
    intro D F inv lab pre; exact ⟨lab,pre.1⟩
  | roots_seen _ _ ih => exact ih
  | @roots_fresh u us a b c j k white call rest ihcall ihrest =>
    intro D F inv lab pre
    obtain ⟨wp,closed⟩ := pre
    have childReady : LabelReady g (.visit u a.count) a :=
      ⟨white,rfl,fun v hv _ => wp v hv,Or.inl ⟨wp u white,closed⟩⟩
    obtain ⟨lb,pb⟩ := ihcall D F inv lab childReady
    obtain ⟨E,H,ib,_,_⟩ := metadata call D F inv white
    have same : b.count = a.count := count_same call
    have rootLabel : b.arrays 5 u = a.count := by
      cases call with
      | visit valid scan =>
        have stable := preserve scan trivial
        simp only [leave_arrays,Fin.reduceEq,reduceIte]
        rw [stable u (Or.inl (by simp)) 5 (by decide)]; simp
    have rootBlack : b.arrays 0 u = 2 := (progress_covered call white).2
    have ln := labels_nextTree lb u (by omega) (rootLabel.trans same.symm)
    have rn : LabelReady g (.roots us) (nextTree b) := by
      refine ⟨pb,?_⟩
      intro v hv
      change b.arrays 5 v < b.count+1
      have := (lb.range v hv).2; omega
    exact ihrest E H (inv_nextTree ib) ln rn

lemma labels_initial : Labels initial := by
  constructor <;> simp [initial]

lemma final_labels (g : Graph) (values : List Int) (a : Pure.State) (k : Nat)
    (execution : Eval g (.roots values) initial a k) : Labels a := by
  exact (label_run execution ∅ ∅ (inv_initial g) labels_initial (by simp [LabelReady,WhiteParents,initial])).1


def Before (s : Pure.State) (u v : Int) : Prop := s.arrays 0 u = 2 ∧ s.arrays 3 u < s.arrays 2 v
def Contains (s : Pure.State) (u v : Int) : Prop :=
  s.arrays 2 u ≤ s.arrays 2 v ∧ (s.arrays 0 u = 1 ∨ (s.arrays 0 v = 2 ∧ s.arrays 3 v ≤ s.arrays 3 u))
def Top (s : Pure.State) (u : Int) : Prop :=
  s.arrays 0 u = 1 ∧ ∀ v : Int, s.arrays 0 v = 1 → s.arrays 2 v ≤ s.arrays 2 u
structure Spans (g : Graph) (s : Pure.State) : Prop where
  nested : ∀ u v : Int, s.arrays 0 u ≠ 0 → s.arrays 0 v ≠ 0 → s.arrays 2 u < s.arrays 2 v →
    Before s u v ∨ Contains s u v
  parent : ∀ v : Int, s.arrays 0 v ≠ 0 → s.arrays 1 v = -1 ∨
    (s.arrays 0 (s.arrays 1 v) ≠ 0 ∧ Edge g (s.arrays 1 v) v ∧
      s.arrays 2 (s.arrays 1 v) < s.arrays 2 v ∧ Contains s (s.arrays 1 v) v)
  nearest : ∀ u v : Int, s.arrays 0 u ≠ 0 → s.arrays 0 v ≠ 0 →
    s.arrays 2 u < s.arrays 2 v → ¬ Before s u v →
    s.arrays 0 (s.arrays 1 v) ≠ 0 ∧ s.arrays 2 u ≤ s.arrays 2 (s.arrays 1 v) ∧ Contains s u (s.arrays 1 v)
  edges : ∀ u v : Int, s.arrays 0 u = 2 → Edge g u v →
    s.arrays 0 v ≠ 0 ∧ s.arrays 2 v < s.arrays 3 u

def SpanReady (g : Graph) (task : Pure.Task) (s : Pure.State) : Prop :=
  match task with
  | .visit u _ => s.arrays 0 u = 0 ∧
    (∀ v : Int, s.arrays 0 v = 0 → v ≠ u → s.arrays 1 v = -1) ∧
    ((s.arrays 1 u = -1 ∧ ∀ v : Int, s.arrays 0 v ≠ 1) ∨
     (Top s (s.arrays 1 u) ∧ Edge g (s.arrays 1 u) u))
  | .scan u _ vs => Vertex g u ∧ Top s u ∧ WhiteParents s ∧ ∀ v ∈ vs, Edge g u (v : Int)
  | .roots _ => WhiteParents s ∧ ∀ v : Int, s.arrays 0 v ≠ 1

lemma colors {g : Graph} {D F : Finset Int} {s : Pure.State} (h : Inv g D F s)
    (v : Int) (hv : s.arrays 0 v ≠ 0) : s.arrays 0 v = 1 ∨ s.arrays 0 v = 2 := by
  rw [h.color] at hv ⊢
  split_ifs <;> simp_all
lemma discovered_mem {g : Graph} {D F : Finset Int} {s : Pure.State} (h : Inv g D F s)
    (v : Int) (hv : s.arrays 0 v ≠ 0) : v ∈ D := by
  by_contra hn; exact hv ((white_iff h v).mpr hn)
lemma nonwhite_valid {g : Graph} {D F : Finset Int} {s : Pure.State} (h : Inv g D F s)
    (v : Int) (hv : s.arrays 0 v ≠ 0) : Vertex g v := h.valid v (discovered_mem h v hv)

lemma top_preserved {a b : Pure.State} {u : Int} (top : Top a u)
    (pr : Progress a b) (ps : Preserve a b) : Top b u := by
  have un : a.arrays 0 u ≠ 0 := by have := top.1; omega
  refine ⟨(progress_nonwhite pr un).trans top.1,?_⟩
  intro v gray
  have oldGray : a.arrays 0 v = 1 := by rcases pr v with he | ⟨_,he⟩ <;> omega
  have vn : a.arrays 0 v ≠ 0 := by omega
  rw [ps v (Or.inl vn) 2 (by decide),ps u (Or.inl un) 2 (by decide)]
  exact top.2 v oldGray

lemma spans_parent {g : Graph} {s : Pure.State} (h : Spans g s) (u p : Int)
    (white : s.arrays 0 u = 0) : Spans g (write s 1 u p) := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa [Before,Contains] using h.nested
  · intro v hv
    have vn : s.arrays 0 v ≠ 0 := by simpa using hv
    have ne : v ≠ u := by intro he; subst v; exact vn white
    simpa [ne,Contains] using h.parent v vn
  · intro v w hv hw lt nb
    have vn : s.arrays 0 v ≠ 0 := by simpa using hv
    have wn : s.arrays 0 w ≠ 0 := by simpa using hw
    have ne : w ≠ u := by intro he; subst w; exact wn white
    simpa [ne,Contains] using h.nearest v w vn wn (by simpa using lt) (by simpa [Before] using nb)
  · simpa using h.edges

lemma spans_enter {g : Graph} {D F : Finset Int} {s : Pure.State} {u l : Int}
    (inv : Inv g D F s) (h : Spans g s) (pre : SpanReady g (.visit u l) s) :
    Spans g (enter s u l) := by
  obtain ⟨white,_,pc⟩ := pre
  have ne (v : Int) (hv : s.arrays 0 v ≠ 0) : v ≠ u := by intro he; subst v; exact hv white
  have dt (v : Int) (hv : s.arrays 0 v ≠ 0) : s.arrays 2 v ≤ s.clock :=
    (inv.discovery v (discovered_mem inv v hv)).2
  have ft (v : Int) (hv : s.arrays 0 v = 2) : s.arrays 3 v ≤ s.clock :=
    (inv.finish v ((black_iff inv v).mp hv)).2
  have old (v : Int) (hv : (enter s u l).arrays 0 v ≠ 0) (vn : v ≠ u) : s.arrays 0 v ≠ 0 := by simpa [vn] using hv
  have oldContains (v w : Int) (hv : s.arrays 0 v ≠ 0) (hw : s.arrays 0 w ≠ 0) :
      Contains (enter s u l) v w ↔ Contains s v w := by simp [Contains,ne v hv,ne w hw]
  have oldBefore (v w : Int) (hv : s.arrays 0 v ≠ 0) (hw : s.arrays 0 w ≠ 0) :
      Before (enter s u l) v w ↔ Before s v w := by simp [Before,ne v hv,ne w hw]
  refine ⟨?_,?_,?_,?_⟩
  · intro v w hv hw lt
    by_cases ve : v = u
    · subst v
      by_cases we : w = u
      · subst w; omega
      · have wt := dt w (old w hw we); simp [we] at lt; omega
    · have vn := old v hv ve
      by_cases we : w = u
      · subst w
        rcases colors inv v vn with gray | black
        · right
          have vt := dt v vn
          simp [Contains,ve,gray]; omega
        · left
          have vt := ft v black
          simp [Before,ve,black]; omega
      · have wn := old w hw we
        have lt' : s.arrays 2 v < s.arrays 2 w := by simpa [ve,we] using lt
        rcases h.nested v w vn wn lt' with hb | hc
        · exact Or.inl ((oldBefore v w vn wn).mpr hb)
        · exact Or.inr ((oldContains v w vn wn).mpr hc)
  · intro v hv
    by_cases ve : v = u
    · subst v
      rcases pc with ⟨root,_⟩ | ⟨top,edge⟩
      · exact Or.inl (by simpa using root)
      · right
        have pn : s.arrays 0 (s.arrays 1 u) ≠ 0 := by have := top.1; omega
        have pnu := ne _ pn
        have pt := dt _ pn
        refine ⟨by simpa [pnu] using pn,by simpa using edge,?_,?_⟩
        · simp [pnu]; omega
        · simp [Contains,pnu,top.1]; omega
    · have vn := old v hv ve
      rcases h.parent v vn with root | ⟨pn,edge,lt,ct⟩
      · exact Or.inl (by simpa using root)
      · right
        exact ⟨by simpa [ne _ pn] using pn,by simpa using edge,
          by simpa [ne _ pn,ve] using lt,(by simpa using (oldContains _ _ pn vn).mpr ct)⟩
  · intro v w hv hw lt nb
    by_cases ve : v = u
    · subst v
      by_cases we : w = u
      · subst w; omega
      · have wt := dt w (old w hw we); simp [we] at lt; omega
    · have vn := old v hv ve
      by_cases we : w = u
      · subst w
        have vg : s.arrays 0 v = 1 := by
          rcases colors inv v vn with gray | black
          · exact gray
          · have ftv := ft v black
            apply False.elim; apply nb; simp [Before,ve,black]; omega
        rcases pc with ⟨_,none⟩ | ⟨top,edge⟩
        · exact (none v vg).elim
        · have pn : s.arrays 0 (s.arrays 1 u) ≠ 0 := by have := top.1; omega
          have pnu := ne _ pn
          have vp := top.2 v vg
          refine ⟨by simpa [pnu] using pn,by simpa [ve,pnu] using vp,?_⟩
          simpa [Contains,ve,pnu,vg] using vp
      · have wn := old w hw we
        have lt' : s.arrays 2 v < s.arrays 2 w := by simpa [ve,we] using lt
        have nb' : ¬ Before s v w := fun hb => nb ((oldBefore v w vn wn).mpr hb)
        obtain ⟨pn,le,ct⟩ := h.nearest v w vn wn lt' nb'
        refine ⟨by simpa [ne _ pn] using pn,by simpa [ve,ne _ pn] using le,?_⟩
        simpa using (oldContains v _ vn pn).mpr ct
  · intro v w black edge
    have ve : v ≠ u := by intro he; subst v; simp at black
    have black' : s.arrays 0 v = 2 := by simpa [ve] using black
    obtain ⟨wn,lt⟩ := h.edges v w black' edge
    exact ⟨by simpa [ne w wn] using wn,by simpa [ne w wn] using lt⟩

lemma contains_leave {g : Graph} {D F : Finset Int} {s : Pure.State} {u v w : Int}
    (inv : Inv g D F s) (top : Top s u)
    (vn : s.arrays 0 v ≠ 0) (wn : s.arrays 0 w ≠ 0)
    (h : Contains s v w) : Contains (leave s u) v w := by
  refine ⟨by simpa using h.1,?_⟩
  by_cases ve : v = u
  · subst v
    right
    by_cases we : w = u
    · simp [we]
    · have wb : s.arrays 0 w = 2 := by
        rcases colors inv w wn with gray | black
        · have le := top.2 w gray
          have eq : s.arrays 2 u = s.arrays 2 w := by have := h.1; omega
          exact (we (inv.discoveryDistinct u (discovered_mem inv u (by have := top.1; omega)) w
            (discovered_mem inv w wn) eq).symm).elim
        · exact black
      have ft := (inv.finish w ((black_iff inv w).mp wb)).2
      simp [we,wb]; omega
  · rcases h.2 with gray | ⟨black,le⟩
    · left; simpa [ve] using gray
    · right
      have we : w ≠ u := by intro he; subst w; have := top.1; omega
      simpa [ve,we] using And.intro black le

lemma before_leave {s : Pure.State} {u v w : Int} (top : Top s u) (h : Before s v w) :
    Before (leave s u) v w := by
  have ne : v ≠ u := by intro he; subst v; have := top.1; have := h.1; omega
  simpa [Before,ne] using h

lemma spans_leave {g : Graph} {D F : Finset Int} {s : Pure.State} {u : Int}
    (inv : Inv g D F s) (h : Spans g s) (top : Top s u)
    (scanned : ∀ v : Nat, v ∈ g.neighbors u.toNat → s.arrays 0 (v : Int) ≠ 0) :
    Spans g (leave s u) := by
  have nw (v : Int) : (leave s u).arrays 0 v ≠ 0 ↔ s.arrays 0 v ≠ 0 := by
    by_cases he : v = u <;> simp [he,top.1]
  refine ⟨?_,?_,?_,?_⟩
  · intro v w vn wn lt
    have vn' := (nw v).mp vn; have wn' := (nw w).mp wn
    rcases h.nested v w vn' wn' (by simpa using lt) with hb | hc
    · exact Or.inl (before_leave top hb)
    · exact Or.inr (contains_leave inv top vn' wn' hc)
  · intro v vn
    have vn' := (nw v).mp vn
    rcases h.parent v vn' with root | ⟨pn,edge,lt,ct⟩
    · exact Or.inl (by simpa using root)
    · refine Or.inr ⟨by simpa using (nw _).mpr pn,by simpa using edge,by simpa using lt,?_⟩
      simpa using contains_leave inv top pn vn' ct
  · intro v w vn wn lt nb
    have vn' := (nw v).mp vn; have wn' := (nw w).mp wn
    have nb' : ¬ Before s v w := fun hb => nb (before_leave top hb)
    obtain ⟨pn,le,ct⟩ := h.nearest v w vn' wn' (by simpa using lt) nb'
    refine ⟨by simpa using (nw _).mpr pn,by simpa using le,?_⟩
    simpa using contains_leave inv top vn' pn ct
  · intro v w black edge
    by_cases ve : v = u
    · subst v
      have wn : s.arrays 0 w ≠ 0 := by
        have wm : w.toNat ∈ g.neighbors u.toNat := edge.2.2
        have w0 : (w.toNat : Int) = w := Int.toNat_of_nonneg edge.2.1.1
        simpa [w0] using scanned w.toNat wm
      have dt := (inv.discovery w (discovered_mem inv w wn)).2
      exact ⟨(nw _).mpr wn,by simp; omega⟩
    · have vb : s.arrays 0 v = 2 := by simpa [ve] using black
      obtain ⟨wn,lt⟩ := h.edges v w vb edge
      exact ⟨(nw _).mpr wn,by simpa [ve] using lt⟩

lemma span_ready {g : Graph} {task : Pure.Task} {s : Pure.State}
    (h : SpanReady g task s) : Ready task s := by cases task <;> simp_all [Ready,SpanReady]

lemma spans_nextTree {g : Graph} {s : Pure.State} (h : Spans g s) : Spans g (nextTree s) := by
  rcases h with ⟨a,b,c,d⟩; exact ⟨a,b,c,d⟩

lemma span_run {g : Graph} {task : Pure.Task} {a b : Pure.State} {k : Nat}
    (run : Eval g task a b k) :
    ∀ D F, Inv g D F a → Spans g a → SpanReady g task a → Spans g b ∧ WhiteParents b := by
  induction run with
  | @visit u l a b k hu run ih =>
    intro D F inv span pre
    have white := pre.1
    have entered := spans_enter inv span pre
    have ei := inv_enter inv u l hu white
    have top : Top (enter a u l) u := by
      refine ⟨by simp,?_⟩
      intro v gray
      by_cases ve : v = u
      · simp [ve]
      · have vg : a.arrays 0 v = 1 := by simpa [ve] using gray
        have dt := (inv.discovery v (discovered_mem inv v (by omega))).2
        simp [ve]; omega
    have wp : WhiteParents (enter a u l) := by
      intro v hv
      have ne : v ≠ u := by intro he; subst v; simp at hv
      have vw : a.arrays 0 v = 0 := by simpa [ne] using hv
      simpa using pre.2.1 v vw ne
    have row : ∀ v ∈ g.neighbors u.toNat, Edge g u (v : Int) := by
      intro v hv
      have un : u.toNat < g.size := by have := hu.1; have := hu.2; omega
      have bound := g.bounded u.toNat un v hv
      exact ⟨hu,⟨by omega,by exact_mod_cast bound⟩,by simpa using hv⟩
    obtain ⟨out,pb⟩ := ih _ _ ei entered ⟨hu,top,wp,row⟩
    obtain ⟨E,H,ib,_,_⟩ := metadata run _ _ ei trivial
    obtain ⟨pr,scanned⟩ := progress_covered run trivial
    have tp := top_preserved top pr (preserve run trivial)
    refine ⟨spans_leave ib out tp scanned,?_⟩
    intro v hv
    have ne : v ≠ u := by intro he; subst v; simp at hv
    have vw : b.arrays 0 v = 0 := by simpa [ne] using hv
    simpa using pb v vw
  | scan_nil => intro D F inv span pre; exact ⟨span,pre.2.2.1⟩
  | @scan_seen u l vs a b k v seen run ih =>
    intro D F inv span pre
    exact ih D F inv span ⟨pre.1,pre.2.1,pre.2.2.1,fun w hw => pre.2.2.2 w (by simp [hw])⟩
  | @scan_fresh u l vs a b c j k v white call rest ihcall ihrest =>
    intro D F inv span pre
    obtain ⟨hu,top,wp,row⟩ := pre
    have childPre : SpanReady g (.visit (v : Int) l) (write a 1 (v : Int) u) := by
      refine ⟨by simpa using white,?_,Or.inr ?_⟩
      · intro w hw wn
        have ww : a.arrays 0 w = 0 := by simpa using hw
        simpa [wn] using wp w ww
      · refine ⟨?_,?_⟩
        · simpa [Top] using top
        · simpa using row v (by simp)
    obtain ⟨out,pb⟩ := ihcall D F (inv_parent inv v u) (spans_parent span v u white) childPre
    obtain ⟨E,H,ib,_,_⟩ := metadata call D F (inv_parent inv v u) (by simpa [Ready] using white)
    have pr := (progress_covered call (by simpa [Ready] using white)).1
    have ps := preserve call (by simpa [Ready] using white)
    have oldtop : Top (write a 1 (v : Int) u) u := by simpa [Top] using top
    exact ihrest E H ib out ⟨hu,top_preserved oldtop pr ps,pb,fun w hw => row w (by simp [hw])⟩
  | roots_nil => intro D F inv span pre; exact ⟨span,pre.1⟩
  | @roots_seen u us a b k seen run ih =>
    intro D F inv span pre; exact ih D F inv span pre
  | @roots_fresh u us a b c j k white call rest ihcall ihrest =>
    intro D F inv span pre
    have parent : a.arrays 1 u = -1 := pre.1 u white
    obtain ⟨out,pb⟩ := ihcall D F inv span
      ⟨white,fun v hv _ => pre.1 v hv,Or.inl ⟨parent,pre.2⟩⟩
    obtain ⟨E,H,ib,_,_⟩ := metadata call D F inv white
    have pr := (progress_covered call white).1
    have noGray : ∀ v : Int, (nextTree b).arrays 0 v ≠ 1 := by
      intro v gray
      change b.arrays 0 v = 1 at gray
      have old : a.arrays 0 v = 1 := by rcases pr v with he | ⟨_,he⟩ <;> omega
      exact pre.2 v old
    exact ihrest E H (inv_nextTree ib) (spans_nextTree out) ⟨pb,noGray⟩

lemma spans_initial (g : Graph) : Spans g initial := by
  constructor <;> simp [initial]

lemma final_spans (g : Graph) (values : List Int) (a : Pure.State) (k : Nat)
    (execution : Eval g (.roots values) initial a k) : Spans g a :=
  (span_run execution ∅ ∅ (inv_initial g) (spans_initial g)
    (by simp [SpanReady,WhiteParents,initial])).1


lemma visit_fields {g : Graph} {a b : Pure.State} {u l : Int} {k : Nat}
    (run : Eval g (.visit u l) a b k) :
    b.arrays 1 u = a.arrays 1 u ∧ b.arrays 2 u = a.clock+1 ∧ b.arrays 3 u = b.clock := by
  cases run with
  | @visit _ _ _ c _ hu scan =>
    have ps := preserve scan trivial
    have parent := ps u (Or.inl (by simp)) 1 (by decide)
    have discover := ps u (Or.inl (by simp)) 2 (by decide)
    exact ⟨by simpa using parent,by simpa using discover,by simp⟩

def RootBirth (task : Pure.Task) (a b : Pure.State) : Prop :=
  match task with
  | .visit u _ => ∀ v : Int, b.arrays 0 v ≠ 0 → b.arrays 1 v = -1 → a.arrays 0 v ≠ 0 ∨ v = u
  | .scan _ _ _ => ∀ v : Int, b.arrays 0 v ≠ 0 → b.arrays 1 v = -1 → a.arrays 0 v ≠ 0
  | .roots _ => True

def BirthReady (g : Graph) (task : Pure.Task) (s : Pure.State) : Prop :=
  Ready task s ∧ match task with | .scan u _ _ => Vertex g u | _ => True

lemma root_birth {g : Graph} {task : Pure.Task} {a b : Pure.State} {k : Nat}
    (run : Eval g task a b k) : BirthReady g task a → RootBirth task a b := by
  induction run with
  | @visit u l a b k hu scan ih =>
    intro pre v vn vp
    have ne : v ≠ u → a.arrays 0 v ≠ 0 := by
      intro ve
      have bn : b.arrays 0 v ≠ 0 := by simpa [ve] using vn
      have bp : b.arrays 1 v = -1 := by simpa using vp
      have old := ih ⟨trivial,hu⟩ v bn bp
      simpa [ve] using old
    by_cases ve : v = u
    · exact Or.inr ve
    · exact Or.inl (ne ve)
  | scan_nil => intro _ v vn vp; exact vn
  | @scan_seen u l vs a b k v seen rest ih => exact ih
  | @scan_fresh u l vs a b c j k v white call rest ihcall ihrest =>
    intro pre w wn wp
    have bn := ihrest pre w wn wp
    have ps := preserve rest trivial
    have bp : b.arrays 1 w = -1 := (ps w (Or.inl bn) 1 (by decide)).symm.trans wp
    rcases ihcall ⟨by simpa [Ready] using white,trivial⟩ w bn bp with old | eq
    · simpa using old
    · have p := (visit_fields call).1
      have hu : Vertex g u := pre.2
      have u0 := hu.1
      rw [eq] at bp
      have p' : b.arrays 1 (v : Int) = u := by simpa using p
      omega
  | roots_nil => exact fun _ => trivial
  | roots_seen => exact fun _ => trivial
  | roots_fresh => exact fun _ => trivial

-- Before a root can be selected, every earlier vertex in the outer order is black.
def Priority (values : List Int) (s : Pure.State) : Prop :=
  ∀ v : Int, s.arrays 0 v ≠ 0 → s.arrays 1 v = -1 →
    ∀ w ∈ values, values.idxOf w < values.idxOf v →
      s.arrays 0 w = 2 ∧ s.arrays 3 w < s.arrays 2 v

lemma priority_visit {g : Graph} {D F : Finset Int} {a b : Pure.State} {u l : Int} {k : Nat}
    (run : Eval g (.visit u l) a b k) (white : a.arrays 0 u = 0)
    (inv : Inv g D F a) (values processed remaining : List Int)
    (split : values = processed ++ u :: remaining) (nodup : values.Nodup)
    (closed : ∀ v ∈ processed, a.arrays 0 v = 2) (prio : Priority values a) : Priority values b := by
  have ps := preserve run white
  have pr := (progress_covered run white).1
  intro v vn vp w wm before
  by_cases old : a.arrays 0 v = 0
  · have root : v = u := by
      rcases root_birth run ⟨white,trivial⟩ v vn vp with no | eq
      · exact (no old).elim
      · exact eq
    subst v
    have unm : u ∉ processed := by
      rw [split] at nodup
      exact fun hu => (List.nodup_append.mp nodup).2.2 u hu u (by simp) rfl
    have idx : values.idxOf u = processed.length := by
      rw [split,List.idxOf_append_of_notMem unm]; simp
    have wp : w ∈ processed := by
      apply (List.IsPrefix.mem_iff_idxOf_lt_length (l₁ := processed) (l₂ := values) ?_ w).mpr
      · simpa [idx] using before
      · rw [split]; exact List.prefix_append _ _
    have wb := closed w wp
    have wn : a.arrays 0 w ≠ 0 := by omega
    have ft := (inv.finish w ((black_iff inv w).mp wb)).2
    refine ⟨(progress_nonwhite pr wn).trans wb,?_⟩
    rw [ps w (Or.inl wn) 3 (by decide),(visit_fields run).2.1]
    omega
  · have oldRoot : a.arrays 1 v = -1 := (ps v (Or.inl old) 1 (by decide)).symm.trans vp
    obtain ⟨wb,lt⟩ := prio v old oldRoot w wm before
    have wn : a.arrays 0 w ≠ 0 := by omega
    refine ⟨(progress_nonwhite pr wn).trans wb,?_⟩
    rw [ps w (Or.inl wn) 3 (by decide),ps v (Or.inl old) 2 (by decide)]
    exact lt

lemma priority_roots (g : Graph) (values : List Int) (nodup : values.Nodup)
    (remaining processed : List Int) (split : values = processed ++ remaining)
    (a b : Pure.State) (k : Nat) (run : Eval g (.roots remaining) a b k)
    (D F : Finset Int) (inv : Inv g D F a) (span : Spans g a)
    (ready : SpanReady g (.roots remaining) a)
    (closed : ∀ v ∈ processed, a.arrays 0 v = 2) (prio : Priority values a) : Priority values b := by
  induction remaining generalizing processed a b k D F with
  | nil => cases run; exact prio
  | cons u us ih =>
    have sp : values = (processed ++ [u]) ++ us := by simpa [List.append_assoc] using split
    cases run with
    | roots_seen seen rest =>
      have ub : a.arrays 0 u = 2 := by
        rcases colors inv u seen with gray | black
        · exact (ready.2 u gray).elim
        · exact black
      have cl : ∀ v ∈ processed ++ [u], a.arrays 0 v = 2 := by
        intro v hv
        rcases List.mem_append.mp hv with hv | hv
        · exact closed v hv
        · simpa only [List.mem_singleton.mp hv] using ub
      exact ih (processed ++ [u]) sp a b _ rest D F inv span ready cl prio
    | @roots_fresh _ _ _ middle _ j _ white call rest =>
      have child : SpanReady g (.visit u a.count) a :=
        ⟨white,fun v hv _ => ready.1 v hv,Or.inl ⟨ready.1 u white,ready.2⟩⟩
      obtain ⟨sm,pm⟩ := span_run call D F inv span child
      obtain ⟨E,H,im,_,_⟩ := metadata call D F inv white
      have pr := (progress_covered call white).1
      have black : middle.arrays 0 u = 2 := (progress_covered call white).2
      have cl : ∀ v ∈ processed ++ [u], (nextTree middle).arrays 0 v = 2 := by
        intro v hv
        rcases List.mem_append.mp hv with hv | hv
        · have vb := closed v hv
          exact (progress_nonwhite pr (by omega)).trans vb
        · simpa only [List.mem_singleton.mp hv, nextTree] using black
      have none : ∀ v : Int, (nextTree middle).arrays 0 v ≠ 1 := by
        intro v gray
        have old : a.arrays 0 v = 1 := by
          change middle.arrays 0 v = 1 at gray
          rcases pr v with he | ⟨_,he⟩ <;> omega
        exact ready.2 v old
      have prio' := priority_visit call white inv values processed us split nodup closed prio
      exact ih (processed ++ [u]) sp (nextTree middle) b _ rest E H (inv_nextTree im)
        (spans_nextTree sm) ⟨pm,none⟩ cl prio'

lemma final_priority (g : Graph) (values : List Int) (nodup : values.Nodup)
    (a : Pure.State) (k : Nat) (run : Eval g (.roots values) initial a k) : Priority values a := by
  exact priority_roots g values nodup values [] (by simp) initial a k run ∅ ∅ (inv_initial g)
    (spans_initial g) (by simp [SpanReady,WhiteParents,initial]) (by simp)
    (by simp [Priority,initial])


lemma visit_label {g : Graph} {a b : Pure.State} {u l : Int} {k : Nat}
    (run : Eval g (.visit u l) a b k) : b.arrays 5 u = l := by
  cases run with
  | @visit _ _ _ c _ hu scan =>
    have eq := preserve scan trivial u (Or.inl (by simp)) 5 (by decide)
    simpa using eq

lemma roots_closed (g : Graph) (values : List Int) (a b : Pure.State) (k : Nat)
    (run : Eval g (.roots values) a b k) (D F : Finset Int) (inv : Inv g D F a)
    (lab : Labels a) (pre : LabelReady g (.roots values) a) :
    ∀ v : Int, b.arrays 0 v ≠ 0 → b.arrays 5 v < b.count := by
  induction values generalizing a b k D F with
  | nil => cases run; exact pre.2
  | cons u us ih =>
    cases run with
    | roots_seen seen rest => exact ih a b _ rest D F inv lab pre
    | @roots_fresh _ _ _ middle _ j _ white call rest =>
      have childPre : LabelReady g (.visit u a.count) a :=
        ⟨white,rfl,fun v hv _ => pre.1 v hv,Or.inl ⟨pre.1 u white,pre.2⟩⟩
      obtain ⟨lm,pm⟩ := label_run call D F inv lab childPre
      obtain ⟨E,H,im,_,_⟩ := metadata call D F inv white
      have same : middle.count = a.count := count_same call
      have black : middle.arrays 0 u = 2 := (progress_covered call white).2
      have labnext := labels_nextTree lm u (by omega) ((visit_label call).trans same.symm)
      have readynext : LabelReady g (.roots us) (nextTree middle) := by
        refine ⟨pm,?_⟩
        intro v hv
        change middle.arrays 5 v < middle.count+1
        have := (lm.range v hv).2; omega
      exact ih (nextTree middle) b _ rest E H (inv_nextTree im) labnext readynext

end DFSMetadata

open DFSMetadata

theorem solution (g : Graph) (input : Seq) (values : List Int)
    (permutation : values.Perm ((List.range g.size).map Int.ofNat))
    (observed : ∀ i : Nat, i < g.size → input i = values[i]!)
    (a : Pure.State) (k : Nat) (execution : Eval g (.roots values) initial a k) :
    LocalCertificate g input (a.arrays 1) (a.arrays 2) (a.arrays 3)
      (a.arrays 4) (a.arrays 5) a.count.toNat := by
  have inv := final_metadata g values permutation a k execution
  have lab := final_labels g values a k execution
  have span := final_spans g values a k execution
  have closed := roots_closed g values initial a k execution ∅ ∅ (inv_initial g) labels_initial
    (by simp [LabelReady,WhiteParents,initial])
  have nd : values.Nodup := permutation.nodup_iff.mpr
    ((List.nodup_range (n := g.size)).map (by intro x y h; exact Int.ofNat_inj.mp h))
  have prio := final_priority g values nd a k execution
  have len : values.length = g.size := by simpa using permutation.length_eq
  have black (v : Int) (hv : Vertex g v) : a.arrays 0 v = 2 :=
    (black_iff inv v).mpr ((mem_vertices g v).mpr hv)
  have nw (v : Int) (hv : Vertex g v) : a.arrays 0 v ≠ 0 := by rw [black v hv]; omega
  have vc (v : Int) (hv : Vertex g v) : v ∈ vertices g := (mem_vertices g v).mpr hv
  have count : (a.count.toNat : Int) = a.count := Int.toNat_of_nonneg lab.count
  have get (i : Nat) (hi : i < g.size) : input i = values[i]'(by omega) := by
    rw [observed i hi]
    simp [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem (show i < values.length by omega)]
  have valid (i : Nat) (hi : i < g.size) : Vertex g (input i) := by
    have mem : input i ∈ values := by rw [get i hi]; exact List.getElem_mem (by omega)
    have rm := permutation.mem_iff.mp mem
    obtain ⟨v,hv,he⟩ := List.mem_map.mp rm
    rw [← he]
    change 0 ≤ (v : Int) ∧ (v : Int) < (g.size : Int)
    have vn := List.mem_range.mp hv; omega
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,final_order inv,?_,?_,?_,?_,?_⟩
  · intro v hv
    have dt := inv.discovery v (vc v hv)
    have ft := inv.finish v (vc v hv)
    have clock := inv.clock
    simp only [vertices_card] at clock
    exact ⟨dt.1,ft.1,by omega⟩
  · intro u v hu hv eq
    exact inv.discoveryDistinct u (vc u hu) v (vc v hv) eq
  · intro u v hu hv eq
    exact inv.finishDistinct u (vc u hu) v (vc v hv) eq
  · intro u v hu hv
    exact inv.eventDistinct u (vc u hu) v (vc v hv)
  · intro u v hu hv
    by_cases lt : a.arrays 2 u < a.arrays 2 v
    · rcases span.nested u v (nw u hu) (nw v hv) lt with bef | con
      · exact Or.inl bef.2
      · have ff : a.arrays 3 v ≤ a.arrays 3 u := by simpa [Contains,black u hu,black v hv] using con.2
        exact Or.inr (Or.inr (Or.inl ⟨le_of_lt lt,ff⟩))
    · by_cases gt : a.arrays 2 v < a.arrays 2 u
      · rcases span.nested v u (nw v hv) (nw u hu) gt with bef | con
        · exact Or.inr (Or.inl bef.2)
        · have ff : a.arrays 3 u ≤ a.arrays 3 v := by simpa [Contains,black v hv,black u hu] using con.2
          exact Or.inr (Or.inr (Or.inr ⟨le_of_lt gt,ff⟩))
      · have eq : u = v := inv.discoveryDistinct u (vc u hu) v (vc v hv) (by omega)
        subst v; exact Or.inr (Or.inr (Or.inl ⟨le_refl _,le_refl _⟩))
  · intro v hv
    rcases span.parent v (nw v hv) with root | ⟨pn,edge,lt,ct⟩
    · exact Or.inl root
    · right
      have pv := nonwhite_valid inv _ pn
      have ff : a.arrays 3 v ≤ a.arrays 3 (a.arrays 1 v) := by simpa [Contains,black _ pv,black v hv] using ct.2
      have ne : a.arrays 3 v ≠ a.arrays 3 (a.arrays 1 v) := by
        intro eq
        have ve := inv.finishDistinct v (vc v hv) _ (vc _ pv) eq
        rw [← ve] at lt; omega
      exact ⟨edge,lt,by omega⟩
  · intro u v hu hv lt ff
    have nb : ¬ Before a u v := by
      intro bef; have df := (inv.finish v (vc v hv)).1; have := bef.2; omega
    obtain ⟨pn,le,ct⟩ := span.nearest u v (nw u hu) (nw v hv) lt nb
    have pv := nonwhite_valid inv _ pn
    have pf : a.arrays 3 (a.arrays 1 v) ≤ a.arrays 3 u := by simpa [Contains,black u hu,black _ pv] using ct.2
    exact ⟨pv,le,pf⟩
  · intro u v edge
    exact (span.edges u v (black u edge.1) edge).2
  · intro i hi root j hj
    have im : input i ∈ values := by rw [get i hi]; exact List.getElem_mem (by omega)
    have jm : input j ∈ values := by rw [get j (by omega)]; exact List.getElem_mem (by omega)
    have ii : values.idxOf (input i) = i := by rw [get i hi]; exact nd.idxOf_getElem i (by omega)
    have ji : values.idxOf (input j) = j := by rw [get j (by omega)]; exact nd.idxOf_getElem j (by omega)
    exact (prio (input i) (nw _ (valid i hi)) root (input j) jm (by omega)).2
  · intro i j hij hj
    exact inv.orderIncreasing i j hij (by simpa using hj)
  · intro v hv
    exact ⟨(lab.range v (nw v hv)).1,by rw [count]; exact closed v (nw v hv)⟩
  · intro tag ht
    have ht' : (tag : Int) < a.count := by rw [← count]; exact_mod_cast ht
    obtain ⟨v,vn,vl⟩ := lab.coverage tag ht'
    exact ⟨v,nonwhite_valid inv v vn,vl⟩
  · intro v hv hp
    exact (lab.parent v (nw v hv) hp).2
  · intro u v hu hv ru rv
    exact lab.rootOrder u v (nw u hu) (nw v hv) ru rv
