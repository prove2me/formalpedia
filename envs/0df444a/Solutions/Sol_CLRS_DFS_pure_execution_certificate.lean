-- Prove2me | solution 1 for CLRS.DFS.pure_execution_certificate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:04:47.17193+00:00
-- url     : https://prove2.me/submissions/937c4e00-0094-4f39-ad2c-42244414c60d

import Theorems.Thm_CLRS_DFS_local_certificate_of_execution
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Finset.Range

set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
open Algo2LeanGenerated CLRS.GraphTraversal CLRS.DFS CLRS.DFS.Pure
open scoped BigOperators

namespace DFSTermination

-- The unvisited vertices carry all future visit and edge-scanning work.
def whiteWeight (g : Graph) (weight : Nat → Nat) (s : Pure.State) : Nat :=
  ∑ v ∈ Finset.range g.size, if s.arrays 0 (v : Int) = 0 then weight v else 0

def whites (g : Graph) (s : Pure.State) : Nat := whiteWeight g (fun _ => 1) s

def potential (g : Graph) (s : Pure.State) : Nat :=
  whiteWeight g (fun v => 4 + 2 * (g.neighbors v).length) s

-- A finished call preserves every previously nonwhite color. New vertices are black.
def Progress (a b : Pure.State) : Prop :=
  ∀ v : Int, b.arrays 0 v = a.arrays 0 v ∨ (a.arrays 0 v = 0 ∧ b.arrays 0 v = 2)

@[simp] theorem write_arrays (s : Pure.State) (a i : Fin 6) (u v x : Int) :
    (write s a u v).arrays i x = if i = a then if x = u then v else s.arrays i x
      else s.arrays i x := by
  by_cases h : i = a <;> by_cases hx : x = u <;> simp [write, h, hx]

@[simp] theorem write_clock (s : Pure.State) (a : Fin 6) (u v : Int) :
    (write s a u v).clock = s.clock := rfl
@[simp] theorem write_finished (s : Pure.State) (a : Fin 6) (u v : Int) :
    (write s a u v).finished = s.finished := rfl
@[simp] theorem write_count (s : Pure.State) (a : Fin 6) (u v : Int) :
    (write s a u v).count = s.count := rfl
@[simp] theorem enter_color (s : Pure.State) (u l v : Int) :
    (enter s u l).arrays 0 v = if v = u then 1 else s.arrays 0 v := by simp [enter]
@[simp] theorem leave_color (s : Pure.State) (u v : Int) :
    (leave s u).arrays 0 v = if v = u then 2 else s.arrays 0 v := by simp [leave]
@[simp] theorem enter_clock (s : Pure.State) (u l : Int) :
    (enter s u l).clock = s.clock + 1 := rfl
@[simp] theorem enter_finished (s : Pure.State) (u l : Int) :
    (enter s u l).finished = s.finished := rfl
@[simp] theorem enter_count (s : Pure.State) (u l : Int) :
    (enter s u l).count = s.count := rfl
@[simp] theorem leave_clock (s : Pure.State) (u : Int) :
    (leave s u).clock = s.clock + 1 := rfl
@[simp] theorem leave_finished (s : Pure.State) (u : Int) :
    (leave s u).finished = s.finished + 1 := rfl
@[simp] theorem leave_count (s : Pure.State) (u : Int) :
    (leave s u).count = s.count := rfl

lemma weight_congr {g : Graph} {a b : Pure.State} (weight : Nat → Nat)
    (h : ∀ v : Int, b.arrays 0 v = a.arrays 0 v) :
    whiteWeight g weight b = whiteWeight g weight a := by
  apply Finset.sum_congr rfl
  intro v _; rw [h]

lemma weight_remove {g : Graph} {a b : Pure.State} (weight : Nat → Nat)
    {u : Int} (hu : Vertex g u) (white : a.arrays 0 u = 0)
    (notwhite : b.arrays 0 u ≠ 0)
    (unchanged : ∀ v : Int, v ≠ u → b.arrays 0 v = a.arrays 0 v) :
    whiteWeight g weight b + weight u.toNat = whiteWeight g weight a := by
  have hu' : u.toNat ∈ Finset.range g.size := by
    have h0 := hu.1; have hn := hu.2
    simp only [Finset.mem_range]; omega
  have hu0 : (u.toNat : Int) = u := Int.toNat_of_nonneg hu.1
  have hsum : (∑ v ∈ (Finset.range g.size).erase u.toNat,
      if b.arrays 0 (v : Int) = 0 then weight v else 0) =
      ∑ v ∈ (Finset.range g.size).erase u.toNat,
      if a.arrays 0 (v : Int) = 0 then weight v else 0 := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [unchanged _ (by have := (Finset.mem_erase.mp hv).1; omega)]
  unfold whiteWeight
  rw [← Finset.sum_erase_add _ _ hu', ← Finset.sum_erase_add _
    (fun v : Nat => if a.arrays 0 (v : Int) = 0 then weight v else 0) hu']
  simp only [hu0, if_neg notwhite, if_pos white, Nat.add_zero, hsum]

lemma progress_refl (s : Pure.State) : Progress s s := fun _ => Or.inl rfl
lemma progress_trans {a b c : Pure.State} (ab : Progress a b) (bc : Progress b c) :
    Progress a c := by
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

lemma progress_weight {g : Graph} {a b : Pure.State} (h : Progress a b)
    (weight : Nat → Nat) : whiteWeight g weight b ≤ whiteWeight g weight a := by
  apply Finset.sum_le_sum
  intro v _
  rcases h (v : Int) with he | ⟨ha,hb⟩
  · simp [he]
  · simp [ha,hb]

lemma progress_whites {g : Graph} {a b : Pure.State} (h : Progress a b) :
    whites g b ≤ whites g a := progress_weight h _

lemma weight_write_parent (g : Graph) (weight : Nat → Nat) (s : Pure.State) (u v : Int) :
    whiteWeight g weight (write s 1 u v) = whiteWeight g weight s :=
  weight_congr weight (by intro x; simp)

lemma weight_enter {g : Graph} (weight : Nat → Nat) (s : Pure.State) (u l : Int)
    (hu : Vertex g u) (hw : s.arrays 0 u = 0) :
    whiteWeight g weight (enter s u l) + weight u.toNat = whiteWeight g weight s :=
  weight_remove weight hu hw (by simp) (by intro v hv; simp [hv])

lemma weight_leave {g : Graph} (weight : Nat → Nat) (s : Pure.State) (u : Int)
    (hu : s.arrays 0 u ≠ 0) :
    whiteWeight g weight (leave s u) = whiteWeight g weight s := by
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : (v : Int) = u
  · simp [hv, hu]
  · simp [hv]

structure Accounting (g : Graph) (a b : Pure.State) : Prop where
  progress : Progress a b
  clock : b.clock + 2 * (whites g b : Int) = a.clock + 2 * (whites g a : Int)
  finished : b.finished + (whites g b : Int) = a.finished + (whites g a : Int)
  count : b.count = a.count

lemma accounting_refl (g : Graph) (s : Pure.State) : Accounting g s s :=
  ⟨progress_refl _,rfl,rfl,rfl⟩

lemma accounting_trans {g : Graph} {a b c : Pure.State}
    (ab : Accounting g a b) (bc : Accounting g b c) : Accounting g a c := by
  refine ⟨progress_trans ab.progress bc.progress,?_,?_,bc.count.trans ab.count⟩
  · have := ab.clock; have := bc.clock; omega
  · have := ab.finished; have := bc.finished; omega

lemma accounting_parent {g : Graph} {a b : Pure.State} {u v : Int}
    (h : Accounting g (write a 1 u v) b) : Accounting g a b := by
  have hw : whites g (write a 1 u v) = whites g a := weight_write_parent _ _ _ _ _
  refine ⟨?_,?_,?_,?_⟩
  · intro x; simpa using h.progress x
  · simpa [hw] using h.clock
  · simpa [hw] using h.finished
  · simpa using h.count

lemma accounting_visit {g : Graph} {a b : Pure.State} {u l : Int}
    (hu : Vertex g u) (hw : a.arrays 0 u = 0)
    (h : Accounting g (enter a u l) b) : Accounting g a (leave b u) := by
  have bu : b.arrays 0 u = 1 := by
    have he := progress_nonwhite h.progress (v := u) (by simp)
    simpa using he
  have we := weight_enter (fun _ => 1) a u l hu hw
  have wl := weight_leave (g := g) (fun _ => 1) b u (by omega)
  change whites g (enter a u l) + 1 = whites g a at we
  change whites g (leave b u) = whites g b at wl
  refine ⟨?_,?_,?_,by simpa using h.count⟩
  · intro v
    by_cases hv : v = u
    · exact Or.inr ⟨by simpa [hv] using hw,by simp [hv]⟩
    · simpa [hv] using h.progress v
  · simp only [leave_clock, wl]
    have hc := h.clock
    simp only [enter_clock] at hc
    omega
  · simp only [leave_finished, wl]
    have hf := h.finished
    simp only [enter_finished] at hf
    omega


-- Strong induction on the number of white vertices, with an inner list induction
-- for scanning, gives finite recursion without assuming an external fuel bound.
theorem visit_exists (g : Graph) (a : Pure.State) (u label : Int)
    (hu : Vertex g u) (hw : a.arrays 0 u = 0) :
    ∃ b k, Eval g (.visit u label) a b k ∧ Accounting g a b ∧
      b.arrays 0 u = 2 ∧ k + potential g b + 1 = potential g a := by
  generalize he : whites g a = n
  induction n using Nat.strong_induction_on generalizing a u label with
  | h n ih =>
    have scan : ∀ (vs : List Nat) (s : Pure.State) (source tag : Int),
        whites g s < n → (∀ v ∈ vs, v < g.size) →
        ∃ t k, Eval g (.scan source tag vs) s t k ∧ Accounting g s t ∧
          k + potential g t = potential g s + 2 * vs.length := by
      intro vs
      induction vs with
      | nil =>
        intro s source tag hn _
        exact ⟨s,0,.scan_nil _ _ _,accounting_refl _ _,by simp⟩
      | cons v vs tail =>
        intro s source tag hn valid
        have hv : Vertex g (v : Int) := ⟨by omega,by exact_mod_cast valid v (by simp)⟩
        have tailvalid : ∀ w ∈ vs, w < g.size := fun w h => valid w (by simp [h])
        by_cases fresh : s.arrays 0 (v : Int) = 0
        · let sp := write s 1 (v : Int) source
          have wp : whites g sp = whites g s := weight_write_parent _ _ _ _ _
          have mp : potential g sp = potential g s := weight_write_parent _ _ _ _ _
          obtain ⟨b,j,call,ab,black,cost⟩ := ih (whites g sp) (by omega) sp (v : Int) tag
            hv (by simpa [sp] using fresh) rfl
          have asb : Accounting g s b := accounting_parent ab
          have wn := progress_whites (g := g) asb.progress
          obtain ⟨c,k,rest,bc,remaining⟩ := tail b source tag (by omega) tailvalid
          refine ⟨c,j+k+3,.scan_fresh fresh call rest,accounting_trans asb bc,?_⟩
          simp only [List.length_cons]
          omega
        · obtain ⟨b,k,rest,ab,cost⟩ := tail s source tag hn tailvalid
          refine ⟨b,k+2,.scan_seen fresh rest,ab,?_⟩
          simp only [List.length_cons]
          omega
    have went := weight_enter (fun _ => 1) a u label hu hw
    change whites g (enter a u label) + 1 = whites g a at went
    have huNat : u.toNat < g.size := by have := hu.1; have := hu.2; omega
    obtain ⟨b,k,call,ab,cost⟩ := scan (g.neighbors u.toNat) (enter a u label) u label
      (by omega) (g.bounded _ huNat)
    have bu : b.arrays 0 u = 1 := by
      have := progress_nonwhite ab.progress (v := u) (by simp)
      simpa using this
    have wl := weight_leave (g := g) (fun v => 4+2*(g.neighbors v).length) b u (by omega)
    have we := weight_enter (fun v => 4+2*(g.neighbors v).length) a u label hu hw
    change potential g (leave b u) = potential g b at wl
    change potential g (enter a u label) + (4+2*(g.neighbors u.toNat).length) =
      potential g a at we
    exact ⟨leave b u,k+3,.visit hu call,accounting_visit hu hw ab,by simp,by omega⟩

structure RootAccounting (g : Graph) (a b : Pure.State) : Prop where
  progress : Progress a b
  clock : b.clock + 2 * (whites g b : Int) = a.clock + 2 * (whites g a : Int)
  finished : b.finished + (whites g b : Int) = a.finished + (whites g a : Int)
  countLower : a.count ≤ b.count
  countUpper : b.count + (whites g b : Int) ≤ a.count + (whites g a : Int)

theorem roots_exists (g : Graph) (values : List Int) (a : Pure.State)
    (valid : ∀ v ∈ values, Vertex g v) :
    ∃ b k, Eval g (.roots values) a b k ∧ RootAccounting g a b ∧
      (∀ v ∈ values, b.arrays 0 v ≠ 0) ∧
      k + potential g b = potential g a + 2 * values.length := by
  induction values generalizing a with
  | nil =>
    exact ⟨a,0,.roots_nil _,⟨progress_refl _,rfl,rfl,le_refl _,le_refl _⟩,
      by simp,by simp⟩
  | cons u us ih =>
    have vu := valid u (by simp)
    have tailvalid : ∀ v ∈ us, Vertex g v := fun v hv => valid v (by simp [hv])
    by_cases fresh : a.arrays 0 u = 0
    · obtain ⟨b,j,call,ab,black,cost⟩ := visit_exists g a u a.count vu fresh
      let bn := nextTree b
      have bnw : whites g bn = whites g b := rfl
      have bnp : potential g bn = potential g b := rfl
      obtain ⟨c,k,rest,bc,seen,remaining⟩ := ih bn tailvalid
      have wc : whites g b + 1 ≤ whites g a := by
        -- Use the strict white-count decrease forced by the black root.
        have hpoint : ∀ v ∈ Finset.range g.size,
            (if b.arrays 0 (v : Int) = 0 then 1 else 0) ≤
            (if (enter a u a.count).arrays 0 (v : Int) = 0 then 1 else 0) := by
          intro v hv
          by_cases hvu : (v : Int) = u
          · simp [hvu,black]
          · simp only [enter_color,if_neg hvu]
            rcases ab.progress (v : Int) with h | ⟨ha,hb⟩
            · simp [h]
            · simp [ha,hb]
        have bound := Finset.sum_le_sum hpoint
        have we := weight_enter (fun _ => 1) a u a.count vu fresh
        change whites g b ≤ whites g (enter a u a.count) at bound
        change whites g (enter a u a.count) + 1 = whites g a at we
        omega
      have cnonwhite : c.arrays 0 u = 2 := by
        have hbn : bn.arrays 0 u = 2 := black
        exact (progress_nonwhite bc.progress (by rw [hbn]; omega)).trans hbn
      refine ⟨c,j+k+3,.roots_fresh fresh call rest,?_,?_,?_⟩
      · refine ⟨progress_trans ab.progress bc.progress,?_,?_,?_,?_⟩
        · have h1 := ab.clock; have h2 := bc.clock
          change c.clock + 2*(whites g c : Int) = b.clock + 2*(whites g b : Int) at h2
          omega
        · have h1 := ab.finished; have h2 := bc.finished
          change c.finished + (whites g c : Int) = b.finished + (whites g b : Int) at h2
          omega
        · have h1 := ab.count; have h2 := bc.countLower
          change b.count + 1 ≤ c.count at h2
          omega
        · have h1 := ab.count; have h2 := bc.countUpper
          change c.count + (whites g c : Int) ≤ b.count + 1 + (whites g b : Int) at h2
          omega
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · omega
        · exact seen v hv
      · simp only [List.length_cons]
        omega
    · obtain ⟨b,k,rest,ab,seen,cost⟩ := ih a tailvalid
      refine ⟨b,k+2,.roots_seen fresh rest,ab,?_,?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · rw [progress_nonwhite ab.progress fresh]; exact fresh
        · exact seen v hv
      · simp only [List.length_cons]
        omega


lemma initial_whites (g : Graph) : whites g initial = g.size := by
  simp [whites, whiteWeight, initial]

lemma initial_potential (g : Graph) : potential g initial = 4 * g.size + 2 * edgeCount g := by
  have range : (List.range g.size).toFinset = Finset.range g.size := by
    ext v; simp
  have edge : (∑ v ∈ Finset.range g.size, (g.neighbors v).length) = edgeCount g := by
    simpa only [range, edgeCount] using List.sum_toFinset (fun v => (g.neighbors v).length) (List.nodup_range (n := g.size))
  simp only [potential, whiteWeight, initial, Fin.reduceEq, true_or, if_pos]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul,
    ← Finset.mul_sum, edge]
  omega

theorem complete_execution (g : Graph) (values : List Int)
    (permutation : values.Perm ((List.range g.size).map Int.ofNat)) :
    ∃ (a : Pure.State) (k : Nat),
      Eval g (.roots values) initial a k ∧
      a.clock = 2 * (g.size : Int) ∧ a.finished = (g.size : Int) ∧
      (∀ v : Int, Vertex g v → a.arrays 0 v = 2) ∧
      (∃ count : Nat, a.count = (count : Int) ∧ count ≤ g.size) ∧
      k = 6 * g.size + 2 * edgeCount g := by
  have valid : ∀ v ∈ values, Vertex g v := by
    intro v hv
    have hm := permutation.mem_iff.mp hv
    rcases List.mem_map.mp hm with ⟨u,hu,rfl⟩
    simp only [List.mem_range] at hu
    change Vertex g (u : Int)
    exact ⟨by omega,by exact_mod_cast hu⟩
  obtain ⟨a,k,call,account,seen,cost⟩ := roots_exists g values initial valid
  have nonwhite : ∀ v : Int, Vertex g v → a.arrays 0 v ≠ 0 := by
    intro v hv
    apply seen
    apply permutation.mem_iff.mpr
    apply List.mem_map.mpr
    refine ⟨v.toNat,?_,Int.toNat_of_nonneg hv.1⟩
    have h0 := hv.1; have hn := hv.2
    simp only [List.mem_range]; omega
  have black : ∀ v : Int, Vertex g v → a.arrays 0 v = 2 := by
    intro v hv
    rcases account.progress v with h | h
    · exact (nonwhite v hv (by simpa [initial] using h)).elim
    · exact h.2
  have finalW : whites g a = 0 := by
    unfold whites whiteWeight
    apply Finset.sum_eq_zero
    intro v hv
    have vv : Vertex g (v : Int) := ⟨by omega,by exact_mod_cast Finset.mem_range.mp hv⟩
    simp [black (v : Int) vv]
  have finalP : potential g a = 0 := by
    unfold potential whiteWeight
    apply Finset.sum_eq_zero
    intro v hv
    have vv : Vertex g (v : Int) := ⟨by omega,by exact_mod_cast Finset.mem_range.mp hv⟩
    simp [black (v : Int) vv]
  have clock := account.clock
  have finished := account.finished
  have countLower := account.countLower
  have countUpper := account.countUpper
  rw [finalW, initial_whites] at clock finished
  simp only [Nat.cast_zero, mul_zero, add_zero, initial, zero_add] at clock finished
  change 0 ≤ a.count at countLower
  rw [finalW, initial_whites] at countUpper
  simp only [Nat.cast_zero, add_zero, initial, zero_add] at countUpper
  have len : values.length = g.size := by simpa using permutation.length_eq
  refine ⟨a,k,call,clock,finished,black,⟨a.count.toNat,?_,?_⟩,?_⟩
  · exact (Int.toNat_of_nonneg countLower).symm
  · omega
  · rw [finalP, initial_potential] at cost
    omega

end DFSTermination

theorem solution (g : Graph) (input : Seq) (values : List Int)
    (permutation : values.Perm ((List.range g.size).map Int.ofNat))
    (observed : ∀ i : Nat, i < g.size → input i = values[i]!) :
    ∃ (a : Pure.State) (k : Nat),
      Eval g (.roots values) initial a k ∧ Completed g input a ∧
      k ≤ 6 * g.size + 2 * edgeCount g := by
  obtain ⟨a,k,call,clock,finished,black,⟨count,hcount,bound⟩,cost⟩ :=
    DFSTermination.complete_execution g values permutation
  have cert := CLRS.DFS.local_certificate_of_execution g input values permutation observed a k call
  have cn : a.count.toNat = count := by omega
  rw [cn] at cert
  exact ⟨a,k,call,⟨clock,finished,black,count,hcount,bound,cert⟩,cost.le⟩
