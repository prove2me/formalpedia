-- Prove2me | solution 1 for FasterDistributedMatching.ApproximateMatching.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T22:07:10.75213+00:00
-- url     : https://prove2.me/submissions/3237ca9a-3d73-475c-bb54-a3aae70b5598

import Theorems.Thm_FasterDistributedMatching_ApproximateMatching_lemma_2_1
import Theorems.Thm_FasterDistributedMatching_ApproximateMatching_lemma_3_2
import Theorems.Thm_FasterDistributedMatching_ApproximateMatching_lemma_3_3
import Theorems.Thm_FasterDistributedMatching_ApproximateMatching_lemma_3_5
import Theorems.Thm_FasterDistributedMatching_ApproximateMatching_lemma_3_6
import Theorems.Thm_FasterDistributedMatching_ApproximateMatching_lemma_3_7
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Local
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_StageData
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Basic
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Routing
import Theorems.Thm_Timetabling85_ClassTeacher_prop_2_1
import Theorems.Thm_FasterDistributedMatching_ApproximateMatching_bounded_degree_bipartite_maximal_matching
import Mathlib.NumberTheory.Bertrand

-- Solutions/Sol_local_sequence.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace LocalSequence

structure State (K I L R : Type) where
  parameters : K
  ownID : ℕ
  original : I
  elapsed : ℕ
  left : L
  right : R

section Sequence
variable {K I O J P : Type}
    (A : Deterministic K I O) (B : Deterministic K J P)
    (prepare : K → ℕ → I → O → J)

def rightInitial (k : K) (id : ℕ) (inp : I) : B.program.State :=
  B.program.init k id (prepare k id inp (A.program.out (A.program.init k id inp (fun _ => false)))) (fun _ => false)

def sequence : Deterministic K I P where
  program := {
    State := State K I A.program.State B.program.State
    Msg := A.program.Msg × B.program.Msg
    rounds := fun k => A.program.rounds k+1+B.program.rounds k
    init := fun k id inp _ => ⟨k,id,inp,0,A.program.init k id inp (fun _ => false),rightInitial A B prepare k id inp⟩
    send := fun st => (A.program.send st.left,B.program.send st.right)
    step := fun st msgs =>
      if st.elapsed < A.program.rounds st.parameters then
        {st with elapsed := st.elapsed+1,left := A.program.step st.left (msgs.map Prod.fst)}
      else if st.elapsed = A.program.rounds st.parameters then
        {st with elapsed := st.elapsed+1,right := B.program.init st.parameters st.ownID (prepare st.parameters st.ownID st.original (A.program.out st.left)) (fun _ => false)}
      else {st with elapsed := st.elapsed+1,right := B.program.step st.right (msgs.map Prod.snd)}
    out := fun st => B.program.out st.right }
  tape_independent := by intros; rfl

variable {V : Type} [Fintype V] (H : SimpleGraph V) (k : K) (ids : V → ℕ) (inp : V → I)

lemma run_left (t : ℕ) (ht : t ≤ A.program.rounds k) : ∀ v,
    (sequence A B prepare).program.run H k ids inp (fun _ _ => false) t v =
      ⟨k,ids v,inp v,t,A.program.run H k ids inp (fun _ _ => false) t v,rightInitial A B prepare k (ids v) (inp v)⟩ := by
  induction t with
  | zero => intro v; rfl
  | succ t ih =>
    intro v
    have htt : t < A.program.rounds k := by omega
    have hi := ih (by omega)
    conv_lhs => rw [SmoothedMIS.LocalAlg.run]
    simp only [hi]
    dsimp only [sequence]
    rw [if_pos htt]
    simp only [SmoothedMIS.LocalAlg.run,Multiset.map_map,Function.comp_def]

abbrev nextInput : V → J := fun v => prepare k (ids v) (inp v)
  (A.program.output H k ids inp (fun _ _ => false) v)

lemma run_right (t : ℕ) : ∀ v,
    (sequence A B prepare).program.run H k ids inp (fun _ _ => false) (A.program.rounds k+1+t) v =
      ⟨k,ids v,inp v,A.program.rounds k+1+t,
        A.program.run H k ids inp (fun _ _ => false) (A.program.rounds k) v,
        B.program.run H k ids (nextInput A prepare H k ids inp) (fun _ _ => false) t v⟩ := by
  induction t with
  | zero =>
    intro v
    simp only [Nat.add_zero]
    conv_lhs => rw [SmoothedMIS.LocalAlg.run]
    simp only [run_left A B prepare H k ids inp _ le_rfl]
    dsimp only [sequence]
    simp only [lt_self_iff_false,ite_false,ite_true]
    rfl
  | succ t ih =>
    intro v
    rw [show A.program.rounds k+1+(t+1) = (A.program.rounds k+1+t)+1 by omega,SmoothedMIS.LocalAlg.run]
    simp only [ih]
    dsimp only [sequence]
    have hlt : ¬(A.program.rounds k+1+t < A.program.rounds k) := by omega
    have heq : ¬(A.program.rounds k+1+t = A.program.rounds k) := by omega
    simp only [if_neg hlt,if_neg heq]
    simp only [SmoothedMIS.LocalAlg.run,Multiset.map_map,Function.comp_def]

lemma sequence_output (v : V) :
    (sequence A B prepare).program.output H k ids inp (fun _ _ => false) v =
      B.program.output H k ids (nextInput A prepare H k ids inp) (fun _ _ => false) v := by
  unfold SmoothedMIS.LocalAlg.output
  change B.program.out ((sequence A B prepare).program.run H k ids inp (fun _ _ => false)
    (A.program.rounds k+1+B.program.rounds k) v).right = _
  rw [run_right]

end Sequence
end LocalSequence

-- Solutions/Sol_local_transform.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace LocalTransform

variable {K I O J P : Type}

def freeze (A : Deterministic K I O) (k : K) : Deterministic Unit I O where
  program := {
    State := A.program.State
    Msg := A.program.Msg
    rounds := fun _ => A.program.rounds k
    init := fun _ id inp _ => A.program.init k id inp (fun _ => false)
    send := A.program.send
    step := A.program.step
    out := A.program.out }
  tape_independent := by intros; rfl

lemma freeze_run (A : Deterministic K I O) (k : K) {V : Type} [Fintype V] (H : SimpleGraph V)
    (ids : V → ℕ) (inp : V → I) (t : ℕ) : ∀ v,
    (freeze A k).program.run H () ids inp (fun _ _ => false) t v =
      A.program.run H k ids inp (fun _ _ => false) t v := by
  induction t with
  | zero => intro v; rfl
  | succ t ih =>
    intro v
    rw [SmoothedMIS.LocalAlg.run,SmoothedMIS.LocalAlg.run]
    simp only [ih]
    rfl

lemma freeze_output (A : Deterministic K I O) (k : K) {V : Type} [Fintype V] (H : SimpleGraph V)
    (ids : V → ℕ) (inp : V → I) (v : V) :
    (freeze A k).program.output H () ids inp (fun _ _ => false) v =
      A.program.output H k ids inp (fun _ _ => false) v := by
  unfold SmoothedMIS.LocalAlg.output
  rw [freeze_run]
  rfl

def transform (A : Deterministic Unit J O) (pre : ℕ → I → J) (post : ℕ → I → O → P) : Deterministic Unit I P where
  program := {
    State := ℕ × I × A.program.State
    Msg := A.program.Msg
    rounds := A.program.rounds
    init := fun _ id inp _ => (id,inp,A.program.init () id (pre id inp) (fun _ => false))
    send := fun st => A.program.send st.2.2
    step := fun st msgs => (st.1,st.2.1,A.program.step st.2.2 msgs)
    out := fun st => post st.1 st.2.1 (A.program.out st.2.2) }
  tape_independent := by intros; rfl

lemma transform_run (A : Deterministic Unit J O) (pre : ℕ → I → J) (post : ℕ → I → O → P)
    {V : Type} [Fintype V] (H : SimpleGraph V) (ids : V → ℕ) (inp : V → I) (t : ℕ) : ∀ v,
    (transform A pre post).program.run H () ids inp (fun _ _ => false) t v =
      (ids v,inp v,A.program.run H () ids (fun v => pre (ids v) (inp v)) (fun _ _ => false) t v) := by
  induction t with
  | zero => intro v; rfl
  | succ t ih =>
    intro v
    rw [SmoothedMIS.LocalAlg.run,SmoothedMIS.LocalAlg.run]
    simp only [ih]
    rfl

lemma transform_output (A : Deterministic Unit J O) (pre : ℕ → I → J) (post : ℕ → I → O → P)
    {V : Type} [Fintype V] (H : SimpleGraph V) (ids : V → ℕ) (inp : V → I) (v : V) :
    (transform A pre post).program.output H () ids inp (fun _ _ => false) v =
      post (ids v) (inp v) (A.program.output H () ids (fun v => pre (ids v) (inp v)) (fun _ _ => false) v) := by
  unfold SmoothedMIS.LocalAlg.output
  rw [transform_run]
  rfl

def pointwise (f : ℕ → I → O) : Deterministic Unit I O where
  program := {
    State := O
    Msg := Unit
    rounds := fun _ => 0
    init := fun _ id inp _ => f id inp
    send := fun _ => ()
    step := fun st _ => st
    out := id }
  tape_independent := by intros; rfl

lemma local_output (f : ℕ → I → O) {V : Type} [Fintype V] (H : SimpleGraph V)
    (ids : V → ℕ) (inp : V → I) (v : V) :
    (pointwise f).program.output H () ids inp (fun _ _ => false) v = f (ids v) (inp v) := rfl

end LocalTransform

-- Solutions/Sol_local_family.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace LocalFamily
section Family
variable {K I O : Type} (F : K → Deterministic Unit I O)

abbrev FamilyState := Σ k : K, (F k).program.State
abbrev FamilyMessage := Σ k : K, (F k).program.Msg

def unpack (k : K) (msg : FamilyMessage F) : Option (F k).program.Msg :=
  if h : msg.1 = k then some (h ▸ msg.2) else none

lemma unpack_same (k : K) (msg : (F k).program.Msg) : unpack F k ⟨k,msg⟩ = some msg := by
  unfold unpack
  rw [dif_pos rfl]

def select : Deterministic K I O where
  program := {
    State := FamilyState F
    Msg := FamilyMessage F
    rounds := fun k => (F k).program.rounds ()
    init := fun k id inp _ => ⟨k,(F k).program.init () id inp (fun _ => false)⟩
    send := fun st => ⟨st.1,(F st.1).program.send st.2⟩
    step := fun st msgs => ⟨st.1,(F st.1).program.step st.2 (msgs.filterMap (unpack F st.1))⟩
    out := fun st => (F st.1).program.out st.2 }
  tape_independent := by intros; rfl

lemma select_run {V : Type} [Fintype V] (H : SimpleGraph V) (k : K) (ids : V → ℕ)
    (inp : V → I) (t : ℕ) : ∀ v,
    (select F).program.run H k ids inp (fun _ _ => false) t v =
      ⟨k,(F k).program.run H () ids inp (fun _ _ => false) t v⟩ := by
  induction t with
  | zero => intro v; rfl
  | succ t ih =>
    intro v
    rw [SmoothedMIS.LocalAlg.run]
    simp only [ih]
    change (⟨k,(F k).program.step ((F k).program.run H () ids inp (fun _ _ => false) t v)
      (((univ.filter (H.Adj v)).val.map (fun w =>
        (⟨k,(F k).program.send ((F k).program.run H () ids inp (fun _ _ => false) t w)⟩ : FamilyMessage F))).filterMap (unpack F k))⟩ : FamilyState F) = _
    rw [Multiset.filterMap_map]
    simp only [Function.comp_def,unpack_same]
    rw [show (fun x => some ((F k).program.send ((F k).program.run H () ids inp (fun _ _ => false) t x))) =
      some ∘ (fun x => (F k).program.send ((F k).program.run H () ids inp (fun _ _ => false) t x)) from rfl,
      ←Multiset.filterMap_map,Multiset.filterMap_some]
    rfl

lemma select_output {V : Type} [Fintype V] (H : SimpleGraph V) (k : K) (ids : V → ℕ)
    (inp : V → I) (v : V) :
    (select F).program.output H k ids inp (fun _ _ => false) v =
      (F k).program.output H () ids inp (fun _ _ => false) v := by
  unfold SmoothedMIS.LocalAlg.output
  change (select F).program.out ((select F).program.run H k ids inp (fun _ _ => false) ((F k).program.rounds ()) v) = _
  rw [select_run]
  rfl

end Family
end LocalFamily

-- Solutions/Sol_local_repeat.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace LocalRepeat
variable {I : Type} (A : ℕ → Deterministic Unit I I)

def programs : ℕ → Deterministic Unit I I
  | 0 => LocalTransform.pointwise (fun _ inp => inp)
  | n+1 => LocalSequence.sequence (programs n) (A n) (fun _ _ _ out => out)

def configurations {V : Type} [Fintype V] (H : SimpleGraph V) (ids : V → ℕ) (inp : V → I) : ℕ → V → I
  | 0 => inp
  | n+1 => (A n).program.output H () ids (configurations H ids inp n) (fun _ _ => false)

lemma repeat_output {V : Type} [Fintype V] (H : SimpleGraph V) (ids : V → ℕ) (inp : V → I) (n : ℕ) : ∀ v,
    (programs A n).program.output H () ids inp (fun _ _ => false) v = configurations A H ids inp n v := by
  induction n with
  | zero => intro v; rfl
  | succ n ih =>
    intro v
    change (LocalSequence.sequence (programs A n) (A n) (fun _ _ _ out => out)).program.output H () ids inp (fun _ _ => false) v = _
    rw [LocalSequence.sequence_output]
    change (A n).program.output H () ids (fun v => (programs A n).program.output H () ids inp (fun _ _ => false) v) (fun _ _ => false) v = _
    simp only [ih]
    rfl

lemma repeat_rounds (n : ℕ) : (programs A n).program.rounds () = n+∑ t ∈ range n, (A t).program.rounds () := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (programs A n).program.rounds ()+1+(A n).program.rounds () = _
    rw [ih,sum_range_succ]
    omega

end LocalRepeat

-- Solutions/Sol_local_weight_input.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace LocalWeights

def mask (neighbors : Finset ℕ) (values : ℕ → ℝ) (j : ℕ) : ℝ := if j ∈ neighbors then values j else 0

lemma mask_eq_weight {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (hi : Function.Injective ids)
    (x : Sym2 (Fin N) → ℝ) (out : Fin N → ℕ → ℝ) (hout : ReportsWeights G ids out x) (v : Fin N) :
    mask (neighborIDs G ids v) (out v) = (weightInput G ids x v).2 := by
  funext j
  unfold mask
  by_cases hj : j ∈ neighborIDs G ids v
  · rw [if_pos hj]
    obtain ⟨u,hu,huj⟩ := mem_image.mp hj
    have huv := (SimpleGraph.mem_neighborFinset G v u).mp hu
    rw [←huj,(hout.2 v u huv).1]
    change x s(v,u) = ∑ w ∈ G.neighborFinset v, if ids w = ids u then x s(v,w) else 0
    symm
    rw [sum_eq_single u]
    · rw [if_pos rfl]
    · intro w hw hwu
      rw [if_neg (fun h => hwu (hi h))]
    · exact fun h => (h hu).elim
  · rw [if_neg hj]
    change 0 = ∑ w ∈ G.neighborFinset v, if ids w = j then x s(v,w) else 0
    symm
    apply sum_eq_zero
    intro w hw
    exact if_neg (fun h => hj (mem_image.mpr ⟨w,hw,h⟩))

lemma masked_reports {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
    (x : Sym2 (Fin N) → ℝ) (out : Fin N → ℕ → ℝ) (hout : ReportsWeights G ids out x) :
    ReportsWeights G ids (fun v => mask (neighborIDs G ids v) (out v)) x := by
  refine ⟨hout.1,?_⟩
  intro u v huv
  have hv : ids v ∈ neighborIDs G ids u := mem_image.mpr ⟨v,(SimpleGraph.mem_neighborFinset G u v).mpr huv,rfl⟩
  have hu : ids u ∈ neighborIDs G ids v := mem_image.mpr ⟨u,(SimpleGraph.mem_neighborFinset G v u).mpr huv.symm,rfl⟩
  exact ⟨(if_pos hv).trans (hout.2 u v huv).1,(if_pos hu).trans (hout.2 u v huv).2⟩

end LocalWeights

-- Solutions/Sol_local_pairing.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace LocalPairing
variable {V W : Type} [DecidableEq V] [DecidableEq W]

def pairs : List V → List (Finset V)
  | [] => []
  | [a] => [{a}]
  | a::b::rest => {a,b}::pairs rest

lemma pairs_map (f : V → W) (l : List V) :
    pairs (l.map f) = (pairs l).map (Finset.image f) := by
  fun_induction pairs l <;> simp_all [pairs]

lemma mem_pairs (l : List V) (v : V) :
    (∃ g ∈ pairs l, v ∈ g) ↔ v ∈ l := by
  fun_induction pairs l <;> simp_all [pairs,or_assoc]

lemma group_subset (l : List V) (g : Finset V) (hg : g ∈ pairs l) : ∀ v ∈ g, v ∈ l :=
  fun v hv => (mem_pairs l v).mp ⟨g,hg,hv⟩

lemma group_sizes (l : List V) (hn : l.Nodup) : ∀ g ∈ pairs l, g.card = 1 ∨ g.card = 2 := by
  fun_induction pairs l
  · simp [pairs]
  · simp [pairs]
  · rename_i a b rest ih
    have hab : a ≠ b := fun h => (List.nodup_cons.mp hn).1 (List.mem_cons.mpr (Or.inl h))
    have hrest : rest.Nodup := hn.of_cons.of_cons
    intro g hg
    rcases List.mem_cons.mp hg with rfl|hg
    · exact Or.inr (card_pair hab)
    · exact ih hrest g hg

lemma groups_disjoint (l : List V) (hn : l.Nodup) : (pairs l).Pairwise Disjoint := by
  fun_induction pairs l
  · simp [pairs]
  · simp [pairs]
  · rename_i a b rest ih
    have ha : a ∉ rest := fun h => (List.nodup_cons.mp hn).1 (List.mem_cons.mpr (Or.inr h))
    have hb : b ∉ rest := (List.nodup_cons.mp hn.of_cons).1
    have hrest : rest.Nodup := hn.of_cons.of_cons
    apply List.pairwise_cons.mpr
    constructor
    · intro g hg
      apply Finset.disjoint_left.mpr
      intro v hv hvg
      rcases mem_insert.mp hv with hva|hv
      · subst v
        exact ha (group_subset rest g hg a hvg)
      · have hvb : v = b := mem_singleton.mp hv
        exact hb (hvb ▸ group_subset rest g hg v hvg)
    · exact ih hrest

lemma singleton_pairwise (l : List V) (hn : l.Nodup) :
    (pairs l).Pairwise (fun g h => g.card ≠ 1 ∨ h.card ≠ 1) := by
  fun_induction pairs l
  · simp [pairs]
  · simp [pairs]
  · rename_i a b rest ih
    have hab : a ≠ b := fun h => (List.nodup_cons.mp hn).1 (List.mem_cons.mpr (Or.inl h))
    have hrest : rest.Nodup := hn.of_cons.of_cons
    apply List.pairwise_cons.mpr
    exact ⟨fun g _ => Or.inl (by rw [card_pair hab]; norm_num),ih hrest⟩

lemma disjoint_index_unique (L : List (Finset V)) (hL : L.Pairwise Disjoint)
    (i j : Fin L.length) (v : V) (hi : v ∈ L.get i) (hj : v ∈ L.get j) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt|hgt
  · exact Finset.disjoint_left.mp (hL.rel_get_of_lt hlt) hi hj
  · exact Finset.disjoint_left.mp (hL.rel_get_of_lt hgt) hj hi

lemma singleton_index_unique (L : List (Finset V))
    (hL : L.Pairwise (fun g h => g.card ≠ 1 ∨ h.card ≠ 1))
    (i j : Fin L.length) (hi : (L.get i).card = 1) (hj : (L.get j).card = 1) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt|hgt
  · exact (hL.rel_get_of_lt hlt).elim (fun h => h hi) (fun h => h hj)
  · exact (hL.rel_get_of_lt hgt).elim (fun h => h hj) (fun h => h hi)

lemma unique_group (l : List V) (hn : l.Nodup) (v : V) :
    v ∈ l ↔ ∃! i : Fin (pairs l).length, v ∈ (pairs l).get i := by
  constructor
  · intro hv
    obtain ⟨g,hg,hvg⟩ := (mem_pairs l v).mpr hv
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hg
    have hvi : v ∈ (pairs l).get i := by rw [hi]; exact hvg
    refine ⟨i,hvi,?_⟩
    intro j hj
    exact disjoint_index_unique _ (groups_disjoint l hn) j i v hj hvi
  · rintro ⟨i,hi,huniq⟩
    exact (mem_pairs l v).mp ⟨_,List.get_mem _ _,hi⟩

lemma singleton_bound (l : List V) (hn : l.Nodup) :
    ((univ : Finset (Fin (pairs l).length)).filter (fun i => ((pairs l).get i).card = 1)).card ≤ 1 := by
  apply card_le_one.mpr
  intro i hi j hj
  exact singleton_index_unique _ (singleton_pairwise l hn) i j (mem_filter.mp hi).2 (mem_filter.mp hj).2

end LocalPairing

-- Solutions/Sol_pairing_construction.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace LocalPairing
section Sorted
variable {V : Type} [DecidableEq V] (S : Finset V) (key : V → ℕ) (hi : Function.Injective key)

def sortedBy : List V := by
  letI := LinearOrder.lift' key hi
  exact S.sort

lemma sortedBy_nodup : (sortedBy S key hi).Nodup := by
  unfold sortedBy
  exact sort_nodup _ _

lemma mem_sortedBy (v : V) : v ∈ sortedBy S key hi ↔ v ∈ S := by
  unfold sortedBy
  exact Finset.mem_sort _

set_option backward.isDefEq.respectTransparency false in
lemma map_sortedBy : (sortedBy S key hi).map key = (S.image key).sort := by
  letI := LinearOrder.lift' key hi
  change S.sort.map key = (S.image key).sort
  have h := Finset.map_sort ⟨key,hi⟩ S (fun a b : V => a ≤ b) (fun a b : ℕ => a ≤ b)
    (fun _ _ _ _ => Iff.rfl)
  rw [Finset.map_eq_image] at h
  convert h using 1 <;> rfl

end Sorted

variable {N : ℕ} (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (ids : Fin N → ℕ) (hi : Function.Injective ids)

def active (v : Fin N) : Finset (Fin N) := (G.neighborFinset v).filter (fun w => x s(v,w) = q)

def pairing : Pairing N := fun v => pairs (sortedBy (active G x q v) ids hi)

lemma pairing_valid : ValidPairing G x q (pairing G x q ids hi) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro a
    exact group_sizes _ (sortedBy_nodup _ ids hi) (group _ a) (List.get_mem _ _)
  · intro v w
    have hmem : (G.Adj v w ∧ x s(v,w) = q) ↔ w ∈ sortedBy (active G x q v) ids hi := by
      rw [mem_sortedBy]
      simp only [active,mem_filter,SimpleGraph.mem_neighborFinset]
    exact hmem.trans (unique_group _ (sortedBy_nodup _ ids hi) w)
  · intro a w hw
    have hm := group_subset _ (group (pairing G x q ids hi) a) (List.get_mem _ _) w hw
    rw [mem_sortedBy] at hm
    exact ⟨(SimpleGraph.mem_neighborFinset G a.1 w).mp (mem_filter.mp hm).1,(mem_filter.mp hm).2⟩
  · intro v
    exact singleton_bound _ (sortedBy_nodup _ ids hi)

def localGroups (q : ℝ) (neighbors : Finset ℕ) (values : ℕ → ℝ) : List (Finset ℕ) :=
  pairs ((neighbors.filter (fun j => values j = q)).sort)

lemma localGroups_correct (out : Fin N → ℕ → ℝ) (hout : ReportsWeights G ids out x) (v : Fin N) :
    localGroups q (neighborIDs G ids v) (out v) = (pairing G x q ids hi v).map (image ids) := by
  have hactive : (neighborIDs G ids v).filter (fun j => out v j = q) = (active G x q v).image ids := by
    ext j
    constructor
    · intro hj
      obtain ⟨hjneigh,hjval⟩ := mem_filter.mp hj
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hjneigh
      have hAdj := (SimpleGraph.mem_neighborFinset G v w).mp hw
      rw [(hout.2 v w hAdj).1] at hjval
      exact mem_image.mpr ⟨w,mem_filter.mpr ⟨hw,hjval⟩,rfl⟩
    · intro hj
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hj
      have hAdj := (SimpleGraph.mem_neighborFinset G v w).mp (mem_filter.mp hw).1
      refine mem_filter.mpr ⟨mem_image.mpr ⟨w,(mem_filter.mp hw).1,rfl⟩,?_⟩
      rw [(hout.2 v w hAdj).1]
      exact (mem_filter.mp hw).2
  unfold localGroups pairing
  rw [hactive,←map_sortedBy _ ids hi,pairs_map]

end LocalPairing

-- Solutions/Sol_potential_change.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingRounding
section Potential
variable {N : ℕ} (G : SimpleGraph (Fin N))

lemma load_as_edges (x : Sym2 (Fin N) → ℝ) (v : Fin N) :
    load G x v = ∑ e ∈ G.edgeFinset, if v ∈ e then x e else 0 := by
  unfold load RandomOrderCRS.fracDegree
  rw [G.incidenceFinset_eq_filter]
  exact sum_filter ..

lemma load_sub (x y : Sym2 (Fin N) → ℝ) (v : Fin N) :
    load G (fun e => y e-x e) v = load G y v-load G x v := by
  unfold load RandomOrderCRS.fracDegree
  simp only [Finset.sum_sub_distrib]

def endpointSum (f : Fin N → ℝ) : Sym2 (Fin N) → ℝ :=
  Sym2.lift ⟨fun u v => f u+f v,by intro u v; exact add_comm _ _⟩

lemma endpointSum_apply (f : Fin N → ℝ) (u v : Fin N) : endpointSum f s(u,v) = f u+f v := rfl

lemma weighted_loads (d : Sym2 (Fin N) → ℝ) (f : Fin N → ℝ) :
    (∑ v, f v*load G d v) = ∑ e ∈ G.edgeFinset, endpointSum f e*d e := by
  simp_rw [load_as_edges,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  obtain ⟨⟨u,w⟩,rfl⟩ := e.exists_rep
  have huw : u ≠ w := (G.mem_edgeSet.mp (G.mem_edgeFinset.mp he)).ne
  have hi (v : Fin N) : f v*(if v ∈ s(u,w) then d s(u,w) else 0) =
      (if v = u then f u*d s(u,w) else 0)+(if v = w then f w*d s(u,w) else 0) := by
    simp only [Sym2.mem_iff]
    by_cases h1 : v = u <;> by_cases h2 : v = w <;> simp_all
  simp_rw [hi,sum_add_distrib]
  simp only [sum_ite_eq',mem_univ,ite_true,endpointSum_apply]
  ring

def linearCoefficient (x : Sym2 (Fin N) → ℝ) (e : Sym2 (Fin N)) : ℝ :=
  1-4*endpointSum (load G x) e

lemma linearCoefficient_apply (x : Sym2 (Fin N) → ℝ) (u v : Fin N) :
    linearCoefficient G x s(u,v) = 1-4*load G x u-4*load G x v := by
  unfold linearCoefficient
  rw [endpointSum_apply]
  ring

lemma potential_change (x y : Sym2 (Fin N) → ℝ) :
    potential G y-potential G x =
      (∑ e ∈ G.edgeFinset, linearCoefficient G x e*(y e-x e))-
        2*(∑ v, (load G y v-load G x v)^2) := by
  have hpen : penalty G y-penalty G x =
      4*(∑ v, load G x v*(load G y v-load G x v))+
        2*(∑ v, (load G y v-load G x v)^2) := by
    unfold penalty
    simp only [mul_sum,←sum_sub_distrib,←sum_add_distrib]
    apply sum_congr rfl
    intro v hv
    ring
  have hcross := weighted_loads G (fun e => y e-x e) (load G x)
  simp_rw [load_sub] at hcross
  have hlinear : (∑ e ∈ G.edgeFinset, linearCoefficient G x e*(y e-x e)) =
      totalWeight G y-totalWeight G x-4*(∑ v, load G x v*(load G y v-load G x v)) := by
    rw [hcross]
    unfold linearCoefficient totalWeight
    simp only [sub_mul,one_mul,mul_assoc,sum_sub_distrib,←mul_sum]
  unfold potential
  linarith

end Potential
end MatchingRounding

-- Solutions/Sol_matching_cover.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteRounding
variable {N : ℕ} (G : SimpleGraph (Fin N))

lemma endpoint_exists (e : Sym2 (Fin N)) : ∃ v, v ∈ e := by
  obtain ⟨⟨u,v⟩,rfl⟩ := e.exists_rep
  exact ⟨u,Sym2.mem_mk_left _ _⟩

lemma maximum_matching : ∃ M : Finset G.edgeSet, SemiStreamMWM.IsMatching G M ∧ M.card = optimum G := by
  have hempty : (∅ : Finset G.edgeSet) ∈ SemiStreamMWM.matchings G := by
    simp [SemiStreamMWM.matchings,SemiStreamMWM.IsMatching]
  obtain ⟨M,hM,hcard⟩ := exists_mem_eq_sup (SemiStreamMWM.matchings G) ⟨∅,hempty⟩ Finset.card
  exact ⟨M,(mem_filter.mp hM).2,hcard.symm⟩

lemma maximum_covers (M : Finset G.edgeSet) (hM : SemiStreamMWM.IsMatching G M) (hcard : M.card = optimum G)
    (e : G.edgeSet) : ∃ f ∈ M, ∃ v, v ∈ e.val ∧ v ∈ f.val := by
  by_contra hcover
  have hdisj : ∀ f ∈ M, ∀ v ∈ e.val, v ∉ f.val := by
    intro f hf v hve hvf
    exact hcover ⟨f,hf,v,hve,hvf⟩
  have heM : e ∉ M := by
    intro he
    obtain ⟨v,hv⟩ := endpoint_exists e.val
    exact hdisj e he v hv hv
  have hins : SemiStreamMWM.IsMatching G (insert e M) := by
    intro a ha b hb hab v hva
    rcases mem_insert.mp ha with hae|haM
    · subst a
      rcases mem_insert.mp hb with hbe|hbM
      · exact (hab hbe.symm).elim
      · exact hdisj b hbM v hva
    · rcases mem_insert.mp hb with hbe|hbM
      · subst b
        intro hve
        exact hdisj a haM v hve hva
      · exact hM a haM b hbM hab v hva
  have hle : (insert e M).card ≤ optimum G := by
    exact le_sup (f:=Finset.card) (mem_filter.mpr ⟨mem_univ _,hins⟩)
  rw [card_insert_of_notMem heM,hcard] at hle
  omega

lemma weight_vertex_cover (x : Sym2 (Fin N) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (S : Finset (Fin N)) (hcover : ∀ e ∈ G.edgeSet, ∃ v ∈ S, v ∈ e) :
    totalWeight G x ≤ ∑ v ∈ S, load G x v := by
  simp_rw [MatchingRounding.load_as_edges]
  rw [sum_comm]
  apply sum_le_sum
  intro e he
  obtain ⟨v,hv,hve⟩ := hcover e (G.mem_edgeFinset.mp he)
  calc
    x e = (if v ∈ e then x e else 0) := (if_pos hve).symm
    _ ≤ ∑ u ∈ S, if u ∈ e then x e else 0 :=
      single_le_sum (f:=fun u => if u ∈ e then x e else 0) (fun u _ => by split_ifs <;> simp_all) hv

lemma halfload_weight_bound (x : Sym2 (Fin N) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hload : ∀ v, load G x v ≤ 1/2) : totalWeight G x ≤ (optimum G : ℝ) := by
  obtain ⟨M,hM,hcard⟩ := maximum_matching G
  let S : Finset (Fin N) := M.biUnion (fun e => e.val.toFinset)
  have hc : ∀ e ∈ G.edgeSet, ∃ v ∈ S, v ∈ e := by
    intro e he
    obtain ⟨f,hf,v,hve,hvf⟩ := maximum_covers G M hM hcard ⟨e,he⟩
    exact ⟨v,mem_biUnion.mpr ⟨f,hf,Sym2.mem_toFinset.mpr hvf⟩,hve⟩
  have hs : S.card ≤ 2*M.card := by
    calc
      S.card ≤ ∑ e ∈ M, e.val.toFinset.card := card_biUnion_le
      _ ≤ ∑ _ ∈ M, (2:ℕ) := sum_le_sum (fun e _ => by rw [Sym2.card_toFinset]; split_ifs <;> omega)
      _ = 2*M.card := by simp [mul_comm]
  have hscast : (S.card : ℝ) ≤ 2*(M.card : ℝ) := by exact_mod_cast hs
  have hw := weight_vertex_cover G x hx S hc
  have hl : (∑ v ∈ S, load G x v) ≤ (S.card : ℝ)/2 := by
    calc
      _ ≤ ∑ _ ∈ S, (1/2:ℝ) := sum_le_sum (fun v _ => hload v)
      _ = _ := by simp [div_eq_mul_inv]
  rw [hcard] at hscast
  linarith

lemma sum_loads (x : Sym2 (Fin N) → ℝ) : (∑ v, load G x v) = 2*totalWeight G x := by
  have h := MatchingRounding.weighted_loads G x (fun _ => 1)
  simp only [one_mul] at h
  have he (e : Sym2 (Fin N)) : MatchingRounding.endpointSum (fun _ : Fin N => (1:ℝ)) e = 2 := by
    obtain ⟨⟨u,v⟩,rfl⟩ := e.exists_rep
    change MatchingRounding.endpointSum (fun _ : Fin N => (1:ℝ)) s(u,v) = 2
    rw [MatchingRounding.endpointSum_apply]
    norm_num
  simp_rw [he] at h
  exact h.trans (mul_sum ..).symm

lemma halfload_penalty_bound (x : Sym2 (Fin N) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hload : ∀ v, load G x v ≤ 1/2) : penalty G x ≤ 2*totalWeight G x := by
  rw [←sum_loads G x]
  unfold penalty
  rw [mul_sum]
  apply sum_le_sum
  intro v _
  have hn : 0 ≤ load G x v := by
    unfold load RandomOrderCRS.fracDegree
    exact sum_nonneg (fun e _ => hx e)
  nlinarith [hload v]

end BipartiteRounding

-- Solutions/Sol_dyadic_rounding.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteRounding

def quantum (i : ℕ) : ℝ := 1/(2:ℝ)^i

lemma quantum_pos (i : ℕ) : 0 < quantum i := by unfold quantum; positivity
lemma quantum_succ (i : ℕ) : quantum i = 2*quantum (i+1) := by unfold quantum; rw [pow_succ]; field_simp

lemma quantum_antitone : Antitone quantum := by
  apply antitone_nat_of_succ_le
  intro i
  have h := quantum_succ i
  linarith [quantum_pos (i+1)]

def dyadicIndex (K : ℕ) (r : ℝ) : ℕ :=
  if h : ∃ i, i ≤ K ∧ quantum i ≤ r then Nat.find h else 0

lemma dyadicIndex_spec (K : ℕ) (r : ℝ) (hr : quantum K ≤ r) (hupper : r ≤ 1) :
    dyadicIndex K r ≤ K ∧ quantum (dyadicIndex K r) ≤ r ∧ r ≤ 2*quantum (dyadicIndex K r) := by
  let h : ∃ i, i ≤ K ∧ quantum i ≤ r := ⟨K,le_rfl,hr⟩
  unfold dyadicIndex
  rw [dif_pos h]
  refine ⟨(Nat.find_spec h).1,(Nat.find_spec h).2,?_⟩
  cases hidx : Nat.find h with
  | zero => simpa only [quantum,pow_zero,div_one,mul_one] using (show r ≤ (2:ℝ) by linarith)
  | succ i =>
    have hbad : ¬(i ≤ K ∧ quantum i ≤ r) := Nat.find_min h (by omega)
    have hiK : i ≤ K := by have hk := (Nat.find_spec h).1; omega
    have hlt : r < quantum i := lt_of_not_ge (fun hh => hbad ⟨hiK,hh⟩)
    rw [←quantum_succ i]
    exact hlt.le

variable {N : ℕ} (G : SimpleGraph (Fin N))

def scaledDyadic (K : ℕ) (f : Sym2 (Fin N) → ℝ) (e : Sym2 (Fin N)) : ℝ :=
  if e ∈ G.edgeSet then quantum (dyadicIndex K (f e)+3) else 0

lemma scaledDyadic_bounds (K : ℕ) (f : Sym2 (Fin N) → ℝ) (hf : fractional G f)
    (hlower : ∀ e ∈ G.edgeSet, quantum K ≤ f e) (e : Sym2 (Fin N)) :
    f e/16 ≤ scaledDyadic G K f e ∧ scaledDyadic G K f e ≤ f e/8 := by
  by_cases he : e ∈ G.edgeSet
  · rw [scaledDyadic,if_pos he]
    have hh := dyadicIndex_spec K (f e) (hlower e he) (hf.1 e).2
    have hscale : quantum (dyadicIndex K (f e)+3) = quantum (dyadicIndex K (f e))/8 := by
      unfold quantum
      rw [pow_add]
      norm_num
      ring
    rw [hscale]
    constructor <;> linarith [hh.2.1,hh.2.2]
  · rw [scaledDyadic,if_neg he,hf.2.1 e he]
    norm_num

lemma scaledDyadic_nonnegative (K : ℕ) (f : Sym2 (Fin N) → ℝ) :
    NonnegativeAssignment G (scaledDyadic G K f) := by
  constructor
  · intro e
    unfold scaledDyadic
    split_ifs <;> linarith [quantum_pos (dyadicIndex K (f e)+3)]
  · intro e he
    exact if_neg he

lemma scaledDyadic_load (K : ℕ) (f : Sym2 (Fin N) → ℝ) (hf : fractional G f)
    (hlower : ∀ e ∈ G.edgeSet, quantum K ≤ f e) (v : Fin N) :
    load G (scaledDyadic G K f) v ≤ 1/8 := by
  calc
    _ ≤ ∑ e ∈ G.incidenceFinset v, f e/8 := sum_le_sum (fun e _ => (scaledDyadic_bounds G K f hf hlower e).2)
    _ = load G f v/8 := by simp only [load,RandomOrderCRS.fracDegree,sum_div]
    _ ≤ 1/8 := by
      have hh := hf.2.2 v
      change load G f v ≤ 1 at hh
      linarith

lemma smallload_potential (x : Sym2 (Fin N) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hload : ∀ v, load G x v ≤ 1/8) : totalWeight G x/2 ≤ potential G x := by
  have hpen : penalty G x ≤ totalWeight G x/2 := by
    have hs := sum_loads G x
    have hsq : (∑ v, (load G x v)^2) ≤ (∑ v, load G x v)/8 := by
      rw [sum_div]
      apply sum_le_sum
      intro v _
      have hn : 0 ≤ load G x v := by
        unfold load RandomOrderCRS.fracDegree
        exact sum_nonneg (fun e _ => hx e)
      nlinarith [hload v]
    unfold penalty
    linarith
  unfold potential
  linarith

lemma scaledDyadic_potential (K : ℕ) (f : Sym2 (Fin N) → ℝ) (hf : fractional G f)
    (hlower : ∀ e ∈ G.edgeSet, quantum K ≤ f e) (hweight : (optimum G : ℝ)/4 ≤ totalWeight G f) :
    (optimum G : ℝ)/128 ≤ potential G (scaledDyadic G K f) := by
  have hw : totalWeight G f/16 ≤ totalWeight G (scaledDyadic G K f) := by
    unfold totalWeight
    rw [sum_div]
    exact sum_le_sum (fun e _ => (scaledDyadic_bounds G K f hf hlower e).1)
  have hp := smallload_potential G (scaledDyadic G K f) (scaledDyadic_nonnegative G K f).1
    (scaledDyadic_load G K f hf hlower)
  linarith

end BipartiteRounding

-- Solutions/Sol_bipartite_program.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteProgram

structure Memory where
  neighbors : Finset ℕ
  side : Bool
  values : ℕ → ℝ
  edgeColors : ℕ → ℕ
  groups : List (Finset ℕ)
  leaders : ℕ → Option Key
  cuts : ℕ → Bool

def emptyMemory (inp : Finset ℕ × Bool) : Memory :=
  ⟨inp.1,inp.2,fun _ => 0,fun _ => 0,[],fun _ => none,fun _ => false⟩

def groupColor (id : ℕ) (st : Memory) (i : ℕ) : ℕ :=
  if h : i < st.groups.length then
    let S := st.groups.get ⟨i,h⟩
    if hs : S.Nonempty then
      let j := S.min' hs
      2*st.edgeColors j+if id < j then 0 else 1
    else 0
  else 0

def blockInput (id : ℕ) (st : Memory) : StageInput :=
  ⟨st.neighbors,LocalWeights.mask st.neighbors st.values,st.groups,fun _ => none,groupColor id st,fun _ => false,none⟩

def cutInput (id : ℕ) (st : Memory) : StageInput :=
  ⟨st.neighbors,LocalWeights.mask st.neighbors st.values,st.groups,st.leaders,groupColor id st,fun _ => false,none⟩

def roundingInput (id : ℕ) (st : Memory) : StageInput :=
  ⟨st.neighbors,LocalWeights.mask st.neighbors st.values,st.groups,st.leaders,fun _ => 0,st.cuts,some st.side⟩

def formGroups (q : ℝ) (st : Memory) : Memory :=
  {st with groups := LocalPairing.localGroups q st.neighbors st.values,leaders := fun _ => none,cuts := fun _ => false}

def storeBlocks (st : Memory) (out : ℕ → Option Key) : Memory :=
  {st with leaders := fun i => if i < st.groups.length then out i else none}

def storeCuts (st : Memory) (out : ℕ → Bool) : Memory :=
  {st with cuts := fun i => if i < st.groups.length then out i else false}

def storeWeights (st : Memory) (out : ℕ → ℝ) : Memory :=
  {st with values := LocalWeights.mask st.neighbors out}

variable (AB : Deterministic StageParameters StageInput (ℕ → Option Key))
    (AC : Deterministic StageParameters StageInput (ℕ → Bool))
    (AR : Deterministic StageParameters StageInput (ℕ → ℝ))
    (AU : Deterministic Unit (Finset ℕ × (ℕ → ℝ)) (ℕ → ℝ)) (k : StageParameters)

def blocks : Deterministic Unit Memory Memory :=
  LocalTransform.transform (LocalTransform.freeze AB k) blockInput (fun _ st out => storeBlocks st out)

def cuts : Deterministic Unit Memory Memory :=
  LocalTransform.transform (LocalTransform.freeze AC k) cutInput (fun _ st out => storeCuts st out)

def rounding : Deterministic Unit Memory Memory :=
  LocalTransform.transform (LocalTransform.freeze AR k) roundingInput (fun _ st out => storeWeights st out)

def cleanupStep : Deterministic Unit Memory Memory :=
  LocalTransform.transform AU (fun _ st => (st.neighbors,LocalWeights.mask st.neighbors st.values))
    (fun _ st out => storeWeights st out)

def thenDo (A B : Deterministic Unit Memory Memory) : Deterministic Unit Memory Memory :=
  LocalSequence.sequence A B (fun _ _ _ out => out)

def stage : Deterministic Unit Memory Memory :=
  thenDo (LocalTransform.pointwise (fun _ st => formGroups k.q st))
    (thenDo (blocks AB k) (thenDo (cuts AC k) (thenDo (rounding AR k) (cleanupStep AU))))

lemma stage_rounds : (stage AB AC AR AU k).program.rounds () =
    AB.program.rounds k+AC.program.rounds k+AR.program.rounds k+AU.program.rounds ()+4 := by
  change 0+1+(AB.program.rounds k+1+(AC.program.rounds k+1+(AR.program.rounds k+1+AU.program.rounds ()))) = _
  omega

variable (AF : Deterministic Bounds (Finset ℕ) (ℕ → ℝ))
    (AZ : Deterministic (Bounds × ℕ) (Finset ℕ) (ℕ → ℕ)) (base : Bounds) (ell K : ℕ)

def initialization : Deterministic Unit (Finset ℕ × Bool) Memory :=
  LocalTransform.transform (LocalTransform.freeze AF base) (fun _ inp => inp.1)
    (fun _ inp out => {emptyMemory inp with values := fun j =>
      if j ∈ inp.1 then BipartiteRounding.quantum (BipartiteRounding.dyadicIndex K (out j)+3) else 0})

def colorEdges : Deterministic Unit Memory Memory :=
  LocalTransform.transform (LocalTransform.freeze AZ (base,ell)) (fun _ st => st.neighbors)
    (fun _ st out => {st with edgeColors := out})

end BipartiteProgram

-- Solutions/Sol_cut_geometry.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace DeterministicCuts

variable {N : ℕ} {p : Pairing N}

def interaction (B : BlockAssignment p) : SimpleGraph (Copy p) where
  Adj a b := a ≠ b ∧ B a = some a ∧ B b = some b ∧
    ∃ c ∈ block B a, ∃ d ∈ block B b, c.1 = d.1
  symm := ⟨by
    rintro a b ⟨hne,ha,hb,c,hc,d,hd,he⟩
    exact ⟨hne.symm,hb,ha,d,hd,c,hc,he.symm⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

lemma virtual_walk_physical (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (hp : ValidPairing G x q p) {a b : Copy p} (w : (virtualGraph p).Walk a b) :
    ∃ u : G.Walk a.1 b.1, u.length = w.length := by
  induction w with
  | nil => exact ⟨.nil,rfl⟩
  | @cons a b c h w ih =>
    obtain ⟨u,hu⟩ := ih
    have hab := (hp.2.2.1 a b.1 h.2.1).1
    exact ⟨.cons hab u,by simp [hu]⟩

lemma internal_walk_short (B : BlockAssignment p) (ell : ℕ) (hB : ValidBlocks ell B)
    (a : Copy p) (ha : B a = some a) (c : Copy p) (hc : c ∈ block B a) :
    ∃ w : (virtualGraph p).Walk a c, w.length ≤ 65*ell := by
  obtain ⟨w,hw⟩ := (hB.2 a a ha).2.2.2 c hc
  let path := w.toPath
  have hsub : (path.val.support.toFinset : Finset (Copy p)) ⊆ block B a := by
    intro z hz
    exact hw z (w.support_toPath_subset_support (List.mem_toFinset.mp hz))
  have hcard := card_le_card hsub
  rw [List.toFinset_card_of_nodup path.property.support_nodup,SimpleGraph.Walk.length_support] at hcard
  have hbnd := (hB.2 a a ha).2.2.1
  exact ⟨path.val,by omega⟩

lemma member_close (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (hp : ValidPairing G x q p) (B : BlockAssignment p) (ell : ℕ) (hB : ValidBlocks ell B)
    (a : Copy p) (ha : B a = some a) (c : Copy p) (hc : c ∈ block B a) :
    Close G (65*ell) a.1 c.1 := by
  obtain ⟨w,hw⟩ := internal_walk_short B ell hB a ha c hc
  obtain ⟨u,hu⟩ := virtual_walk_physical G x q hp w
  exact ⟨u,hu.trans_le hw⟩

lemma interaction_close (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (hp : ValidPairing G x q p) (B : BlockAssignment p) (ell : ℕ) (hB : ValidBlocks ell B)
    (a b : Copy p) (hab : (interaction B).Adj a b) : Close G (130*ell) a.1 b.1 := by
  obtain ⟨hne,ha,hb,c,hc,d,hd,he⟩ := hab
  obtain ⟨wa,hwa⟩ := member_close G x q hp B ell hB a ha c hc
  have hbclose := member_close G x q hp B ell hB b hb d hd
  rw [←he] at hbclose
  obtain ⟨wb,hwb⟩ := hbclose
  refine ⟨wa.append wb.reverse,?_⟩
  rw [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_reverse]
  omega

lemma interaction_proper (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (hp : ValidPairing G x q p) (B : BlockAssignment p) (ell : ℕ) (hB : ValidBlocks ell B)
    (zeta : ℕ) (col : Copy p → ℕ) (hcol : ReusableColors G ell zeta col) :
    Proper (interaction B) zeta col := by
  refine ⟨hcol.1,?_⟩
  intro a b hab
  apply hcol.2 a b hab.1
  obtain ⟨w,hw⟩ := interaction_close G x q hp B ell hB a b hab
  exact ⟨w,by omega⟩

lemma copyIdentity_injective (ids : Fin N → ℕ) (hi : Function.Injective ids) :
    Function.Injective (fun a : Copy p => Nat.pair (ids a.1) a.2.val) := by
  intro a b he
  have hf := Nat.pair_eq_pair.mp he
  have hfirst := hi hf.1
  cases a with
  | mk v i =>
    cases b with
    | mk w j =>
      dsimp only at hfirst hf
      subst w
      have hij : i = j := Fin.ext hf.2
      subst j
      rfl

lemma interaction_walk (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (hp : ValidPairing G x q p) (B : BlockAssignment p) (ell : ℕ) (hB : ValidBlocks ell B)
    {a b : Copy p} (w : (interaction B).Walk a b) :
    ∃ path : G.Walk a.1 b.1, path.length ≤ 130*ell*w.length := by
  induction w with
  | nil => exact ⟨.nil,by simp⟩
  | @cons a b c h w ih =>
    obtain ⟨edge,he⟩ := interaction_close G x q hp B ell hB a b h
    obtain ⟨path,hpath⟩ := ih
    refine ⟨edge.append path,?_⟩
    rw [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_cons]
    nlinarith

lemma interaction_close_physical (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (hp : ValidPairing G x q p) (B : BlockAssignment p) (ell : ℕ) (hB : ValidBlocks ell B)
    (t : ℕ) (a b : Copy p) (hclose : Close (interaction B) t a b) :
    Close G (130*ell*t) a.1 b.1 := by
  obtain ⟨w,hw⟩ := hclose
  obtain ⟨path,hpath⟩ := interaction_walk G x q hp B ell hB w
  exact ⟨path,hpath.trans (Nat.mul_le_mul_left (130*ell) hw)⟩

end DeterministicCuts

-- Solutions/Sol_pairing_colors.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace LocalPairing
section Picks
variable {N : ℕ} (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (p : Pairing N) (hp : ValidPairing G x q p) (ids : Fin N → ℕ) (hi : Function.Injective ids)

def groupNonempty (a : Copy p) : (group p a).Nonempty := card_pos.mp (by rcases hp.1 a with h|h <;> omega)

def pickID (a : Copy p) : ℕ := ((group p a).image ids).min' ((groupNonempty G x q p hp a).image ids)

def pick (a : Copy p) : Fin N :=
  ((mem_image.mp (((group p a).image ids).min'_mem ((groupNonempty G x q p hp a).image ids)))).choose

lemma pick_spec (a : Copy p) : pick G x q p hp ids a ∈ group p a ∧ ids (pick G x q p hp ids a) = pickID G x q p hp ids a :=
  ((mem_image.mp (((group p a).image ids).min'_mem ((groupNonempty G x q p hp a).image ids)))).choose_spec

lemma pick_valid : CopyEdgeChoice G p (pick G x q p hp ids) := by
  constructor
  · intro a
    exact (hp.2.2.1 a _ (pick_spec G x q p hp ids a).1).1
  · intro a b hab hne heq
    have hactive := hp.2.2.1 a _ (pick_spec G x q p hp ids a).1
    have huniq := (hp.2.1 a.1 (pick G x q p hp ids a)).mp hactive
    cases a with
    | mk u i =>
      cases b with
      | mk v j =>
        change u = v at hab
        subst v
        have hi' := (pick_spec G x q p hp ids ⟨u,i⟩).1
        have hj' : pick G x q p hp ids ⟨u,i⟩ ∈ group p ⟨u,j⟩ := heq ▸ (pick_spec G x q p hp ids ⟨u,j⟩).1
        have hij : i = j := huniq.unique hi' hj'
        subst j
        exact hne rfl

include hp in
lemma reusable_separates (ell zeta : ℕ) (col : Copy p → ℕ)
    (hc : ReusableColors G ell zeta col) : Separates (virtualGraph p) (64*ell) zeta col := by
  refine ⟨hc.1,?_⟩
  intro a b hab hclose
  obtain ⟨w,hw⟩ := hclose
  obtain ⟨u,hu⟩ := DeterministicCuts.virtual_walk_physical G x q hp w
  exact hc.2 a b hab ⟨u,by omega⟩

end Picks
end LocalPairing

-- Solutions/Sol_stage_input_colors.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteProgram

@[ext] lemma stageInput_ext (a b : StageInput) (hn : a.neighbors = b.neighbors)
    (he : a.edgeValue = b.edgeValue) (hg : a.groups = b.groups) (hl : a.leader = b.leader)
    (hc : a.color = b.color) (hcut : a.cut = b.cut) (hs : a.side = b.side) : a = b := by
  cases a
  cases b
  simp_all

structure Represents {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
    (x : Sym2 (Fin N) → ℝ) (chi : Sym2 (Fin N) → ℕ) (side : Fin N → Bool) (st : Fin N → Memory) : Prop where
  neighbors : ∀ v, (st v).neighbors = neighborIDs G ids v
  sides : ∀ v, (st v).side = side v
  weights : ReportsWeights G ids (fun v => (st v).values) x
  colors : ∀ u v, G.Adj u v → (st u).edgeColors (ids v) = chi s(u,v)

section Color
variable {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (hi : Function.Injective ids)
    (x : Sym2 (Fin N) → ℝ) (q : ℝ) (p : Pairing N) (hp : ValidPairing G x q p)
    (chi : Sym2 (Fin N) → ℕ) (st : Fin N → Memory)
    (hcolors : ∀ u v, G.Adj u v → (st u).edgeColors (ids v) = chi s(u,v))
    (hgroups : ∀ v, (st v).groups = (p v).map (image ids))
include hi hp hcolors hgroups

lemma groupColor_correct (a : Copy p) :
    groupColor (ids a.1) (st a.1) a.2.val =
      copyColor ids chi (LocalPairing.pick G x q p hp ids) a := by
  have hlen : a.2.val < (st a.1).groups.length := by rw [hgroups a.1,List.length_map]; exact a.2.isLt
  have hg : (st a.1).groups.get ⟨a.2.val,hlen⟩ = (group p a).image ids := by
    simp only [List.get_eq_getElem]
    simp only [hgroups a.1,List.getElem_map]
    rfl
  have hnon := (LocalPairing.groupNonempty G x q p hp a).image ids
  have hpick := LocalPairing.pick_spec G x q p hp ids a
  have hAdj := (hp.2.2.1 a _ hpick.1).1
  unfold groupColor
  rw [dif_pos hlen]
  dsimp only
  rw [hg,dif_pos hnon]
  change 2*(st a.1).edgeColors (LocalPairing.pickID G x q p hp ids a)+
    (if ids a.1 < LocalPairing.pickID G x q p hp ids a then 0 else 1) = _
  rw [←hpick.2,hcolors a.1 _ hAdj]
  rfl

lemma color_function (v : Fin N) : groupColor (ids v) (st v) =
    (stageInput G ids x p none (some (copyColor ids chi (LocalPairing.pick G x q p hp ids)))
      (fun _ => false) (fun _ => none) v).color := by
  funext i
  by_cases hi' : i < (p v).length
  · have heq := groupColor_correct G ids hi x q p hp chi st hcolors hgroups ⟨v,⟨i,hi'⟩⟩
    simpa only [stageInput,dif_pos hi',Option.map_some,Option.getD_some] using heq
  · have hbad : ¬i < (st v).groups.length := by rw [hgroups v,List.length_map]; exact hi'
    unfold groupColor
    rw [dif_neg hbad]
    simp only [stageInput,dif_neg hi']

end Color
end BipartiteProgram

-- Solutions/Sol_stage_inputs.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteProgram
section Inputs
variable {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (hi : Function.Injective ids)
    (x : Sym2 (Fin N) → ℝ) (q : ℝ) (p : Pairing N) (hp : ValidPairing G x q p)
    (chi : Sym2 (Fin N) → ℕ) (side : Fin N → Bool) (st : Fin N → Memory)
    (hrep : Represents G ids x chi side st)
    (hgroups : ∀ v, (st v).groups = (p v).map (image ids))
include hi hp hrep hgroups

lemma blocks_input_eq (v : Fin N) : blockInput (ids v) (st v) =
    stageInput G ids x p none (some (copyColor ids chi (LocalPairing.pick G x q p hp ids)))
      (fun _ => false) (fun _ => none) v := by
  apply stageInput_ext
  · exact hrep.neighbors v
  · change LocalWeights.mask (st v).neighbors (st v).values = (weightInput G ids x v).2
    rw [hrep.neighbors v]
    exact LocalWeights.mask_eq_weight G ids hi x _ hrep.weights v
  · exact hgroups v
  · funext i
    simp [blockInput,stageInput]
  · exact color_function G ids hi x q p hp chi st hrep.colors hgroups v
  · funext i
    simp [blockInput,stageInput]
  · rfl

lemma stored_blocks_leaders (out : Fin N → ℕ → Option Key) (B : BlockAssignment p)
    (hout : ReportsBlocks ids out B) (v : Fin N) :
    (storeBlocks (st v) (out v)).leaders =
      (stageInput G ids x p (some B) none (fun _ => false) (fun _ => none) v).leader := by
  funext i
  by_cases hi' : i < (p v).length
  · have hlen : i < (st v).groups.length := by rw [hgroups v,List.length_map]; exact hi'
    change (if i < (st v).groups.length then out v i else none) = _
    rw [if_pos hlen]
    simpa only [stageInput,dif_pos hi',Option.bind_some] using hout ⟨v,⟨i,hi'⟩⟩
  · have hbad : ¬i < (st v).groups.length := by rw [hgroups v,List.length_map]; exact hi'
    change (if i < (st v).groups.length then out v i else none) = _
    rw [if_neg hbad]
    simp only [stageInput,dif_neg hi']

lemma cuts_input_eq (B : BlockAssignment p)
    (hleaders : ∀ v, (st v).leaders =
      (stageInput G ids x p (some B) none (fun _ => false) (fun _ => none) v).leader) (v : Fin N) :
    cutInput (ids v) (st v) = stageInput G ids x p (some B)
      (some (copyColor ids chi (LocalPairing.pick G x q p hp ids))) (fun _ => false) (fun _ => none) v := by
  apply stageInput_ext
  · exact hrep.neighbors v
  · change LocalWeights.mask (st v).neighbors (st v).values = (weightInput G ids x v).2
    rw [hrep.neighbors v]
    exact LocalWeights.mask_eq_weight G ids hi x _ hrep.weights v
  · exact hgroups v
  · exact hleaders v
  · exact color_function G ids hi x q p hp chi st hrep.colors hgroups v
  · funext i
    simp [cutInput,stageInput]
  · rfl

lemma stored_cuts_function (out : Fin N → ℕ → Bool) (B : BlockAssignment p)
    (s : Copy p → Copy p) (hout : ReportsCuts out B s) (v : Fin N) :
    (storeCuts (st v) (out v)).cuts =
      (stageInput G ids x p (some B) none (cutMarks B s) (fun v => some (side v)) v).cut := by
  funext i
  by_cases hi' : i < (p v).length
  · have hlen : i < (st v).groups.length := by rw [hgroups v,List.length_map]; exact hi'
    change (if i < (st v).groups.length then out v i else false) = _
    rw [if_pos hlen]
    simp only [stageInput,dif_pos hi']
    apply Bool.eq_iff_iff.mpr
    change out v i = true ↔ decide (∃ b, B b = some b ∧ s b = ⟨v,⟨i,hi'⟩⟩) = true
    rw [decide_eq_true_eq]
    exact hout ⟨v,⟨i,hi'⟩⟩
  · have hbad : ¬i < (st v).groups.length := by rw [hgroups v,List.length_map]; exact hi'
    change (if i < (st v).groups.length then out v i else false) = _
    rw [if_neg hbad]
    simp only [stageInput,dif_neg hi']

lemma rounding_input_eq (B : BlockAssignment p) (s : Copy p → Copy p)
    (hleaders : ∀ v, (st v).leaders =
      (stageInput G ids x p (some B) none (fun _ => false) (fun _ => none) v).leader)
    (hcuts : ∀ v, (st v).cuts =
      (stageInput G ids x p (some B) none (cutMarks B s) (fun v => some (side v)) v).cut) (v : Fin N) :
    roundingInput (ids v) (st v) = stageInput G ids x p (some B) none (cutMarks B s) (fun v => some (side v)) v := by
  apply stageInput_ext
  · exact hrep.neighbors v
  · change LocalWeights.mask (st v).neighbors (st v).values = (weightInput G ids x v).2
    rw [hrep.neighbors v]
    exact LocalWeights.mask_eq_weight G ids hi x _ hrep.weights v
  · exact hgroups v
  · exact hleaders v
  · funext i
    simp [roundingInput,stageInput]
  · exact hcuts v
  · change some (st v).side = some (side v)
    rw [hrep.sides v]

end Inputs
end BipartiteProgram

-- Solutions/Sol_stage_program_execution.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteProgram

lemma thenDo_output {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (st : Fin N → Memory)
    (A B : Deterministic Unit Memory Memory) (v : Fin N) :
    (thenDo A B).program.output G () ids st (fun _ _ => false) v =
      B.program.output G () ids (A.program.output G () ids st (fun _ _ => false)) (fun _ _ => false) v := by
  rw [thenDo,LocalSequence.sequence_output]

lemma blocks_output {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (st : Fin N → Memory)
    (A : Deterministic StageParameters StageInput (ℕ → Option Key)) (k : StageParameters) (v : Fin N) :
    (blocks A k).program.output G () ids st (fun _ _ => false) v =
      storeBlocks (st v) (execute A G k ids (fun v => blockInput (ids v) (st v)) v) := by
  rw [blocks,LocalTransform.transform_output,LocalTransform.freeze_output]
  rfl

lemma cuts_output {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (st : Fin N → Memory)
    (A : Deterministic StageParameters StageInput (ℕ → Bool)) (k : StageParameters) (v : Fin N) :
    (cuts A k).program.output G () ids st (fun _ _ => false) v =
      storeCuts (st v) (execute A G k ids (fun v => cutInput (ids v) (st v)) v) := by
  rw [cuts,LocalTransform.transform_output,LocalTransform.freeze_output]
  rfl

lemma rounding_output {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (st : Fin N → Memory)
    (A : Deterministic StageParameters StageInput (ℕ → ℝ)) (k : StageParameters) (v : Fin N) :
    (rounding A k).program.output G () ids st (fun _ _ => false) v =
      storeWeights (st v) (execute A G k ids (fun v => roundingInput (ids v) (st v)) v) := by
  rw [rounding,LocalTransform.transform_output,LocalTransform.freeze_output]
  rfl

lemma cleanup_output {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (st : Fin N → Memory)
    (A : Deterministic Unit (Finset ℕ × (ℕ → ℝ)) (ℕ → ℝ)) (v : Fin N) :
    (cleanupStep A).program.output G () ids st (fun _ _ => false) v =
      storeWeights (st v) (execute A G () ids (fun v => ((st v).neighbors,LocalWeights.mask (st v).neighbors (st v).values)) v) := by
  rw [cleanupStep,LocalTransform.transform_output]
  rfl

section Representation
variable {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
    (x : Sym2 (Fin N) → ℝ) (chi : Sym2 (Fin N) → ℕ) (side : Fin N → Bool) (st : Fin N → Memory)
    (h : Represents G ids x chi side st)

include h

lemma represents_formGroups (q : ℝ) : Represents G ids x chi side (fun v => formGroups q (st v)) :=
  ⟨h.neighbors,h.sides,h.weights,h.colors⟩

lemma represents_storeBlocks (out : Fin N → ℕ → Option Key) :
    Represents G ids x chi side (fun v => storeBlocks (st v) (out v)) := ⟨h.neighbors,h.sides,h.weights,h.colors⟩

lemma represents_storeCuts (out : Fin N → ℕ → Bool) :
    Represents G ids x chi side (fun v => storeCuts (st v) (out v)) := ⟨h.neighbors,h.sides,h.weights,h.colors⟩

lemma represents_storeWeights (y : Sym2 (Fin N) → ℝ) (out : Fin N → ℕ → ℝ)
    (hout : ReportsWeights G ids out y) :
    Represents G ids y chi side (fun v => storeWeights (st v) (out v)) := by
  refine ⟨h.neighbors,h.sides,?_,h.colors⟩
  have hh := LocalWeights.masked_reports G ids y out hout
  simpa only [storeWeights,h.neighbors] using hh

lemma formGroups_correct (q : ℝ) (hi : Function.Injective ids) :
    ∀ v, (formGroups q (st v)).groups = (LocalPairing.pairing G x q ids hi v).map (image ids) := by
  intro v
  change LocalPairing.localGroups q (st v).neighbors (st v).values = _
  rw [h.neighbors v]
  exact LocalPairing.localGroups_correct G x q ids hi _ h.weights v

end Representation
end BipartiteProgram

-- Solutions/Sol_rounding_feasible.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingRounding
variable {N : ℕ} (G : SimpleGraph (Fin N))

lemma load_nonneg (x : Sym2 (Fin N) → ℝ) (hx : ∀ e, 0 ≤ x e) (v : Fin N) : 0 ≤ load G x v := by
  unfold load RandomOrderCRS.fracDegree
  exact sum_nonneg (fun e _ => hx e)

lemma load_add (x d : Sym2 (Fin N) → ℝ) (v : Fin N) :
    load G (fun e => x e+d e) v = load G x v+load G d v := by
  unfold load RandomOrderCRS.fracDegree
  simp only [sum_add_distrib]

lemma edge_le_load (x : Sym2 (Fin N) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (u v : Fin N) (hAdj : G.Adj u v) : x s(u,v) ≤ load G x u := by
  unfold load RandomOrderCRS.fracDegree
  apply single_le_sum (fun e _ => hx e)
  exact (G.mem_incidenceFinset u s(u,v)).mpr ⟨G.mem_edgeSet.mpr hAdj,by simp⟩

lemma double_load_bound (x y : Sym2 (Fin N) → ℝ) (hxy : ∀ e, y e ≤ 2*x e) (v : Fin N) :
    load G y v ≤ 2*load G x v := by
  unfold load RandomOrderCRS.fracDegree
  calc
    _ ≤ ∑ e ∈ G.incidenceFinset v, 2*x e := sum_le_sum (fun e _ => hxy e)
    _ = _ := (mul_sum ..).symm

lemma dominated_fractional (x y : Sym2 (Fin N) → ℝ) (hx : fractional G x)
    (hload : ∀ v, load G x v ≤ 1/2) (hy : ∀ e, 0 ≤ y e ∧ y e ≤ 2*x e) :
    fractional G y ∧ ∀ v, load G y v ≤ 1 := by
  have hx0 : ∀ e, 0 ≤ x e := fun e => (hx.1 e).1
  have hyload (v : Fin N) : load G y v ≤ 1 := by
    have hh := double_load_bound G x y (fun e => (hy e).2) v
    have ht := hload v
    linarith
  have hsupport (e : Sym2 (Fin N)) (he : e ∉ G.edgeSet) : y e = 0 := by
    have hxz := hx.2.1 e he
    have hh := hy e
    rw [hxz] at hh
    linarith
  have hyupper (e : Sym2 (Fin N)) : y e ≤ 1 := by
    by_cases he : e ∈ G.edgeSet
    · obtain ⟨⟨u,v⟩,rfl⟩ := e.exists_rep
      have hAdj := G.mem_edgeSet.mp he
      have hh := edge_le_load G x hx0 u v hAdj
      have ht := hload u
      have hb := (hy s(u,v)).2
      linarith
    · rw [hsupport e he]
      norm_num
  exact ⟨⟨fun e => ⟨(hy e).1,hyupper e⟩,hsupport,hyload⟩,hyload⟩

end MatchingRounding

-- Solutions/Sol_rounding_accumulation.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteRounding

lemma quantum_sum (K n : ℕ) (hn : n ≤ K) :
    (∑ t ∈ range n, quantum (K-t)) = quantum (K-n)-quantum K := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ,ih (by omega)]
    have hk : K-n = (K-(n+1))+1 := by omega
    have hq := quantum_succ (K-(n+1))
    rw [←hk] at hq
    linarith

lemma quantum_sum_small (K n : ℕ) (hn : n+16 ≤ K) :
    (∑ t ∈ range n, quantum (K-t)) ≤ 1/65536 := by
  rw [quantum_sum K n (by omega)]
  have hq := quantum_antitone (show 16 ≤ K-n by omega)
  norm_num [quantum] at hq ⊢
  have hp : 0 ≤ ((2:ℝ)^K)⁻¹ := by positivity
  linarith

variable {N : ℕ} (G : SimpleGraph (Fin N))

lemma fractional_of_load (x : Sym2 (Fin N) → ℝ) (hx : NonnegativeAssignment G x)
    (hload : ∀ v, load G x v ≤ 1/2) : fractional G x := by
  refine ⟨?_,hx.2,fun v => (hload v).trans (by norm_num)⟩
  intro e
  refine ⟨hx.1 e,?_⟩
  by_cases he : e ∈ G.edgeSet
  · obtain ⟨⟨u,v⟩,rfl⟩ := e.exists_rep
    have hadj := G.mem_edgeSet.mp he
    have hh := MatchingRounding.edge_le_load G x hx.1 u v hadj
    linarith [hload u]
  · rw [hx.2 e he]
    norm_num

lemma stage_loss_bound (x y : Sym2 (Fin N) → ℝ) (hx : fractional G x)
    (hload : ∀ v, load G x v ≤ 1/2) (ell : ℝ) (hell : 0 < ell) (q : ℝ) (hq : 0 ≤ q)
    (hloss : potential G x-(8*penalty G x/ell^2+72*q*totalWeight G x) ≤ potential G y) :
    potential G x-(optimum G : ℝ)*(16/ell^2+72*q) ≤ potential G y := by
  have hw := halfload_weight_bound G x (fun e => (hx.1 e).1) hload
  have hp := halfload_penalty_bound G x (fun e => (hx.1 e).1) hload
  have hpen : penalty G x ≤ 2*(optimum G : ℝ) := hp.trans (by linarith)
  have hd : 0 < ell^2 := sq_pos_of_pos hell
  have hterm : 8*penalty G x/ell^2 ≤ 16*(optimum G : ℝ)/ell^2 :=
    div_le_div_of_nonneg_right (by linarith) hd.le
  have hqterm : 72*q*totalWeight G x ≤ 72*q*(optimum G : ℝ) :=
    mul_le_mul_of_nonneg_left hw (by positivity)
  have heq : (optimum G : ℝ)*(16/ell^2+72*q) = 16*(optimum G : ℝ)/ell^2+72*q*(optimum G : ℝ) := by ring
  rw [heq]
  linarith

lemma accumulated_loss (K n : ℕ) (ell : ℝ) (Phi : ℕ → ℝ) (O : ℝ)
    (hstep : ∀ t < n, Phi t-O*(16/ell^2+72*quantum (K-t)) ≤ Phi (t+1)) :
    Phi 0-O*(16*n/ell^2+72*∑ t ∈ range n, quantum (K-t)) ≤ Phi n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hi := ih (fun t ht => hstep t (by omega))
    have hs := hstep n (by omega)
    rw [sum_range_succ,Nat.cast_add,Nat.cast_one]
    ring_nf at hi hs ⊢
    linarith

lemma accumulated_retention (K n ell : ℕ) (Phi : ℕ → ℝ) (O : ℝ) (hO : 0 ≤ O)
    (hn : n+16 ≤ K) (hell : 65536*(n:ℝ) ≤ (ell:ℝ)^2) (hellpos : 0 < ell)
    (hinit : O/128 ≤ Phi 0)
    (hstep : ∀ t < n, Phi t-O*(16/(ell:ℝ)^2+72*quantum (K-t)) ≤ Phi (t+1)) : O/256 ≤ Phi n := by
  have htotal := accumulated_loss K n ell Phi O hstep
  have hq := quantum_sum_small K n hn
  have hd : 0 < (ell:ℝ)^2 := by positivity
  have hdiv : 16*(n:ℝ)/(ell:ℝ)^2 ≤ 16/65536 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hsmall : 16*(n:ℝ)/(ell:ℝ)^2+72*(∑ t ∈ range n, quantum (K-t)) ≤ 1/256 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsmall hO
  linarith

end BipartiteRounding

-- Solutions/Sol_two_schedule.lean

open Classical Finset
noncomputable section
namespace MatchingRounding

variable {V : Type} [Fintype V]

def TwoSchedule (R : V → V → ℕ) (X : V → V → Fin 2 → ℕ) : Prop :=
  (∀ u v, (∑ k, X u v k) = R u v) ∧
  (∀ u k, (∑ v, X u v k) ≤ 1) ∧ (∀ v k, (∑ u, X u v k) ≤ 1)

lemma two_schedule_exists (R : V → V → ℕ)
    (hrow : ∀ u, (∑ v, R u v) ≤ 2) (hcol : ∀ v, (∑ u, R u v) ≤ 2) :
    ∃ X : V → V → Fin 2 → ℕ, TwoSchedule R X := by
  let e := Fintype.equivFin V
  let matrix := fun i j => R (e.symm i) (e.symm j)
  have hr (i : Fin (Fintype.card V)) : Timetabling85.ClassTeacher.rowSum matrix i ≤ 2 := by
    change (∑ j, R (e.symm i) (e.symm j)) ≤ 2
    rw [e.symm.sum_comp (fun v => R (e.symm i) v)]
    exact hrow _
  have hc (j : Fin (Fintype.card V)) : Timetabling85.ClassTeacher.colSum matrix j ≤ 2 := by
    change (∑ i, R (e.symm i) (e.symm j)) ≤ 2
    rw [e.symm.sum_comp (fun u => R u (e.symm j))]
    exact hcol _
  obtain ⟨x,hx⟩ := (Timetabling85.ClassTeacher.prop_2_1 matrix 2).mpr ⟨hc,hr⟩
  refine ⟨fun u v k => x (e u) (e v) k,?_,?_,?_⟩
  · intro u v
    have hh := hx.1 (e u) (e v)
    simpa only [matrix,Equiv.symm_apply_apply] using hh
  · intro u k
    rw [e.sum_comp (fun j => x (e u) j k)]
    exact hx.2.1 (e u) k
  · intro v k
    rw [e.sum_comp (fun i => x i (e v) k)]
    exact hx.2.2.1 (e v) k

def scheduleSign (X : V → V → Fin 2 → ℕ) (u v : V) : ℝ := (X u v 0:ℝ)-(X u v 1:ℝ)

lemma scheduleSign_unit (R : V → V → ℕ) (X : V → V → Fin 2 → ℕ) (hX : TwoSchedule R X)
    (u v : V) (hR : R u v = 1) : scheduleSign X u v = 1 ∨ scheduleSign X u v = -1 := by
  have hs := hX.1 u v
  rw [Fin.sum_univ_two,hR] at hs
  have hcases : (X u v 0 = 1 ∧ X u v 1 = 0) ∨ (X u v 0 = 0 ∧ X u v 1 = 1) := by omega
  rcases hcases with h|h
  · left; simp only [scheduleSign,h.1,h.2,Nat.cast_one,Nat.cast_zero,sub_zero]
  · right; simp only [scheduleSign,h.1,h.2,Nat.cast_one,Nat.cast_zero,zero_sub]

lemma scheduleSign_row_balance (R : V → V → ℕ) (X : V → V → Fin 2 → ℕ) (hX : TwoSchedule R X)
    (u : V) (hR : (∑ v, R u v) = 2) : (∑ v, scheduleSign X u v) = 0 := by
  have hs : (∑ v, X u v 0)+(∑ v, X u v 1) = 2 := by
    rw [←sum_add_distrib]
    calc
      _ = ∑ v, R u v := sum_congr rfl (fun v _ => by simpa only [Fin.sum_univ_two] using hX.1 u v)
      _ = 2 := hR
  have h0 := hX.2.1 u (0:Fin 2)
  have h1 := hX.2.1 u (1:Fin 2)
  have he0 : (∑ v, X u v 0) = 1 := by omega
  have he1 : (∑ v, X u v 1) = 1 := by omega
  simp only [scheduleSign,sum_sub_distrib,←Nat.cast_sum,he0,he1,sub_self]

lemma scheduleSign_col_balance (R : V → V → ℕ) (X : V → V → Fin 2 → ℕ) (hX : TwoSchedule R X)
    (v : V) (hR : (∑ u, R u v) = 2) : (∑ u, scheduleSign X u v) = 0 := by
  have hs : (∑ u, X u v 0)+(∑ u, X u v 1) = 2 := by
    rw [←sum_add_distrib]
    calc
      _ = ∑ u, R u v := sum_congr rfl (fun u _ => by simpa only [Fin.sum_univ_two] using hX.1 u v)
      _ = 2 := hR
  have h0 := hX.2.2 v (0:Fin 2)
  have h1 := hX.2.2 v (1:Fin 2)
  have he0 : (∑ u, X u v 0) = 1 := by omega
  have he1 : (∑ u, X u v 1) = 1 := by omega
  simp only [scheduleSign,sum_sub_distrib,←Nat.cast_sum,he0,he1,sub_self]

end MatchingRounding

-- Solutions/Sol_bipartite_signs.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace MatchingRounding
section Signs
variable {V : Type} [Fintype V] (H : SimpleGraph V) (side : V → Bool)

def bipartiteMatrix (u v : V) : ℕ := if H.Adj u v ∧ side u = false ∧ side v = true then 1 else 0

lemma adjacency_sum (v : V) : (∑ w, if H.Adj v w then (1:ℕ) else 0) = H.degree v := by
  rw [Finset.sum_boole]
  have he : univ.filter (H.Adj v) = H.neighborFinset v := by ext w; simp
  rw [he,H.card_neighborFinset_eq_degree]
  simp only [Nat.cast_id]

variable (hSide : ∀ u v, H.Adj u v → side u ≠ side v)
include hSide

lemma bipartiteMatrix_row (u : V) (hu : side u = false) :
    (∑ v, bipartiteMatrix H side u v) = H.degree u := by
  have he (v : V) : bipartiteMatrix H side u v = if H.Adj u v then 1 else 0 := by
    by_cases hadj : H.Adj u v
    · have hv : side v = true := by have h := hSide u v hadj; cases hs : side v <;> simp_all
      simp only [bipartiteMatrix,hadj,hu,hv,and_self,ite_true]
    · simp only [bipartiteMatrix,hadj,false_and,ite_false]
  simp only [he]
  exact adjacency_sum H u

lemma bipartiteMatrix_col (v : V) (hv : side v = true) :
    (∑ u, bipartiteMatrix H side u v) = H.degree v := by
  have he (u : V) : bipartiteMatrix H side u v = if H.Adj v u then 1 else 0 := by
    by_cases hadj : H.Adj v u
    · have hu : side u = false := by have h := hSide v u hadj; cases hs : side u <;> simp_all
      simp only [bipartiteMatrix,hadj,hadj.symm,hu,hv,and_self,ite_true]
    · have hn : ¬H.Adj u v := fun h => hadj h.symm
      simp only [bipartiteMatrix,hadj,hn,false_and,ite_false]
  simp only [he]
  exact adjacency_sum H v

lemma graph_two_schedule (hD : ∀ v, H.degree v ≤ 2) :
    ∃ X : V → V → Fin 2 → ℕ, TwoSchedule (bipartiteMatrix H side) X := by
  apply two_schedule_exists
  · intro u
    cases hu : side u with
    | false => rw [bipartiteMatrix_row H side hSide u hu]; exact hD u
    | true => simp only [bipartiteMatrix,hu,Bool.true_eq_false,false_and,and_false,ite_false,sum_const_zero]; omega
  · intro v
    cases hv : side v with
    | false => simp only [bipartiteMatrix,hv,Bool.false_eq_true,and_false,ite_false,sum_const_zero]; omega
    | true => rw [bipartiteMatrix_col H side hSide v hv]; exact hD v

end Signs

section EdgeSigns
variable {V : Type} [Fintype V]

def signedEdge (side : V → Bool) (X : V → V → Fin 2 → ℕ) : Sym2 V → ℝ :=
  Sym2.lift ⟨(fun u v => if side u = side v then 0 else
    if side u = false then scheduleSign X u v else scheduleSign X v u),by
      intro u v
      cases hu : side u <;> cases hv : side v <;> simp only [hu,hv,ite_true,ite_false,Bool.false_eq_true,Bool.true_eq_false]⟩

lemma signedEdge_apply (side : V → Bool) (X : V → V → Fin 2 → ℕ) (u v : V) :
    signedEdge side X s(u,v) = if side u = side v then 0 else
      if side u = false then scheduleSign X u v else scheduleSign X v u := rfl

lemma scheduleSign_zero (R : V → V → ℕ) (X : V → V → Fin 2 → ℕ) (hX : TwoSchedule R X)
    (u v : V) (hR : R u v = 0) : scheduleSign X u v = 0 := by
  have hs := hX.1 u v
  rw [Fin.sum_univ_two,hR] at hs
  have h0 : X u v 0 = 0 := by omega
  have h1 : X u v 1 = 0 := by omega
  simp only [scheduleSign,h0,h1,Nat.cast_zero,sub_zero]

lemma sum_neighbors_eq_all (H : SimpleGraph V) (v : V) (f g : V → ℝ)
    (hin : ∀ w, H.Adj v w → f w = g w) (hout : ∀ w, ¬H.Adj v w → g w = 0) :
    (∑ w ∈ H.neighborFinset v, f w) = ∑ w, g w := by
  have hn : H.neighborFinset v = univ.filter (H.Adj v) := by ext w; simp
  rw [hn,sum_filter]
  apply sum_congr rfl
  intro w hw
  by_cases hadj : H.Adj v w
  · rw [if_pos hadj,hin w hadj]
  · rw [if_neg hadj,hout w hadj]

variable (H : SimpleGraph V) (side : V → Bool)
    (hSide : ∀ u v, H.Adj u v → side u ≠ side v)
    (X : V → V → Fin 2 → ℕ) (hX : TwoSchedule (bipartiteMatrix H side) X)
include hSide hX

lemma signedEdge_unit (u v : V) (hAdj : H.Adj u v) :
    signedEdge side X s(u,v) = 1 ∨ signedEdge side X s(u,v) = -1 := by
  cases hu : side u with
  | false =>
    have hv : side v = true := by have h := hSide u v hAdj; cases hs : side v <;> simp_all
    simp only [signedEdge_apply,hu,hv,Bool.false_eq_true,ite_false,ite_true]
    exact scheduleSign_unit _ X hX u v (by simp only [bipartiteMatrix,hAdj,hu,hv,and_self,ite_true])
  | true =>
    have hv : side v = false := by have h := hSide u v hAdj; cases hs : side v <;> simp_all
    simp only [signedEdge_apply,hu,hv,Bool.true_eq_false,ite_false]
    exact scheduleSign_unit _ X hX v u (by simp only [bipartiteMatrix,hAdj.symm,hv,hu,and_self,ite_true])

lemma signedEdge_balanced (v : V) (hDegree : H.degree v = 2) :
    (∑ w ∈ H.neighborFinset v, signedEdge side X s(v,w)) = 0 := by
  cases hv : side v with
  | false =>
    have he : (∑ w ∈ H.neighborFinset v, signedEdge side X s(v,w)) = ∑ w, scheduleSign X v w := by
      apply sum_neighbors_eq_all
      · intro w hadj
        have hw : side w = true := by have h := hSide v w hadj; cases hs : side w <;> simp_all
        simp only [signedEdge_apply,hv,hw,Bool.false_eq_true,ite_false,ite_true]
      · intro w hadj
        apply scheduleSign_zero _ X hX
        simp only [bipartiteMatrix,hadj,false_and,ite_false]
    rw [he]
    exact scheduleSign_row_balance _ X hX v ((bipartiteMatrix_row H side hSide v hv).trans hDegree)
  | true =>
    have he : (∑ w ∈ H.neighborFinset v, signedEdge side X s(v,w)) = ∑ w, scheduleSign X w v := by
      apply sum_neighbors_eq_all
      · intro w hadj
        have hw : side w = false := by have h := hSide v w hadj; cases hs : side w <;> simp_all
        simp only [signedEdge_apply,hv,hw,Bool.true_eq_false,ite_false]
      · intro w hadj
        apply scheduleSign_zero _ X hX
        have hn : ¬H.Adj w v := fun h => hadj h.symm
        simp only [bipartiteMatrix,hn,false_and,ite_false]
    rw [he]
    exact scheduleSign_col_balance _ X hX v ((bipartiteMatrix_col H side hSide v hv).trans hDegree)

end EdgeSigns

lemma bipartite_edge_signs {V : Type} [Fintype V] (H : SimpleGraph V)
    (side : V → Bool) (hSide : ∀ u v, H.Adj u v → side u ≠ side v) (hD : ∀ v, H.degree v ≤ 2) :
    ∃ z : Sym2 V → ℝ,
      (∀ u v, H.Adj u v → z s(u,v) = 1 ∨ z s(u,v) = -1) ∧
      (∀ v, H.degree v = 2 → (∑ w ∈ H.neighborFinset v, z s(v,w)) = 0) := by
  obtain ⟨X,hX⟩ := graph_two_schedule H side hSide hD
  exact ⟨signedEdge side X,signedEdge_unit H side hSide X hX,signedEdge_balanced H side hSide X hX⟩

end MatchingRounding

-- Solutions/Sol_restrict_edges.lean

open Classical Finset
noncomputable section
namespace MatchingRounding
section Restrict
variable {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (S : Finset (Sym2 V))

def restrictEdges : SimpleGraph V where
  Adj a b := H.Adj a b ∧ s(a,b) ∈ S
  symm := ⟨by rintro a b ⟨h,he⟩; exact ⟨h.symm,by simpa only [Sym2.eq_swap] using he⟩⟩
  loopless := ⟨by intro a h; exact h.1.ne rfl⟩

lemma restrictEdges_le : restrictEdges H S ≤ H := fun _ _ h => h.1

lemma restrictEdges_edgeFinset (hS : S ⊆ H.edgeFinset) : (restrictEdges H S).edgeFinset = S := by
  ext e
  obtain ⟨⟨u,v⟩,rfl⟩ := e.exists_rep
  change s(u,v) ∈ (restrictEdges H S).edgeFinset ↔ s(u,v) ∈ S
  rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
  change (H.Adj u v ∧ s(u,v) ∈ S) ↔ s(u,v) ∈ S
  exact ⟨And.right,fun h => ⟨H.mem_edgeSet.mp (H.mem_edgeFinset.mp (hS h)),h⟩⟩

lemma restrictEdges_incidence (hS : S ⊆ H.edgeFinset) (v : V) :
    (restrictEdges H S).incidenceFinset v = S.filter (fun e => v ∈ e) := by
  rw [SimpleGraph.incidenceFinset_eq_filter,restrictEdges_edgeFinset H S hS]

lemma sum_incidence_neighbors (f : Sym2 V → ℝ) (v : V) :
    (∑ e ∈ H.incidenceFinset v, f e) = ∑ w ∈ H.neighborFinset v, f s(v,w) := by
  symm
  apply sum_bij (fun w _ => s(v,w))
  · intro w hw
    simpa using hw
  · intro a ha b hb hab
    exact Sym2.congr_right.mp hab
  · intro e he
    have hh := (H.mem_incidenceFinset v e).mp he
    obtain ⟨w,rfl⟩ := Sym2.mem_iff_exists.mp hh.2
    exact ⟨w,by simpa using hh.1,rfl⟩
  · intro w hw
    rfl

lemma restrictEdges_signs (side : V → Bool) (hSide : ∀ u v, H.Adj u v → side u ≠ side v)
    (hD : ∀ v, H.degree v ≤ 2) (hS : S ⊆ H.edgeFinset) :
    ∃ z : Sym2 V → ℝ,
      (∀ e ∈ S, z e = 1 ∨ z e = -1) ∧
      ∀ v, (S.filter (fun e => v ∈ e)).card = 2 → (∑ e ∈ S.filter (fun e => v ∈ e), z e) = 0 := by
  let J := restrictEdges H S
  have hJSide : ∀ u v, J.Adj u v → side u ≠ side v := fun u v h => hSide u v h.1
  have hJD : ∀ v, J.degree v ≤ 2 := fun v => (J.degree_le_of_le (restrictEdges_le H S)).trans (hD v)
  obtain ⟨z,hz,hbal⟩ := bipartite_edge_signs J side hJSide hJD
  refine ⟨z,?_,?_⟩
  · intro e he
    obtain ⟨⟨u,v⟩,rfl⟩ := e.exists_rep
    have heJ : s(u,v) ∈ J.edgeFinset := by rwa [restrictEdges_edgeFinset H S hS]
    exact hz u v (J.mem_edgeSet.mp (J.mem_edgeFinset.mp heJ))
  · intro v hv
    have hd : J.degree v = 2 := by
      rw [←J.card_incidenceFinset_eq_degree,restrictEdges_incidence H S hS v]
      exact hv
    rw [←restrictEdges_incidence H S hS v,sum_incidence_neighbors]
    exact hbal v hd

end Restrict
end MatchingRounding

-- Solutions/Sol_dyadic_support.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteRounding
variable {N : ℕ} (G : SimpleGraph (Fin N))

def DyadicLevels (x : Sym2 (Fin N) → ℝ) (K : ℕ) : Prop :=
  ∀ e, x e = 0 ∨ ∃ i ≤ K, x e = quantum i

lemma scaledDyadic_levels (K : ℕ) (f : Sym2 (Fin N) → ℝ) (hf : fractional G f)
    (hlower : ∀ e ∈ G.edgeSet, quantum K ≤ f e) : DyadicLevels (scaledDyadic G K f) (K+3) := by
  intro e
  by_cases he : e ∈ G.edgeSet
  · exact Or.inr ⟨dyadicIndex K (f e)+3,by have hh := dyadicIndex_spec K (f e) (hlower e he) (hf.1 e).2; omega,if_pos he⟩
  · exact Or.inl (if_neg he)

lemma rounding_levels (k : ℕ) (x y : Sym2 (Fin N) → ℝ) (hlevel : DyadicLevels x (k+1))
    (hx : fractional G x) (hy : fractional G y)
    (hround : ∀ e ∈ G.edgeSet, (x e = quantum (k+1) → y e = 0 ∨ y e = 2*quantum (k+1)) ∧
      (x e ≠ quantum (k+1) → y e = x e)) : DyadicLevels y k := by
  intro e
  by_cases he : e ∈ G.edgeSet
  · by_cases hactive : x e = quantum (k+1)
    · rcases (hround e he).1 hactive with hz|hz
      · exact Or.inl hz
      · exact Or.inr ⟨k,le_rfl,hz.trans (quantum_succ k).symm⟩
    · rw [(hround e he).2 hactive]
      rcases hlevel e with hz|⟨i,hi,heq⟩
      · exact Or.inl hz
      · have hik : i ≠ k+1 := fun h => hactive (h ▸ heq)
        exact Or.inr ⟨i,by omega,heq⟩
  · exact Or.inl (hy.2.1 e he)

lemma cleanup_levels (k : ℕ) (x : Sym2 (Fin N) → ℝ) (hlevel : DyadicLevels x k) :
    DyadicLevels (cleanup G x) k := by
  intro e
  unfold cleanup
  split_ifs
  · exact Or.inl rfl
  · exact hlevel e

def supportGraph (x : Sym2 (Fin N) → ℝ) : SimpleGraph (Fin N) where
  Adj u v := G.Adj u v ∧ x s(u,v) ≠ 0
  symm := ⟨by rintro u v ⟨h,hx⟩; exact ⟨h.symm,by simpa only [Sym2.eq_swap] using hx⟩⟩
  loopless := ⟨by intro u h; exact h.1.ne rfl⟩

lemma supportGraph_le (x : Sym2 (Fin N) → ℝ) : supportGraph G x ≤ G := fun _ _ h => h.1

lemma support_edgeFinset (x : Sym2 (Fin N) → ℝ) :
    (supportGraph G x).edgeFinset = G.edgeFinset.filter (fun e => x e ≠ 0) := by
  ext e
  obtain ⟨⟨u,v⟩,rfl⟩ := e.exists_rep
  simp only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,mem_filter]
  rfl

lemma support_weight (x : Sym2 (Fin N) → ℝ) : totalWeight (supportGraph G x) x = totalWeight G x := by
  unfold totalWeight
  rw [support_edgeFinset,sum_filter]
  apply sum_congr rfl
  intro e _
  by_cases he : x e = 0 <;> simp [he]

lemma support_degree (x : Sym2 (Fin N) → ℝ) (hx : fractional G x) (hlevels : DyadicLevels x 16) :
    ∀ v, (supportGraph G x).degree v ≤ 65536 := by
  intro v
  let H := supportGraph G x
  have hsub : H.neighborFinset v ⊆ G.neighborFinset v := by
    intro w hw
    exact (SimpleGraph.mem_neighborFinset G v w).mpr ((SimpleGraph.mem_neighborFinset H v w).mp hw).1
  have hlower (w : Fin N) (hw : w ∈ H.neighborFinset v) : (1/65536:ℝ) ≤ x s(v,w) := by
    have hn := ((SimpleGraph.mem_neighborFinset H v w).mp hw).2
    rcases hlevels s(v,w) with hz|⟨i,hi,heq⟩
    · exact (hn hz).elim
    · rw [heq]
      exact (by norm_num [quantum] : (1/65536:ℝ) = quantum 16) ▸ quantum_antitone hi
  have hbound : (H.degree v : ℝ)/65536 ≤ load G x v := by
    calc
      _ = ∑ _ ∈ H.neighborFinset v, (1/65536:ℝ) := by simp [div_eq_mul_inv]
      _ ≤ ∑ w ∈ H.neighborFinset v, x s(v,w) := sum_le_sum hlower
      _ ≤ ∑ w ∈ G.neighborFinset v, x s(v,w) := sum_le_sum_of_subset_of_nonneg hsub (fun w _ _ => (hx.1 s(v,w)).1)
      _ = load G x v := (MatchingRounding.sum_incidence_neighbors G x v).symm
  have hload := hx.2.2 v
  change load G x v ≤ 1 at hload
  have hcast : (H.degree v : ℝ) ≤ 65536 := by linarith
  exact_mod_cast hcast

end BipartiteRounding

-- Solutions/Sol_stage_composition.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteProgram
open BipartiteRounding

lemma stage_composition {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
    (hi : Function.Injective ids) (k : StageParameters) (x : Sym2 (Fin N) → ℝ)
    (chi : Sym2 (Fin N) → ℕ) (side : Fin N → Bool) (st : Fin N → Memory)
    (hrep : Represents G ids x chi side st)
    (AB : Deterministic StageParameters StageInput (ℕ → Option Key))
    (AC : Deterministic StageParameters StageInput (ℕ → Bool))
    (AR : Deterministic StageParameters StageInput (ℕ → ℝ))
    (AU : Deterministic Unit (Finset ℕ × (ℕ → ℝ)) (ℕ → ℝ))
    (p : Pairing N) (hp : ValidPairing G x k.q p)
    (hgroups : ∀ v, (formGroups k.q (st v)).groups = (p v).map (image ids))
    (hblocks : ∃ B : BlockAssignment p, ValidBlocks k.ell B ∧
      ReportsBlocks ids (execute AB G k ids (stageInput G ids x p none
        (some (copyColor ids chi (LocalPairing.pick G x k.q p hp ids))) (fun _ => false) (fun _ => none))) B)
    (hcuts : ∀ B : BlockAssignment p, ValidBlocks k.ell B → ∃ s : Copy p → Copy p, ValidCuts B s ∧
      ReportsCuts (execute AC G k ids (stageInput G ids x p (some B)
        (some (copyColor ids chi (LocalPairing.pick G x k.q p hp ids))) (fun _ => false) (fun _ => none))) B s ∧
      cutCost G x k.q B s ≤ 8*penalty G x/(k.ell:ℝ)^2+72*k.q*totalWeight G x)
    (hround : ∀ B : BlockAssignment p, ValidBlocks k.ell B → ∀ s : Copy p → Copy p, ValidCuts B s →
      ∃ y : Sym2 (Fin N) → ℝ,
        ReportsWeights G ids (execute AR G k ids (stageInput G ids x p (some B) none (cutMarks B s) (fun v => some (side v)))) y ∧
        fractional G y ∧ (∀ v, load G y v ≤ 1) ∧
        (∀ e ∈ G.edgeSet, (x e = k.q → y e = 0 ∨ y e = 2*k.q) ∧ (x e ≠ k.q → y e = x e)) ∧
        potential G x-cutCost G x k.q B s ≤ potential G y)
    (hcleanup : ∀ y : Sym2 (Fin N) → ℝ, NonnegativeAssignment G y →
      ReportsWeights G ids (execute AU G () ids (weightInput G ids y)) (FasterDistributedMatching.ApproximateMatching.cleanup G y) ∧
      NonnegativeAssignment G (FasterDistributedMatching.ApproximateMatching.cleanup G y) ∧
      (∀ v, load G (FasterDistributedMatching.ApproximateMatching.cleanup G y) v ≤ 1/2) ∧
      potential G y ≤ potential G (FasterDistributedMatching.ApproximateMatching.cleanup G y)) :
    ∃ y : Sym2 (Fin N) → ℝ,
      Represents G ids y chi side ((stage AB AC AR AU k).program.output G () ids st (fun _ _ => false)) ∧
      fractional G y ∧ (∀ v, load G y v ≤ 1/2) ∧
      potential G x-(8*penalty G x/(k.ell:ℝ)^2+72*k.q*totalWeight G x) ≤ potential G y ∧
      ∀ K : ℕ, k.q = quantum (K+1) → fractional G x → DyadicLevels x (K+1) → DyadicLevels y K := by
  let st0 := fun v => formGroups k.q (st v)
  have hr0 := represents_formGroups G ids x chi side st hrep k.q
  obtain ⟨B,hB,hBout⟩ := hblocks
  let binp := stageInput G ids x p none (some (copyColor ids chi (LocalPairing.pick G x k.q p hp ids))) (fun _ => false) (fun _ => none)
  let bout := execute AB G k ids binp
  let stB := fun v => storeBlocks (st0 v) (bout v)
  have hbInput : (fun v => blockInput (ids v) (st0 v)) = binp :=
    funext (blocks_input_eq G ids hi x k.q p hp chi side st0 hr0 hgroups)
  have hbRun : (blocks AB k).program.output G () ids st0 (fun _ _ => false) = stB := by
    funext v
    rw [blocks_output,hbInput]
  have hrB := represents_storeBlocks G ids x chi side st0 hr0 bout
  have hgB : ∀ v, (stB v).groups = (p v).map (image ids) := hgroups
  have hlB : ∀ v, (stB v).leaders = (stageInput G ids x p (some B) none (fun _ => false) (fun _ => none) v).leader :=
    stored_blocks_leaders G ids hi x k.q p hp chi side st0 hr0 hgroups bout B hBout
  obtain ⟨s,hs,hCout,hCost⟩ := hcuts B hB
  let cinp := stageInput G ids x p (some B) (some (copyColor ids chi (LocalPairing.pick G x k.q p hp ids))) (fun _ => false) (fun _ => none)
  let cout := execute AC G k ids cinp
  let stC := fun v => storeCuts (stB v) (cout v)
  have hcInput : (fun v => cutInput (ids v) (stB v)) = cinp :=
    funext (cuts_input_eq G ids hi x k.q p hp chi side stB hrB hgB B hlB)
  have hcRun : (cuts AC k).program.output G () ids stB (fun _ _ => false) = stC := by
    funext v
    rw [cuts_output,hcInput]
  have hrC := represents_storeCuts G ids x chi side stB hrB cout
  have hgC : ∀ v, (stC v).groups = (p v).map (image ids) := hgB
  have hlC : ∀ v, (stC v).leaders = (stageInput G ids x p (some B) none (fun _ => false) (fun _ => none) v).leader := hlB
  have hcutC : ∀ v, (stC v).cuts = (stageInput G ids x p (some B) none (cutMarks B s) (fun v => some (side v)) v).cut :=
    stored_cuts_function G ids hi x k.q p hp chi side stB hrB hgB cout B s hCout
  obtain ⟨z,hRout,hz,hzload,hzround,hzpotential⟩ := hround B hB s hs
  let rinp := stageInput G ids x p (some B) none (cutMarks B s) (fun v => some (side v))
  let rout := execute AR G k ids rinp
  let stR := fun v => storeWeights (stC v) (rout v)
  have hrInput : (fun v => roundingInput (ids v) (stC v)) = rinp :=
    funext (rounding_input_eq G ids hi x k.q p hp chi side stC hrC hgC B s hlC hcutC)
  have hrRun : (rounding AR k).program.output G () ids stC (fun _ _ => false) = stR := by
    funext v
    rw [rounding_output,hrInput]
  have hrR := represents_storeWeights G ids x chi side stC hrC z rout hRout
  have hzNonnegative : NonnegativeAssignment G z := ⟨fun e => (hz.1 e).1,hz.2.1⟩
  obtain ⟨hUout,hUnonnegative,hUload,hUpotential⟩ := hcleanup z hzNonnegative
  let uout := execute AU G () ids (weightInput G ids z)
  let stU := fun v => storeWeights (stR v) (uout v)
  have huInput : (fun v => ((stR v).neighbors,LocalWeights.mask (stR v).neighbors (stR v).values)) = weightInput G ids z := by
    funext v
    apply Prod.ext
    · exact hrR.neighbors v
    · rw [hrR.neighbors v]
      exact LocalWeights.mask_eq_weight G ids hi z _ hrR.weights v
  have huRun : (cleanupStep AU).program.output G () ids stR (fun _ _ => false) = stU := by
    funext v
    rw [cleanup_output,huInput]
  have hrU := represents_storeWeights G ids z chi side stR hrR _ uout hUout
  have hfull : (stage AB AC AR AU k).program.output G () ids st (fun _ _ => false) = stU := by
    funext v
    unfold stage
    rw [thenDo_output]
    change (thenDo (blocks AB k) (thenDo (cuts AC k) (thenDo (rounding AR k) (cleanupStep AU)))).program.output G () ids st0 (fun _ _ => false) v = _
    rw [thenDo_output,hbRun,thenDo_output,hcRun,thenDo_output,hrRun,huRun]
  refine ⟨FasterDistributedMatching.ApproximateMatching.cleanup G z,?_,fractional_of_load G _ hUnonnegative hUload,hUload,?_,?_⟩
  · rw [hfull]
    exact hrU
  · linarith
  · intro K hq hx hlevel
    apply cleanup_levels G K z
    apply rounding_levels G K x z hlevel hx hz
    simpa only [hq] using hzround

end BipartiteProgram

-- Solutions/Sol_bipartite_algorithms.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteProgram

abbrev initialAlgorithm := lemma_2_1.choose
abbrev colorAlgorithm (b : ℕ) := (lemma_3_3.2.2 b).choose
abbrev blockAlgorithm (b : ℕ) := (lemma_3_2 b).choose_spec.choose
abbrev cutAlgorithm := lemma_3_5.choose
abbrev roundingAlgorithm := lemma_3_6.choose
abbrev cleanupAlgorithm := lemma_3_7.choose
abbrev paletteExponent (b : ℕ) := (lemma_3_3.2.2 b).choose_spec.choose_spec.choose

def stageParameters (b : ℕ) (base : Bounds) (ell : ℕ) (q : ℝ) : StageParameters :=
  ⟨base,ell,2*(max 2 base.degree)^(paletteExponent b*ell),q⟩

lemma fixed_stage_correct (b : ℕ) {N : ℕ} (G : SimpleGraph (Fin N)) (k : StageParameters)
    (hell : 2 ≤ k.ell) (hq : 0 < k.q) (hb : boundedGraph G k.n k.degree)
    (ids : Fin N → ℕ) (hid : Identifiers k.n (b+1) ids)
    (side : Fin N → Bool) (hside : Bipartition G side)
    (x : Sym2 (Fin N) → ℝ) (hx : fractional G x) (hload : ∀ v, load G x v ≤ 1/2)
    (chi : Sym2 (Fin N) → ℕ) (st : Fin N → Memory) (hrep : Represents G ids x chi side st)
    (hcolors : ∀ (p : Pairing N) (hp : ValidPairing G x k.q p),
      ReusableColors G k.ell k.zeta (copyColor ids chi (LocalPairing.pick G x k.q p hp ids))) :
    ∃ y : Sym2 (Fin N) → ℝ,
      Represents G ids y chi side
        ((stage (blockAlgorithm b) cutAlgorithm roundingAlgorithm cleanupAlgorithm k).program.output G () ids st (fun _ _ => false)) ∧
      fractional G y ∧ (∀ v, load G y v ≤ 1/2) ∧
      potential G x-(8*penalty G x/(k.ell:ℝ)^2+72*k.q*totalWeight G x) ≤ potential G y ∧
      ∀ K : ℕ, k.q = BipartiteRounding.quantum (K+1) → fractional G x →
        BipartiteRounding.DyadicLevels x (K+1) → BipartiteRounding.DyadicLevels y K := by
  let p := LocalPairing.pairing G x k.q ids hid.1
  have hp := LocalPairing.pairing_valid G x k.q ids hid.1
  have hg := formGroups_correct G ids x chi side st hrep k.q hid.1
  apply stage_composition G ids hid.1 k x chi side st hrep (blockAlgorithm b) cutAlgorithm roundingAlgorithm cleanupAlgorithm p hp hg
  · have hspec := (lemma_3_2 b).choose_spec.choose_spec.choose_spec
    exact ((hspec.2.2.2 N G k hell hb x p hp ids hid).2
      (copyColor ids chi (LocalPairing.pick G x k.q p hp ids))
      (LocalPairing.reusable_separates G x k.q p hp k.ell k.zeta _ (hcolors p hp)))
  · intro B hB
    have hspec := lemma_3_5.choose_spec.choose_spec
    exact hspec.2.2 N G k hell hq hb x ⟨fun e => (hx.1 e).1,hx.2.1⟩ p hp B hB _ (hcolors p hp) ids hid.1
  · intro B hB s hs
    have hspec := lemma_3_6.choose_spec.choose_spec
    obtain ⟨y,trace,hout,hy,hl,hr,hpot,htrace⟩ := hspec.2.2 N G k hell hq hb side hside x hx hload p hp B hB s hs ids hid.1
    exact ⟨y,hout,hy,hl,hr,hpot⟩
  · intro y hy
    exact lemma_3_7.choose_spec.choose_spec.2 N G y hy ids hid.1

end BipartiteProgram

-- Solutions/Sol_bipartite_parameters.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteRounding

def initialExponent (D : ℕ) : ℕ := Nat.clog 2 (max 2 D)+1
def startExponent (D : ℕ) : ℕ := max 16 (initialExponent D+3)
def stageCount (D : ℕ) : ℕ := startExponent D-16
def blockLength (D : ℕ) : ℕ := ⌈256*Real.sqrt ((startExponent D:ℝ)+1)⌉₊

lemma start_large (D : ℕ) : 16 ≤ startExponent D := le_max_left _ _
lemma stages_identity (D : ℕ) : stageCount D+16 = startExponent D := by unfold stageCount; have h := start_large D; omega
lemma initial_le_start (D : ℕ) : initialExponent D+3 ≤ startExponent D := le_max_right _ _

lemma initial_quantum_bound (D : ℕ) : quantum (initialExponent D) ≤ 1/(2*(max 1 D:ℕ):ℝ) := by
  unfold quantum initialExponent
  apply one_div_le_one_div_of_le (by positivity)
  rw [pow_succ]
  have hh := Nat.le_pow_clog (by decide : 1 < 2) (max 2 D)
  have hmax : max 1 D ≤ max 2 D := max_le_max_right _ (by decide : 1 ≤ 2)
  have hp : (max 1 D:ℝ) ≤ (2:ℝ)^Nat.clog 2 (max 2 D) := by exact_mod_cast hmax.trans hh
  norm_cast
  linarith

lemma length_large (D : ℕ) : 2 ≤ blockLength D := by
  have hs : 1 ≤ Real.sqrt ((startExponent D:ℝ)+1) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    norm_num
  have hc := Nat.le_ceil (256*Real.sqrt ((startExponent D:ℝ)+1))
  have hcast : (2:ℝ) ≤ (blockLength D:ℝ) := by unfold blockLength; linarith
  exact_mod_cast hcast

lemma length_square (D : ℕ) : 65536*(stageCount D:ℝ) ≤ (blockLength D:ℝ)^2 := by
  have hc := Nat.le_ceil (256*Real.sqrt ((startExponent D:ℝ)+1))
  change 256*Real.sqrt ((startExponent D:ℝ)+1) ≤ (blockLength D:ℝ) at hc
  have hsq := Real.sq_sqrt (show 0 ≤ (startExponent D:ℝ)+1 by positivity)
  have hs := Real.sqrt_nonneg ((startExponent D:ℝ)+1)
  have hn : (stageCount D:ℝ) ≤ (startExponent D:ℝ) := by exact_mod_cast (show stageCount D ≤ startExponent D by unfold stageCount; omega)
  nlinarith

lemma clog_real_bound (D : ℕ) : (Nat.clog 2 (max 2 D):ℝ) ≤ degreeLog D+1 := by
  rw [←Real.natCeil_logb_natCast]
  norm_num only [Nat.cast_ofNat]
  have hlog : 0 ≤ Real.logb 2 (max 2 D:ℕ) := Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ max 2 D by omega))
  have hceil := Nat.ceil_lt_add_one hlog
  have hle : Real.logb 2 (max 2 D:ℕ) ≤ degreeLog D := by
    unfold degreeLog logTwo
    rw [Nat.cast_max,Nat.cast_ofNat]
    exact le_max_right _ _
  linarith

end BipartiteRounding

-- Solutions/Sol_bipartite_initialization.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteProgram
open BipartiteRounding

lemma initialization_represents {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
    (side : Fin N → Bool) (AF : Deterministic Bounds (Finset ℕ) (ℕ → ℝ)) (base : Bounds) (K : ℕ)
    (f : Sym2 (Fin N) → ℝ) (hf : ReportsWeights G ids (execute AF G base ids (neighborIDs G ids)) f) :
    Represents G ids (scaledDyadic G K f) (fun _ => 0) side
      ((initialization AF base K).program.output G () ids (fun v => (neighborIDs G ids v,side v)) (fun _ _ => false)) := by
  let st := (initialization AF base K).program.output G () ids (fun v => (neighborIDs G ids v,side v)) (fun _ _ => false)
  have he (v : Fin N) : st v = {emptyMemory (neighborIDs G ids v,side v) with values := fun j => if j ∈ (neighborIDs G ids v) then quantum (dyadicIndex K (execute AF G base ids (neighborIDs G ids) v j)+3) else 0} := by
    unfold st initialization
    rw [LocalTransform.transform_output,LocalTransform.freeze_output]
    rfl
  refine ⟨?_,?_,?_,?_⟩
  · intro v
    change (st v).neighbors = _
    rw [he]
    rfl
  · intro v
    change (st v).side = _
    rw [he]
    rfl
  · refine ⟨?_,?_⟩
    · intro e he
      exact if_neg he
    · intro u v huv
      have hneighbor : ids v ∈ neighborIDs G ids u := mem_image.mpr ⟨v,(SimpleGraph.mem_neighborFinset G u v).mpr huv,rfl⟩
      have hreverse : ids u ∈ neighborIDs G ids v := mem_image.mpr ⟨u,(SimpleGraph.mem_neighborFinset G v u).mpr huv.symm,rfl⟩
      change (st u).values (ids v) = _ ∧ (st v).values (ids u) = _
      rw [he u,he v]
      change (if ids v ∈ (neighborIDs G ids u) then _ else 0) = _ ∧ (if ids u ∈ (neighborIDs G ids v) then _ else 0) = _
      rw [if_pos hneighbor,if_pos hreverse,(hf.2 u v huv).1,(hf.2 u v huv).2]
      exact ⟨(if_pos (G.mem_edgeSet.mpr huv)).symm,(if_pos (G.mem_edgeSet.mpr huv)).symm⟩
  · intro u v huv
    change (st u).edgeColors (ids v) = 0
    rw [he]
    rfl

lemma coloring_represents {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
    (side : Fin N → Bool) (x : Sym2 (Fin N) → ℝ) (oldchi chi : Sym2 (Fin N) → ℕ)
    (st : Fin N → Memory) (hrep : Represents G ids x oldchi side st)
    (AZ : Deterministic (Bounds × ℕ) (Finset ℕ) (ℕ → ℕ)) (base : Bounds) (ell : ℕ)
    (hcol : ∀ u v, G.Adj u v → execute AZ G (base,ell) ids (neighborIDs G ids) u (ids v) = chi s(u,v)) :
    Represents G ids x chi side ((colorEdges AZ base ell).program.output G () ids st (fun _ _ => false)) := by
  have hinp : (fun v => (st v).neighbors) = neighborIDs G ids := funext hrep.neighbors
  have he (v : Fin N) : (colorEdges AZ base ell).program.output G () ids st (fun _ _ => false) v =
      {st v with edgeColors := execute AZ G (base,ell) ids (neighborIDs G ids) v} := by
    rw [colorEdges,LocalTransform.transform_output,LocalTransform.freeze_output]
    change {st v with edgeColors := execute AZ G (base,ell) ids (fun v => (st v).neighbors) v} = _
    rw [hinp]
  refine ⟨?_,?_,?_,?_⟩
  · intro v
    rw [he]
    exact hrep.neighbors v
  · intro v
    rw [he]
    exact hrep.sides v
  · have hvalues : (fun v => ((colorEdges AZ base ell).program.output G () ids st (fun _ _ => false) v).values) = (fun v => (st v).values) := by
      funext v
      rw [he]
    rw [hvalues]
    exact hrep.weights
  · intro u v huv
    rw [he]
    exact hcol u v huv

end BipartiteProgram

-- Solutions/Sol_stage_iteration.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteProgram
open BipartiteRounding

lemma dyadicLevels_mono {N : ℕ} (x : Sym2 (Fin N) → ℝ) {k K : ℕ}
    (h : DyadicLevels x k) (hk : k ≤ K) : DyadicLevels x K := by
  intro e
  rcases h e with hz|⟨i,hi,heq⟩
  · exact Or.inl hz
  · exact Or.inr ⟨i,hi.trans hk,heq⟩

lemma iteration_invariant {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
    (side : Fin N → Bool) (chi : Sym2 (Fin N) → ℕ) (st0 : Fin N → Memory)
    (A : ℕ → Deterministic Unit Memory Memory) (K n ell : ℕ)
    (x0 : Sym2 (Fin N) → ℝ) (hrep0 : Represents G ids x0 chi side st0)
    (hx0 : fractional G x0) (hl0 : ∀ v, load G x0 v ≤ 1/2) (hd0 : DyadicLevels x0 K)
    (hstep : ∀ t < n, ∀ (st : Fin N → Memory) (x : Sym2 (Fin N) → ℝ),
      Represents G ids x chi side st → fractional G x → (∀ v, load G x v ≤ 1/2) → DyadicLevels x (K-t) →
      ∃ y : Sym2 (Fin N) → ℝ,
        Represents G ids y chi side ((A t).program.output G () ids st (fun _ _ => false)) ∧
        fractional G y ∧ (∀ v, load G y v ≤ 1/2) ∧ DyadicLevels y (K-(t+1)) ∧
        potential G x-(optimum G:ℝ)*(16/(ell:ℝ)^2+72*quantum (K-t)) ≤ potential G y) :
    ∀ t ≤ n, ∃ x : Sym2 (Fin N) → ℝ,
      Represents G ids x chi side (LocalRepeat.configurations A G ids st0 t) ∧
      fractional G x ∧ (∀ v, load G x v ≤ 1/2) ∧ DyadicLevels x (K-t) ∧
      potential G x0-(optimum G:ℝ)*(16*t/(ell:ℝ)^2+72*∑ i ∈ range t, quantum (K-i)) ≤ potential G x := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨x0,hrep0,hx0,hl0,hd0,?_⟩
    simp
  | succ t ih =>
    intro ht
    obtain ⟨x,hrep,hx,hl,hd,hpot⟩ := ih (by omega)
    obtain ⟨y,hyrep,hy,hyl,hyd,hypot⟩ := hstep t (by omega) _ x hrep hx hl hd
    refine ⟨y,hyrep,hy,hyl,hyd,?_⟩
    rw [sum_range_succ,Nat.cast_add,Nat.cast_one]
    ring_nf at hpot hypot ⊢
    linarith

lemma iteration_retains {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
    (side : Fin N → Bool) (chi : Sym2 (Fin N) → ℕ) (st0 : Fin N → Memory)
    (A : ℕ → Deterministic Unit Memory Memory) (K n ell : ℕ)
    (hn : n+16 = K) (hell : 0 < ell) (hsquare : 65536*(n:ℝ) ≤ (ell:ℝ)^2)
    (x0 : Sym2 (Fin N) → ℝ) (hrep0 : Represents G ids x0 chi side st0)
    (hx0 : fractional G x0) (hl0 : ∀ v, load G x0 v ≤ 1/2) (hd0 : DyadicLevels x0 K)
    (hpot0 : (optimum G:ℝ)/128 ≤ potential G x0)
    (hstep : ∀ t < n, ∀ (st : Fin N → Memory) (x : Sym2 (Fin N) → ℝ),
      Represents G ids x chi side st → fractional G x → (∀ v, load G x v ≤ 1/2) → DyadicLevels x (K-t) →
      ∃ y : Sym2 (Fin N) → ℝ,
        Represents G ids y chi side ((A t).program.output G () ids st (fun _ _ => false)) ∧
        fractional G y ∧ (∀ v, load G y v ≤ 1/2) ∧ DyadicLevels y (K-(t+1)) ∧
        potential G x-(optimum G:ℝ)*(16/(ell:ℝ)^2+72*quantum (K-t)) ≤ potential G y) :
    ∃ x : Sym2 (Fin N) → ℝ,
      Represents G ids x chi side ((LocalRepeat.programs A n).program.output G () ids st0 (fun _ _ => false)) ∧
      fractional G x ∧ (∀ v, load G x v ≤ 1/2) ∧ DyadicLevels x 16 ∧
      (optimum G:ℝ)/256 ≤ potential G x := by
  obtain ⟨x,hrep,hx,hl,hd,hpot⟩ := iteration_invariant G ids side chi st0 A K n ell x0 hrep0 hx0 hl0 hd0 hstep n le_rfl
  have houtput : (LocalRepeat.programs A n).program.output G () ids st0 (fun _ _ => false) = LocalRepeat.configurations A G ids st0 n :=
    funext (LocalRepeat.repeat_output A G ids st0 n)
  refine ⟨x,?_,hx,hl,?_,?_⟩
  · rw [houtput]
    exact hrep
  · have hKn : K-n = 16 := by omega
    simpa only [hKn] using hd
  · have hq := quantum_sum_small K n hn.le
    have hdiv : 16*(n:ℝ)/(ell:ℝ)^2 ≤ 16/65536 := by
      apply (div_le_iff₀ (show 0 < (ell:ℝ)^2 by positivity)).mpr
      nlinarith
    have hsmall : 16*(n:ℝ)/(ell:ℝ)^2+72*(∑ t ∈ range n, quantum (K-t)) ≤ 1/256 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ (optimum G:ℝ) by positivity)
    linarith

end BipartiteProgram

-- Solutions/Sol_fractional_pipeline.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteProgram
open BipartiteRounding

def phaseParameters (b : ℕ) (base : Bounds) (t : ℕ) : StageParameters :=
  stageParameters b base (blockLength base.degree) (quantum (startExponent base.degree-t))

def phaseProgram (b : ℕ) (base : Bounds) (t : ℕ) : Deterministic Unit Memory Memory :=
  stage (blockAlgorithm b) cutAlgorithm roundingAlgorithm cleanupAlgorithm (phaseParameters b base t)

def fractionalPipeline (b : ℕ) (base : Bounds) : Deterministic Unit (Finset ℕ × Bool) Memory :=
  LocalSequence.sequence (initialization initialAlgorithm base (initialExponent base.degree))
    (thenDo (colorEdges (colorAlgorithm b) base (blockLength base.degree))
      (LocalRepeat.programs (phaseProgram b base) (stageCount base.degree))) (fun _ _ _ out => out)

def fractionalAlgorithm (b : ℕ) : Deterministic Bounds (Finset ℕ × Bool) Memory :=
  LocalFamily.select (fractionalPipeline b)

lemma fractional_pipeline_correct (b : ℕ) {N : ℕ} (G : SimpleGraph (Fin N)) (base : Bounds)
    (hb : boundedGraph G base.n base.degree) (side : Fin N → Bool) (hside : Bipartition G side)
    (ids : Fin N → ℕ) (hid : Identifiers base.n (b+1) ids) :
    ∃ (x : Sym2 (Fin N) → ℝ) (chi : Sym2 (Fin N) → ℕ),
      Represents G ids x chi side (execute (fractionalAlgorithm b) G base ids (fun v => (neighborIDs G ids v,side v))) ∧
      fractional G x ∧ (∀ v, load G x v ≤ 1/2) ∧ DyadicLevels x 16 ∧ (optimum G:ℝ)/256 ≤ potential G x := by
  let ell := blockLength base.degree
  let K := startExponent base.degree
  let n := stageCount base.degree
  have hell : 2 ≤ ell := length_large base.degree
  have hn : n+16 = K := stages_identity base.degree
  obtain ⟨f,hfout,hf,hfrange,hfweight⟩ := lemma_2_1.choose_spec.choose_spec.2.2 N G base hb ids hid.1
  have hflower : ∀ e ∈ G.edgeSet, quantum (initialExponent base.degree) ≤ f e := by
    intro e he
    exact (initial_quantum_bound base.degree).trans (hfrange e he).1
  let x0 := scaledDyadic G (initialExponent base.degree) f
  have hx0nonnegative : NonnegativeAssignment G x0 := scaledDyadic_nonnegative G _ f
  have hx0load : ∀ v, load G x0 v ≤ 1/2 := fun v => (scaledDyadic_load G _ f hf hflower v).trans (by norm_num)
  have hx0 : fractional G x0 := fractional_of_load G x0 hx0nonnegative hx0load
  have hd0 : DyadicLevels x0 K := dyadicLevels_mono x0 (scaledDyadic_levels G _ f hf hflower) (initial_le_start base.degree)
  have hp0 : (optimum G:ℝ)/128 ≤ potential G x0 := scaledDyadic_potential G _ f hf hflower hfweight
  let inp : Fin N → Finset ℕ × Bool := fun v => (neighborIDs G ids v,side v)
  let st0 := (initialization initialAlgorithm base (initialExponent base.degree)).program.output G () ids inp (fun _ _ => false)
  have hr0 : Represents G ids x0 (fun _ => 0) side st0 := initialization_represents G ids side initialAlgorithm base _ f hfout
  have hcolspec := (lemma_3_3.2.2 b).choose_spec.choose_spec.choose_spec
  obtain ⟨chi,hchiout,hproper,hroutes,hreuse⟩ := hcolspec.2.2.2 N G base ell hell hb ids hid
  let stZ := (colorEdges (colorAlgorithm b) base ell).program.output G () ids st0 (fun _ _ => false)
  have hrZ : Represents G ids x0 chi side stZ := coloring_represents G ids side x0 _ chi st0 hr0 _ base ell (fun u v h => (hchiout u v h).1)
  have hstep : ∀ t < n, ∀ (st : Fin N → Memory) (x : Sym2 (Fin N) → ℝ),
      Represents G ids x chi side st → fractional G x → (∀ v, load G x v ≤ 1/2) → DyadicLevels x (K-t) →
      ∃ y : Sym2 (Fin N) → ℝ,
        Represents G ids y chi side ((phaseProgram b base t).program.output G () ids st (fun _ _ => false)) ∧
        fractional G y ∧ (∀ v, load G y v ≤ 1/2) ∧ DyadicLevels y (K-(t+1)) ∧
        potential G x-(optimum G:ℝ)*(16/(ell:ℝ)^2+72*quantum (K-t)) ≤ potential G y := by
    intro t ht st x hrep hx hl hd
    let k := phaseParameters b base t
    have hkq : 0 < k.q := quantum_pos (K-t)
    have hkcolors (p : Pairing N) (hp : ValidPairing G x k.q p) :
        ReusableColors G k.ell k.zeta (copyColor ids chi (LocalPairing.pick G x k.q p hp ids)) :=
      hreuse x k.q p hp (LocalPairing.pick G x k.q p hp ids) (LocalPairing.pick_valid G x k.q p hp ids)
    obtain ⟨y,hyrep,hy,hyl,hypot,hyd⟩ := fixed_stage_correct b G k hell hkq hb ids hid side hside x hx hl chi st hrep hkcolors
    have hidx : K-t = (K-(t+1))+1 := by omega
    have hyd' : DyadicLevels y (K-(t+1)) := hyd _ (by change quantum (K-t) = _; rw [hidx]) hx (by rw [←hidx]; exact hd)
    refine ⟨y,hyrep,hy,hyl,hyd',?_⟩
    exact stage_loss_bound G x y hx hl ell (by exact_mod_cast (show 0 < ell by omega)) k.q hkq.le hypot
  obtain ⟨x,hrep,hx,hl,hd,hpot⟩ := iteration_retains G ids side chi stZ (phaseProgram b base) K n ell hn
    (by omega) (length_square base.degree) x0 hrZ hx0 hx0load hd0 hp0 hstep
  refine ⟨x,chi,?_,hx,hl,hd,hpot⟩
  have hrun : execute (fractionalAlgorithm b) G base ids inp =
      (LocalRepeat.programs (phaseProgram b base) n).program.output G () ids stZ (fun _ _ => false) := by
    funext v
    change (LocalFamily.select (fractionalPipeline b)).program.output G base ids inp (fun _ _ => false) v = _
    rw [LocalFamily.select_output]
    unfold fractionalPipeline
    rw [LocalSequence.sequence_output]
    change (thenDo (colorEdges (colorAlgorithm b) base ell) (LocalRepeat.programs (phaseProgram b base) n)).program.output G () ids st0 (fun _ _ => false) v = _
    rw [thenDo_output]
  rw [hrun]
  exact hrep

end BipartiteProgram

-- Solutions/Sol_matching_support_extraction.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteRounding
variable {N : ℕ} (G : SimpleGraph (Fin N))

lemma graph_cover_weight_bound (x : Sym2 (Fin N) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hload : ∀ v, load G x v ≤ 1) (M : SimpleGraph (Fin N))
    (hcover : ∀ e ∈ G.edgeSet, ∃ v, v ∈ e ∧ ∃ w, M.Adj v w) :
    totalWeight G x ≤ 2*(matchingSize M:ℝ) := by
  let S := M.edgeFinset.biUnion (fun e => e.toFinset)
  have hc : ∀ e ∈ G.edgeSet, ∃ v ∈ S, v ∈ e := by
    intro e he
    obtain ⟨v,hve,w,hvw⟩ := hcover e he
    exact ⟨v,mem_biUnion.mpr ⟨s(v,w),M.mem_edgeFinset.mpr (M.mem_edgeSet.mpr hvw),
      Sym2.mem_toFinset.mpr (Sym2.mem_mk_left _ _)⟩,hve⟩
  have hw := weight_vertex_cover G x hx S hc
  have hsum : (∑ v ∈ S, load G x v) ≤ (S.card:ℝ) := by
    calc
      _ ≤ ∑ _ ∈ S, (1:ℝ) := sum_le_sum (fun v _ => hload v)
      _ = _ := by simp
  have hs : S.card ≤ 2*M.edgeFinset.card := by
    calc
      _ ≤ ∑ e ∈ M.edgeFinset, e.toFinset.card := card_biUnion_le
      _ ≤ ∑ _ ∈ M.edgeFinset, (2:ℕ) := sum_le_sum (fun e _ => by rw [Sym2.card_toFinset]; split_ifs <;> omega)
      _ = _ := by simp [mul_comm]
  have hcast : (S.card:ℝ) ≤ 2*(matchingSize M:ℝ) := by exact_mod_cast hs
  linarith

lemma integral_support_extraction (x : Sym2 (Fin N) → ℝ) (hx : fractional G x)
    (hpotential : (optimum G:ℝ)/256 ≤ potential G x) (M : SimpleGraph (Fin N))
    (hM : Matching (supportGraph G x) M)
    (hcover : ∀ e ∈ (supportGraph G x).edgeSet, ∃ v, v ∈ e ∧ ∃ w, M.Adj v w) :
    Matching G M ∧ (optimum G:ℝ)/512 ≤ (matchingSize M:ℝ) := by
  refine ⟨⟨hM.1.trans (supportGraph_le G x),hM.2⟩,?_⟩
  have hload : ∀ v, load (supportGraph G x) x v ≤ 1 := by
    intro v
    -- All removed edges have value zero, hence the physical loads are unchanged.
    have heq : load (supportGraph G x) x v = load G x v := by
      unfold load RandomOrderCRS.fracDegree
      rw [SimpleGraph.incidenceFinset_eq_filter,SimpleGraph.incidenceFinset_eq_filter,support_edgeFinset,filter_filter]
      simp only [sum_filter]
      apply sum_congr rfl
      intro e _
      by_cases hz : x e = 0 <;> by_cases hv : v ∈ e <;> simp [hz,hv]
    rw [heq]
    exact hx.2.2 v
  have hw := graph_cover_weight_bound (supportGraph G x) x (fun e => (hx.1 e).1) hload M hcover
  rw [support_weight] at hw
  have hpen : 0 ≤ penalty G x := mul_nonneg (by norm_num) (sum_nonneg (fun v _ => sq_nonneg (load G x v)))
  unfold potential at hpotential
  linarith

end BipartiteRounding

-- Solutions/Sol_bipartite_matching_pipeline.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteProgram
open BipartiteRounding

abbrev extractionAlgorithm := bounded_degree_bipartite_maximal_matching.choose

def extractionInput (id : ℕ) (st : Memory) : Finset ℕ × Bool :=
  (st.neighbors.filter (fun j => 0 < st.values j),st.side)

def matchingPipeline (b : ℕ) (base : Bounds) : Deterministic Unit (Finset ℕ × Bool) (Option ℕ) :=
  LocalSequence.sequence (fractionalPipeline b base) (LocalTransform.freeze extractionAlgorithm 65536)
    (fun _ id _ st => extractionInput id st)

def matchingAlgorithm (b : ℕ) : Deterministic Bounds (Finset ℕ × Bool) (Option ℕ) :=
  LocalFamily.select (matchingPipeline b)

lemma extractionInput_eq {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (hi : Function.Injective ids)
    (x : Sym2 (Fin N) → ℝ) (hx : fractional G x) (chi : Sym2 (Fin N) → ℕ)
    (side : Fin N → Bool) (st : Fin N → Memory) (hrep : Represents G ids x chi side st) (v : Fin N) :
    extractionInput (ids v) (st v) = (neighborIDs (supportGraph G x) ids v,side v) := by
  apply Prod.ext
  · change (st v).neighbors.filter (fun j => 0 < (st v).values j) = _
    rw [hrep.neighbors v]
    ext j
    constructor
    · intro hj
      obtain ⟨hjn,hjpos⟩ := mem_filter.mp hj
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hjn
      have hadj := (SimpleGraph.mem_neighborFinset G v w).mp hw
      have hvalue : (st v).values (ids w) = x s(v,w) := (hrep.weights.2 v w hadj).1
      rw [hvalue] at hjpos
      exact mem_image.mpr ⟨w,(SimpleGraph.mem_neighborFinset (supportGraph G x) v w).mpr ⟨hadj,ne_of_gt hjpos⟩,rfl⟩
    · intro hj
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hj
      have hadj := (SimpleGraph.mem_neighborFinset (supportGraph G x) v w).mp hw
      refine mem_filter.mpr ⟨mem_image.mpr ⟨w,(SimpleGraph.mem_neighborFinset G v w).mpr hadj.1,rfl⟩,?_⟩
      have hvalue : (st v).values (ids w) = x s(v,w) := (hrep.weights.2 v w hadj.1).1
      rw [hvalue]
      exact lt_of_le_of_ne (hx.1 s(v,w)).1 hadj.2.symm
  · exact hrep.sides v

lemma matching_pipeline_correct (b : ℕ) {N : ℕ} (G : SimpleGraph (Fin N)) (base : Bounds)
    (hb : boundedGraph G base.n base.degree) (side : Fin N → Bool) (hside : Bipartition G side)
    (ids : Fin N → ℕ) (hid : Identifiers base.n (b+1) ids) :
    ∃ M : SimpleGraph (Fin N),
      ReportsMatching G ids (execute (matchingAlgorithm b) G base ids (fun v => (neighborIDs G ids v,side v))) M ∧
      (optimum G:ℝ)/512 ≤ (matchingSize M:ℝ) := by
  let inp := fun v => (neighborIDs G ids v,side v)
  let st := (fractionalPipeline b base).program.output G () ids inp (fun _ _ => false)
  obtain ⟨x,chi,hrep,hx,hl,hd,hpot⟩ := fractional_pipeline_correct b G base hb side hside ids hid
  have hprefix : execute (fractionalAlgorithm b) G base ids inp = st := by
    funext v
    exact LocalFamily.select_output (fractionalPipeline b) G base ids inp v
  rw [hprefix] at hrep
  let H := supportGraph G x
  have hHG : H ≤ G := supportGraph_le G x
  have hdegree : ∀ v, H.degree v ≤ 65536 := support_degree G x hx hd
  have hHside : Bipartition H side := fun u v h => hside u v h.1
  obtain ⟨M,hM,hcover⟩ := bounded_degree_bipartite_maximal_matching.choose_spec.2 N G H 65536 hHG hdegree side hHside ids hid.1
  have hinput : (fun v => extractionInput (ids v) (st v)) = (fun v => (neighborIDs H ids v,side v)) :=
    funext (extractionInput_eq G ids hid.1 x hx chi side st hrep)
  have hout : execute (matchingAlgorithm b) G base ids inp = execute extractionAlgorithm G 65536 ids (fun v => (neighborIDs H ids v,side v)) := by
    funext v
    change (LocalFamily.select (matchingPipeline b)).program.output G base ids inp (fun _ _ => false) v = _
    rw [LocalFamily.select_output]
    unfold matchingPipeline
    rw [LocalSequence.sequence_output,LocalTransform.freeze_output]
    change execute extractionAlgorithm G 65536 ids (fun v => extractionInput (ids v) (st v)) v = _
    rw [hinput]
  have hfinal := integral_support_extraction G x hx hpot M hM.1 hcover
  refine ⟨M,?_,hfinal.2⟩
  rw [hout]
  exact ⟨hfinal.1,hM.2⟩

lemma matching_pipeline_rounds (b : ℕ) (base : Bounds) : (matchingAlgorithm b).program.rounds base ≤
    (fractionalPipeline b base).program.rounds ()+1+7*(65536+1) := by
  change (fractionalPipeline b base).program.rounds ()+1+extractionAlgorithm.program.rounds 65536 ≤ _
  exact Nat.add_le_add_left (bounded_degree_bipartite_maximal_matching.choose_spec.1 65536) _

end BipartiteProgram

-- Solutions/Sol_block_mis.lean

open Classical Finset Polynomial
open FasterDistributedMatching.ApproximateMatching

noncomputable section
namespace BlockColorProof

variable {F : Type} [Field F] [Fintype F]

def poly {d : ℕ} (a : Fin d → F) : F[X] :=
  ∑ i : Fin d, monomial i.val (a i)

lemma poly_coeff {d : ℕ} (a : Fin d → F) (i : Fin d) : (poly a).coeff i.val = a i := by
  simp [poly,Polynomial.coeff_monomial,Fin.val_inj]

lemma poly_injective (d : ℕ) : Function.Injective (@poly F _ d) := by
  intro a b h
  funext i
  have hh := congrArg (fun p : F[X] => p.coeff i.val) h
  simpa only [poly_coeff] using hh

lemma degree_poly {d : ℕ} (a : Fin d → F) : (poly a).natDegree ≤ d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_monomial_le (a i)).trans (Nat.le_of_lt i.isLt)

lemma collisions {d : ℕ} (a b : Fin d → F) (hab : a ≠ b) :
    (univ.filter (fun x : F => (poly a).eval x = (poly b).eval x)).card ≤ d := by
  have hp : poly a - poly b ≠ 0 := sub_ne_zero.mpr (fun h => hab (poly_injective d h))
  have hsub : (univ.filter (fun x : F => (poly a).eval x = (poly b).eval x)) ⊆
      (poly a-poly b).roots.toFinset := by
    intro x hx
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hp).mpr
    change (poly a-poly b).eval x = 0
    rw [Polynomial.eval_sub,sub_eq_zero]
    exact (mem_filter.mp hx).2
  exact (card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' _).trans ((Polynomial.natDegree_sub_le _ _).trans
      (max_le (degree_poly a) (degree_poly b)))))

lemma separating_point {d k D : ℕ} (enc : Fin k ↪ (Fin d → F))
    (hsize : D*d < Fintype.card F) (c : Fin k) (ns : Finset (Fin k))
    (hns : ns.card ≤ D) (hself : c ∉ ns) :
    ∃ x : F, ∀ b ∈ ns, (poly (enc c)).eval x ≠ (poly (enc b)).eval x := by
  let bad := ns.biUnion fun b => univ.filter fun x : F => (poly (enc c)).eval x = (poly (enc b)).eval x
  have hbad : bad.card ≤ D*d := by
    calc
      _ ≤ ∑ b ∈ ns, (univ.filter fun x : F => (poly (enc c)).eval x = (poly (enc b)).eval x).card :=
        card_biUnion_le
      _ ≤ ∑ _ ∈ ns, d := by
        apply sum_le_sum
        intro b hb
        exact collisions (enc c) (enc b) (fun h => hself (enc.injective h ▸ hb))
      _ ≤ D*d := by simpa using Nat.mul_le_mul_right d hns
  have hproper : bad ≠ univ := by
    intro h
    rw [h,card_univ] at hbad
    omega
  have hex : ∃ x : F, x ∉ bad := by
    by_contra h
    apply hproper
    ext x
    simp only [mem_univ,iff_true]
    by_contra hx
    exact h ⟨x,hx⟩
  obtain ⟨x,hx⟩ := hex
  refine ⟨x,?_⟩
  intro b hb heq
  exact hx (mem_biUnion.mpr ⟨b,hb,mem_filter.mpr ⟨mem_univ x,heq⟩⟩)

def nextPalette (D k : ℕ) : ℕ := 4*(D*Nat.clog 2 k+1)^2

lemma separating_family (D k : ℕ) :
    ∃ S : Fin k → Finset (Fin (nextPalette D k)),
      ∀ (c : Fin k) (ns : Finset (Fin k)), ns.card ≤ D → c ∉ ns →
        ∃ i ∈ S c, ∀ b ∈ ns, i ∉ S b := by
  let d := Nat.clog 2 k
  obtain ⟨q,hprime,hq,hqu⟩ := Nat.exists_prime_lt_and_le_two_mul (D*d+1) (by omega)
  letI : Fact q.Prime := ⟨hprime⟩
  have hq2 : 2 ≤ q := hprime.two_le
  have hcard : Fintype.card (Fin k) ≤ Fintype.card (Fin d → ZMod q) := by
    simp only [Fintype.card_fin,Fintype.card_fun,ZMod.card]
    exact (Nat.le_pow_clog (by decide) k).trans (Nat.pow_le_pow_left hq2 d)
  obtain ⟨enc⟩ := Function.Embedding.nonempty_of_card_le hcard
  have hcard2 : Fintype.card (ZMod q × ZMod q) ≤ nextPalette D k := by
    simp only [Fintype.card_prod,ZMod.card]
    unfold nextPalette
    change q*q ≤ 4*(D*d+1)^2
    nlinarith
  let E : (ZMod q × ZMod q) ↪ Fin (nextPalette D k) :=
    (Fintype.equivFin (ZMod q × ZMod q)).toEmbedding.trans (Fin.castLEEmb hcard2)
  let S : Fin k → Finset (Fin (nextPalette D k)) := fun c =>
    univ.image fun x : ZMod q => E (x,(poly (enc c)).eval x)
  refine ⟨S,?_⟩
  intro c ns hns hc
  have hsize : D*d < Fintype.card (ZMod q) := by simpa using (by omega : D*d < q)
  obtain ⟨x,hx⟩ := separating_point enc hsize c ns hns hc
  refine ⟨E (x,(poly (enc c)).eval x),mem_image.mpr ⟨x,mem_univ x,rfl⟩,?_⟩
  intro b hb hmem
  obtain ⟨y,_,hy⟩ := mem_image.mp hmem
  have heq := E.injective hy
  have hyx : y = x := congrArg Prod.fst heq
  have hev := congrArg Prod.snd heq
  apply hx b hb
  simpa only [hyx] using hev.symm

def family (D k : ℕ) : Fin k → Finset (Fin (nextPalette D k)) :=
  (separating_family D k).choose

lemma family_spec (D k : ℕ) (c : Fin k) (ns : Finset (Fin k))
    (hns : ns.card ≤ D) (hc : c ∉ ns) :
    ∃ i ∈ family D k c, ∀ b ∈ ns, i ∉ family D k b :=
  (separating_family D k).choose_spec c ns hns hc

def finiteNeighbors (k : ℕ) (ns : Finset ℕ) (hns : ∀ b ∈ ns, b < k) : Finset (Fin k) :=
  ns.attach.image fun b => ⟨b.val,hns b.val b.property⟩

lemma finiteNeighbors_card (k : ℕ) (ns : Finset ℕ) (hns : ∀ b ∈ ns, b < k) :
    (finiteNeighbors k ns hns).card ≤ ns.card := by
  exact (card_image_le).trans_eq (card_attach)

lemma finiteNeighbors_mem (k : ℕ) (ns : Finset ℕ) (hns : ∀ b ∈ ns, b < k) (b : Fin k) :
    b ∈ finiteNeighbors k ns hns ↔ b.val ∈ ns := by
  constructor
  · intro hb
    obtain ⟨c,hc,heq⟩ := mem_image.mp hb
    exact (congrArg Fin.val heq) ▸ c.property
  · intro hb
    exact mem_image.mpr ⟨⟨b.val,hb⟩,mem_attach _ _,Fin.ext rfl⟩

def localReduce (D k c : ℕ) (ns : Finset ℕ) : ℕ :=
  if h : c < k ∧ ns.card ≤ D ∧ c ∉ ns ∧ ∀ b ∈ ns, b < k then
    let nsFin := finiteNeighbors k ns h.2.2.2
    let hc : (⟨c,h.1⟩ : Fin k) ∉ nsFin := by
      intro hm
      exact h.2.2.1 ((finiteNeighbors_mem k ns h.2.2.2 _).mp hm)
    ((family_spec D k ⟨c,h.1⟩ nsFin
      ((finiteNeighbors_card k ns h.2.2.2).trans h.2.1) hc).choose).val
  else 0

lemma localReduce_spec (D k c : ℕ) (ns : Finset ℕ)
    (h : c < k ∧ ns.card ≤ D ∧ c ∉ ns ∧ ∀ b ∈ ns, b < k) :
    ∃ i : Fin (nextPalette D k), localReduce D k c ns = i.val ∧
      i ∈ family D k ⟨c,h.1⟩ ∧ ∀ b (hb : b ∈ ns), i ∉ family D k ⟨b,h.2.2.2 b hb⟩ := by
  let nsFin := finiteNeighbors k ns h.2.2.2
  have hcard : nsFin.card ≤ D := (finiteNeighbors_card k ns h.2.2.2).trans h.2.1
  have hc : (⟨c,h.1⟩ : Fin k) ∉ nsFin := by
    intro hm
    exact h.2.2.1 ((finiteNeighbors_mem k ns h.2.2.2 _).mp hm)
  have hex := family_spec D k ⟨c,h.1⟩ nsFin hcard hc
  refine ⟨hex.choose,?_,hex.choose_spec.1,?_⟩
  · unfold localReduce
    rw [dif_pos h]
  · intro b hb
    exact hex.choose_spec.2 _ ((finiteNeighbors_mem k ns h.2.2.2 _).mpr hb)

lemma localReduce_lt (D k c : ℕ) (ns : Finset ℕ) : localReduce D k c ns < nextPalette D k := by
  unfold localReduce
  split_ifs
  · exact Fin.isLt _
  · unfold nextPalette
    positivity

lemma localReduce_distinct (D k c b : ℕ) (ns ms : Finset ℕ)
    (hc : c < k ∧ ns.card ≤ D ∧ c ∉ ns ∧ ∀ j ∈ ns, j < k)
    (hb : b < k ∧ ms.card ≤ D ∧ b ∉ ms ∧ ∀ j ∈ ms, j < k)
    (hbn : b ∈ ns) : localReduce D k c ns ≠ localReduce D k b ms := by
  obtain ⟨i,hi,hif,hin⟩ := localReduce_spec D k c ns hc
  obtain ⟨j,hj,hjf,hjn⟩ := localReduce_spec D k b ms hb
  intro heq
  have hij : i = j := Fin.ext (hi.symm.trans (heq.trans hj))
  exact hin b hbn (hij ▸ hjf)

lemma local_reduce_proper {V : Type} [Fintype V] (H : SimpleGraph V)
    (D k : ℕ) (col : V → ℕ) (hcol : Proper H k col)
    (hD : ∀ v, H.degree v ≤ D) :
    Proper H (nextPalette D k)
      (fun v => localReduce D k (col v) ((H.neighborFinset v).image col)) := by
  have hgood (v : V) : col v < k ∧ ((H.neighborFinset v).image col).card ≤ D ∧
      col v ∉ (H.neighborFinset v).image col ∧
      ∀ j ∈ (H.neighborFinset v).image col, j < k := by
    refine ⟨hcol.1 v,(card_image_le).trans ?_,?_,?_⟩
    · simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hD v
    · intro h
      obtain ⟨w,hw,heq⟩ := mem_image.mp h
      exact hcol.2 v w (by simpa using hw) heq.symm
    · intro j hj
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hj
      exact hcol.1 w
  refine ⟨fun v => localReduce_lt D k _ _,?_⟩
  intro v w hvw
  exact localReduce_distinct D k (col v) (col w) _ _ (hgood v) (hgood w)
    (mem_image.mpr ⟨w,by simpa using hvw,rfl⟩)

lemma nextPalette_bound (D k : ℕ) (hD : 2 ≤ D) (hk : 2 ≤ k) :
    nextPalette D k ≤ 16 * D^2 * (Nat.clog 2 k)^2 := by
  have hd : 1 ≤ Nat.clog 2 k := Nat.clog_pos (by decide) (by omega)
  unfold nextPalette
  have hm : 1 ≤ D * Nat.clog 2 k := by nlinarith
  nlinarith

lemma clog_nextPalette (D k : ℕ) (hD : 2 ≤ D) (hk : 2 ≤ k) :
    Nat.clog 2 (nextPalette D k) ≤ 4+2*Nat.clog 2 D+2*Nat.clog 2 (Nat.clog 2 k) := by
  apply Nat.clog_le_of_le_pow
  calc
    _ ≤ 16 * D^2 * (Nat.clog 2 k)^2 := nextPalette_bound D k hD hk
    _ ≤ 16 * (2^Nat.clog 2 D)^2 * (2^Nat.clog 2 (Nat.clog 2 k))^2 := by
      gcongr
      · exact Nat.le_pow_clog (by decide) _
      · exact Nat.le_pow_clog (by decide) _
    _ = _ := by
      simp only [pow_add,← pow_mul,Nat.mul_comm]
      norm_num

lemma polynomial_le_exponential (l : ℕ) (hl : 64 ≤ l) :
    (32*l)^4 ≤ 2^(l-1) := by
  induction l,hl using Nat.le_induction with
  | base => norm_num
  | succ l hl ih =>
    have hratio : (32*(l+1))^4 ≤ 2*(32*l)^4 := by
      have hsmall : 8*(l+1) ≤ 9*l := by omega
      have hp := Nat.pow_le_pow_left hsmall 4
      simp only [mul_pow] at hp
      norm_num at hp
      have hp' : 4096*(l+1)^4 ≤ 8192*l^4 := hp.trans
        (Nat.mul_le_mul_right _ (by decide : 6561 ≤ 8192))
      have hh : (l+1)^4 ≤ 2*l^4 := by omega
      calc
        _ = 32^4 * (l+1)^4 := by ring
        _ ≤ 32^4 * (2*l^4) := Nat.mul_le_mul_left _ hh
        _ = _ := by ring
    calc
      _ ≤ 2*(32*l)^4 := hratio
      _ ≤ 2*2^(l-1) := Nat.mul_le_mul_left 2 ih
      _ = _ := by rw [show l+1-1 = (l-1)+1 by omega,pow_succ]; omega

lemma clog_fourth_bound (d : ℕ) (hd : 2^64 ≤ d) :
    (32*Nat.clog 2 d)^4 ≤ d := by
  have hlog : 64 ≤ Nat.clog 2 d := by
    have ht : 2^63 < d := by omega
    have hh := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr ht
    omega
  have hp := polynomial_le_exponential (Nat.clog 2 d) hlog
  have hd1 : 1 < d := by omega
  have hpred := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hd1
  exact hp.trans (by simpa only [Nat.pred_eq_sub_one] using hpred.le)

lemma two_step_palette (D k : ℕ) (hD : 2 ≤ D) (hk : 2 ≤ k) :
    nextPalette D (nextPalette D k) ≤ max (D^64) (Nat.clog 2 k) := by
  let d := Nat.clog 2 k
  let a := Nat.clog 2 D
  let b := Nat.clog 2 d
  have ha : a ≤ D := Nat.clog_le_of_le_pow (show D ≤ 2^D from (Nat.lt_pow_self (by decide : 1 < 2)).le)
  have hd : 1 ≤ d := Nat.clog_pos (by decide) (by omega)
  have hlog : Nat.clog 2 (nextPalette D k) ≤ 4+2*a+2*b := clog_nextPalette D k hD hk
  have hnext : nextPalette D (nextPalette D k) ≤ 4*(D*(4+2*a+2*b)+1)^2 := by
    unfold nextPalette
    exact Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left
      (Nat.add_le_add_right (Nat.mul_le_mul_left D hlog) 1) 2)
  by_cases hsmall : d ≤ D^64
  · have hb : b ≤ 64*a := by
      apply Nat.clog_le_of_le_pow
      calc
        d ≤ D^64 := hsmall
        _ ≤ (2^a)^64 := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) D) 64
        _ = _ := by rw [← pow_mul,Nat.mul_comm]
    have hinner : D*(4+2*a+2*b)+1 ≤ 135*D^2 := by nlinarith
    have hbound : nextPalette D (nextPalette D k) ≤ 72900*D^4 := by
      calc
        _ ≤ 4*(D*(4+2*a+2*b)+1)^2 := hnext
        _ ≤ 4*(135*D^2)^2 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hinner 2)
        _ = _ := by ring
    have hconst : 72900 ≤ D^60 :=
      (by norm_num : 72900 ≤ 2^60).trans (Nat.pow_le_pow_left hD 60)
    apply le_trans _ (le_max_left _ _)
    calc
      _ ≤ 72900*D^4 := hbound
      _ ≤ D^60*D^4 := Nat.mul_le_mul_right _ hconst
      _ = _ := by rw [← pow_add]
  · have hlarge : 2^64 ≤ d := (Nat.pow_le_pow_left hD 64).trans (by omega)
    have hfour : (32*b)^4 ≤ d := clog_fourth_bound d hlarge
    have hD4 : D^4 ≤ d :=
      (Nat.pow_le_pow_right (by omega : 0 < D) (by decide : 4 ≤ 64)).trans (by omega)
    have hDpow : D ≤ D^4 := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < D) (by decide : 1 ≤ 4)
    have hDle : D ≤ d := hDpow.trans hD4
    have hab : a ≤ b := Nat.clog_mono_right 2 hDle
    have hb : 1 ≤ b := Nat.clog_pos (by decide) (by omega)
    have hinner : D*(4+2*a+2*b)+1 ≤ 16*D*b := by nlinarith
    have hbound : nextPalette D (nextPalette D k) ≤ 1024*D^2*b^2 := by
      calc
        _ ≤ 4*(D*(4+2*a+2*b)+1)^2 := hnext
        _ ≤ 4*(16*D*b)^2 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hinner 2)
        _ = _ := by ring
    have hsquare : (1024*D^2*b^2)^2 ≤ d^2 := by
      calc
        _ = D^4*(32*b)^4 := by ring
        _ ≤ D^4*d := Nat.mul_le_mul_left _ hfour
        _ ≤ d*d := Nat.mul_le_mul_right d hD4
        _ = _ := by ring
    have hlast : 1024*D^2*b^2 ≤ d := (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hsquare
    exact (hbound.trans hlast).trans (le_max_right _ _)

lemma nextPalette_mono (D : ℕ) : Monotone (nextPalette D) := by
  intro a b hab
  unfold nextPalette
  gcongr

lemma nextPalette_threshold (D : ℕ) (hD : 2 ≤ D) : nextPalette D (D^64) ≤ D^64 := by
  have hclog : Nat.clog 2 (D^64) ≤ 64*D := by
    apply Nat.clog_le_of_le_pow
    calc
      D^64 ≤ (2^D)^64 := Nat.pow_le_pow_left (Nat.lt_pow_self (by decide : 1 < 2)).le 64
      _ = _ := by rw [← pow_mul,Nat.mul_comm]
  have hinner : D*Nat.clog 2 (D^64)+1 ≤ 65*D^2 := by nlinarith
  have hconst : 16900 ≤ D^60 :=
    (by norm_num : 16900 ≤ 2^60).trans (Nat.pow_le_pow_left hD 60)
  calc
    _ = 4*(D*Nat.clog 2 (D^64)+1)^2 := rfl
    _ ≤ 4*(65*D^2)^2 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hinner 2)
    _ = 16900*D^4 := by ring
    _ ≤ D^60*D^4 := Nat.mul_le_mul_right _ hconst
    _ = _ := by rw [← pow_add]

def paddedNext (D k : ℕ) : ℕ := max (D^64) (nextPalette D k)

lemma paddedNext_mono (D : ℕ) : Monotone (paddedNext D) :=
  fun _ _ h => max_le_max_left _ (nextPalette_mono D h)

lemma paddedNext_twice (D k : ℕ) (hD : 2 ≤ D) (hk : 2 ≤ k) :
    paddedNext D (paddedNext D k) ≤ max (D^64) (Nat.clog 2 k) := by
  unfold paddedNext
  apply max_le (le_max_left _ _)
  by_cases h : nextPalette D k ≤ D^64
  · rw [max_eq_left h]
    exact (nextPalette_threshold D hD).trans (le_max_left _ _)
  · rw [max_eq_right (by omega : D^64 ≤ nextPalette D k)]
    exact two_step_palette D k hD hk

lemma clog_lt_self (n : ℕ) (hn : 2 ≤ n) : Nat.clog 2 n < n := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr ?_ |>.trans_lt (Nat.pred_lt (by omega))
  have hpow : n ≤ 2^(n-1) := by
    induction n,hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      rw [show n+1-1 = (n-1)+1 by omega,pow_succ]
      omega
  simpa only [Nat.pred_eq_sub_one] using hpow

def height (n : ℕ) : ℕ := if h : n ≤ 1 then 0 else 1+height (Nat.clog 2 n)
termination_by n
 decreasing_by exact clog_lt_self n (by omega)

lemma height_le_self (n : ℕ) : height n ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [height]
    split_ifs with hn
    · omega
    · have hlt := clog_lt_self n (by omega)
      have hh := ih _ hlt
      omega

lemma height_mono : Monotone height := by
  intro a b hab
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
    by_cases ha : a ≤ 1
    · rw [height,dif_pos ha]; exact Nat.zero_le _
    · have hb : ¬ b ≤ 1 := by omega
      have hea : height a = 1+height (Nat.clog 2 a) := by rw [height,dif_neg ha]
      have heb : height b = 1+height (Nat.clog 2 b) := by rw [height,dif_neg hb]
      rw [hea,heb]
      have hlt := clog_lt_self b (by omega)
      exact Nat.add_le_add_left (ih _ hlt (Nat.clog_mono_right 2 hab)) 1

lemma height_pow_two (n : ℕ) (hn : 1 ≤ n) : height (2^n) = 1+height n := by
  rw [height,dif_neg (by
    have h : 2 ≤ 2^n := by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hn
    omega),Nat.clog_pow 2 n (by decide)]

lemma square_le_two_pow (n : ℕ) (hn : 4 ≤ n) : n^2 ≤ 2^n := by
  induction n,hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    have hh : (n+1)^2 ≤ 2*n^2 := by nlinarith
    exact hh.trans (Nat.mul_le_mul_left 2 ih |>.trans_eq (by ring))

def tower (n : ℕ) : ℕ → ℕ
  | 0 => n
  | t+1 => 2^(tower n t)

lemma tower_ge (n t : ℕ) : n ≤ tower n t := by
  induction t with
  | zero => rfl
  | succ t ih => exact ih.trans (Nat.lt_pow_self (by decide : 1 < 2)).le

lemma height_tower (n t : ℕ) (hn : 1 ≤ n) : height (tower n t) = t+height n := by
  induction t with
  | zero => simp [tower]
  | succ t ih =>
    rw [tower,height_pow_two _ (hn.trans (tower_ge n t)),ih]
    omega

lemma power_le_tower (n B : ℕ) (hn : 2 ≤ n) : n^B ≤ tower n B := by
  induction B with
  | zero => simpa [tower] using (show 1 ≤ n by omega)
  | succ B ih =>
    cases B with
    | zero => simpa [tower] using (Nat.lt_pow_self (by decide : 1 < 2) : n < 2^n).le
    | succ B =>
      have ht : 4 ≤ tower n (B+1) := by
        change 4 ≤ 2^(tower n B)
        exact (by norm_num : 4 ≤ 2^2).trans (Nat.pow_le_pow_right (by decide) (hn.trans (tower_ge n B)))
      calc
        n^(B+1+1) = n^(B+1)*n := by rw [pow_succ]
        _ ≤ (tower n (B+1))^2 := by
          simpa only [pow_two] using Nat.mul_le_mul ih (tower_ge n (B+1))
        _ ≤ 2^(tower n (B+1)) := square_le_two_pow _ ht
        _ = _ := rfl

lemma height_power (n B : ℕ) (hn : 2 ≤ n) : height (n^B) ≤ height n+B := by
  have h := height_mono (power_le_tower n B hn)
  rw [height_tower n B (by omega)] at h
  omega

lemma clog_ceil_log (x : ℝ) (hx : 0 < x) :
    Nat.clog 2 ⌈x⌉₊ = ⌈logTwo x⌉₊ := by
  apply eq_of_forall_ge_iff
  intro j
  rw [Nat.clog_le_iff_le_pow (by decide : 1 < 2),Nat.ceil_le,Nat.ceil_le]
  rw [Nat.cast_pow,Nat.cast_ofNat]
  have h : logTwo x ≤ (j : ℝ) ↔ x ≤ (2 : ℝ)^(j : ℝ) :=
    Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hx
  simpa only [Real.rpow_natCast] using h.symm

lemma iterLog_height (fuel : ℕ) (x : ℝ) (hx : 0 < x) (hf : ⌈x⌉₊ ≤ fuel) :
    iterLog fuel x = height ⌈x⌉₊ := by
  induction fuel generalizing x with
  | zero =>
    have hh : 0 < ⌈x⌉₊ := Nat.ceil_pos.mpr hx
    omega
  | succ fuel ih =>
    by_cases hx1 : x ≤ 1
    · have hn : ⌈x⌉₊ ≤ 1 := Nat.ceil_le.mpr (by simpa using hx1)
      rw [iterLog,if_pos hx1,height,dif_pos hn]
    · have hn : ¬ ⌈x⌉₊ ≤ 1 := by
        intro h
        have hh := Nat.ceil_le.mp h
        norm_num at hh
        exact hx1 hh
      have hlog : 0 < logTwo x := Real.logb_pos (by norm_num) (by linarith)
      have hceil := clog_ceil_log x hx
      have hlt := clog_lt_self ⌈x⌉₊ (by omega)
      have hnext : ⌈logTwo x⌉₊ ≤ fuel := by omega
      rw [iterLog,if_neg hx1,ih _ hlog hnext]
      conv_rhs => rw [height,dif_neg hn]
      rw [← hceil]

lemma height_nat_iterLog (n : ℕ) : height n = iterLog n n := by
  by_cases hn : n = 0
  · subst n
    rw [height,dif_pos (by decide)]
    rfl
  · have h := iterLog_height n (n : ℝ) (by exact_mod_cast Nat.pos_of_ne_zero hn) (by simp)
    simpa using h.symm

lemma height_max (a b : ℕ) : height (max a b) = max (height a) (height b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h,max_eq_right (height_mono h)]
  · rw [max_eq_left h,max_eq_left (height_mono h)]

lemma height_two : height 2 = 1 := by
  rw [height,dif_neg (by decide)]
  change 1+height 1 = 1
  rw [height,dif_pos (by decide)]

lemma height_max_two (n : ℕ) : height (max 2 n) = logStar n := by
  rw [height_max,height_two,height_nat_iterLog]
  rfl

lemma height_ID_bound (n B : ℕ) : height ((max 2 n)^B) ≤ (B+1)*logStar n := by
  have hh := height_power (max 2 n) B (le_max_left _ _)
  rw [height_max_two] at hh
  have hpos : 1 ≤ logStar n := le_max_left _ _
  nlinarith

lemma palette_iterations (D k : ℕ) (hD : 2 ≤ D) :
    (paddedNext D)^[2*height k] (max (D^64) k) ≤ D^64 := by
  have hfix : paddedNext D (D^64) = D^64 := by
    exact max_eq_left (nextPalette_threshold D hD)
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k ≤ D^64
    · rw [max_eq_left hk,Function.iterate_fixed hfix]
    · have hk2 : 2 ≤ k := by
        have hsmall : 2 ≤ D^64 := by
          exact (by norm_num : 2 ≤ 2^64).trans (Nat.pow_le_pow_left hD 64)
        omega
      have hh : height k = 1+height (Nat.clog 2 k) := by
        rw [height,dif_neg (by omega)]
      rw [hh,show 2*(1+height (Nat.clog 2 k)) = 2*height (Nat.clog 2 k)+2 by omega,
        Function.iterate_add_apply,max_eq_right (by omega : D^64 ≤ k)]
      have htwo : (paddedNext D)^[2] k ≤ max (D^64) (Nat.clog 2 k) := paddedNext_twice D k hD hk2
      apply le_trans ((paddedNext_mono D).iterate (2*height (Nat.clog 2 k)) htwo)
      exact ih _ (clog_lt_self k hk2)

structure ColorParameters where
  degree : ℕ
  palette : ℕ

structure ColorState where
  degree : ℕ
  palette : ℕ
  color : ℕ

def colorProgram : Deterministic ColorParameters ℕ ℕ where
  program := {
    State := ColorState
    Msg := ℕ
    rounds := fun k => 2*height k.palette
    init := fun k _ col _ => ⟨k.degree,max (k.degree^64) k.palette,col⟩
    send := ColorState.color
    step := fun s msgs => ⟨s.degree,paddedNext s.degree s.palette,
      localReduce s.degree s.palette s.color msgs.toFinset⟩
    out := ColorState.color }
  tape_independent := by intros; rfl

lemma colorProgram_invariant {V : Type} [Fintype V] (H : SimpleGraph V)
    (k : ColorParameters) (ids initial : V → ℕ) (hinit : Proper H k.palette initial) (hD : ∀ v, H.degree v ≤ k.degree) (t : ℕ) :
    let run := colorProgram.program.run H k ids initial (fun _ _ => false)
    (∀ v, (run t v).degree = k.degree ∧
      (run t v).palette = (paddedNext k.degree)^[t] (max (k.degree^64) k.palette)) ∧
    Proper H ((paddedNext k.degree)^[t] (max (k.degree^64) k.palette))
      (fun v => (run t v).color) := by
  dsimp only
  induction t with
  | zero =>
    refine ⟨fun v => ⟨rfl,rfl⟩,fun v => (hinit.1 v).trans_le (le_max_right _ _),?_⟩
    intro v w hvw heq
    exact hinit.2 v w hvw heq
  | succ t ih =>
    obtain ⟨hstate,hproper⟩ := ih
    let run := colorProgram.program.run H k ids initial (fun _ _ => false)
    let Q := (paddedNext k.degree)^[t] (max (k.degree^64) k.palette)
    have hnew := local_reduce_proper H k.degree _ _ hproper hD
    have hstep (v : V) : (run (t+1) v).color =
        localReduce k.degree Q (run t v).color
          ((H.neighborFinset v).image (fun w => (run t w).color)) := by
      change localReduce (run t v).degree (run t v).palette (run t v).color
        (((univ.filter (H.Adj v)).val.map fun w => (run t w).color).toFinset) = _
      rw [(hstate v).1,(hstate v).2]
      rw [← Finset.image_toFinset,Finset.val_toFinset,← H.neighborFinset_eq_filter]
    constructor
    · intro v
      constructor
      · change (run t v).degree = k.degree
        exact (hstate v).1
      · change paddedNext (run t v).degree (run t v).palette = _
        rw [(hstate v).1,(hstate v).2,Function.iterate_succ_apply']
    · simp only [Function.iterate_succ_apply']
      constructor
      · intro v
        change (run (t+1) v).color < paddedNext k.degree Q
        rw [hstep]
        exact (hnew.1 v).trans_le (le_max_right _ _)
      · intro v w hvw
        change (run (t+1) v).color ≠ (run (t+1) w).color
        rw [hstep,hstep]
        exact hnew.2 v w hvw

lemma colorProgram_correct {V : Type} [Fintype V] (H : SimpleGraph V)
    (k : ColorParameters) (ids initial : V → ℕ) (hinit : Proper H k.palette initial) (hD2 : 2 ≤ k.degree) (hD : ∀ v, H.degree v ≤ k.degree) :
    Proper H (k.degree^64)
      (colorProgram.program.output H k ids initial (fun _ _ => false)) := by
  have h := colorProgram_invariant H k ids initial hinit hD (2*height k.palette)
  have hp := palette_iterations k.degree k.palette hD2
  exact ⟨fun v => (h.2.1 v).trans_le hp,h.2.2⟩

lemma colorProgram_rounds (D n B : ℕ) :
    colorProgram.program.rounds ⟨D,(max 2 n)^B⟩ ≤ 2*(B+1)*logStar n := by
  change 2*height ((max 2 n)^B) ≤ _
  have h := Nat.mul_le_mul_left 2 (height_ID_bound n B)
  simpa only [mul_assoc] using h


def greedy {V : Type} [Fintype V] (H : SimpleGraph V) (col : V → ℕ) : ℕ → Finset V
  | 0 => ∅
  | t+1 => greedy H col t ∪ univ.filter (fun v => col v = t ∧
      ∀ w, H.Adj v w → w ∉ greedy H col t)

lemma greedy_step {V : Type} [Fintype V] (H : SimpleGraph V) (col : V → ℕ) (t : ℕ) (v : V) :
    v ∈ greedy H col (t+1) ↔ v ∈ greedy H col t ∨
      (col v = t ∧ ∀ w, H.Adj v w → w ∉ greedy H col t) := by
  simp only [greedy,mem_union,mem_filter,mem_univ,true_and]

lemma greedy_mono {V : Type} [Fintype V] (H : SimpleGraph V) (col : V → ℕ) :
    Monotone (greedy H col) := by
  apply monotone_nat_of_le_succ
  intro t v hv
  exact (greedy_step H col t v).mpr (Or.inl hv)

lemma greedy_independent {V : Type} [Fintype V] (H : SimpleGraph V) (col : V → ℕ)
    (hc : ∀ v w, H.Adj v w → col v ≠ col w) (t : ℕ) :
    ∀ v ∈ greedy H col t, ∀ w ∈ greedy H col t, ¬ H.Adj v w := by
  induction t with
  | zero => simp [greedy]
  | succ t ih =>
    intro v hv w hw hvw
    rcases (greedy_step H col t v).mp hv with hold | hnew
    · rcases (greedy_step H col t w).mp hw with holdw | hneww
      · exact ih v hold w holdw hvw
      · exact hneww.2 v hvw.symm hold
    · rcases (greedy_step H col t w).mp hw with holdw | hneww
      · exact hnew.2 w hvw holdw
      · exact hc v w hvw (hnew.1.trans hneww.1.symm)

lemma greedy_dominates {V : Type} [Fintype V] (H : SimpleGraph V) (col : V → ℕ) (t : ℕ) :
    ∀ v, col v < t → v ∈ greedy H col t ∨ ∃ w, H.Adj v w ∧ w ∈ greedy H col t := by
  induction t with
  | zero => intro v hv; omega
  | succ t ih =>
    intro v hv
    by_cases hlt : col v < t
    · rcases ih v hlt with h | ⟨w,hw,hmem⟩
      · exact Or.inl (greedy_mono H col (Nat.le_succ t) h)
      · exact Or.inr ⟨w,hw,greedy_mono H col (Nat.le_succ t) hmem⟩
    · have heq : col v = t := by omega
      by_cases hn : ∀ w, H.Adj v w → w ∉ greedy H col t
      · exact Or.inl ((greedy_step H col t v).mpr (Or.inr ⟨heq,hn⟩))
      · push Not at hn
        obtain ⟨w,hw,hmem⟩ := hn
        exact Or.inr ⟨w,hw,greedy_mono H col (Nat.le_succ t) hmem⟩

structure MISState where
  colors : ColorState
  remaining : ℕ
  index : ℕ
  selected : Bool

def misProgram : Deterministic ColorParameters ℕ Bool where
  program := {
    State := MISState
    Msg := ℕ ⊕ Bool
    rounds := fun k => 2*height k.palette+k.degree^64
    init := fun k id initial _ =>
      ⟨colorProgram.program.init k id initial (fun _ => false),2*height k.palette,0,false⟩
    send := fun s => if 0 < s.remaining then Sum.inl s.colors.color else Sum.inr s.selected
    step := fun s msgs => if 0 < s.remaining then
      {s with remaining := s.remaining-1, colors := (colorProgram.program.step s.colors
        (msgs.filterMap fun m => match m with | .inl n => some n | .inr _ => none))}
      else {s with index := s.index+1, selected := (s.selected ||
        (decide (s.colors.color = s.index) && !decide (Sum.inr true ∈ msgs)))}
    out := MISState.selected }
  tape_independent := by intros; rfl

set_option backward.isDefEq.respectTransparency false in
lemma mis_prefix {V : Type} [Fintype V] (H : SimpleGraph V) (k : ColorParameters)
    (ids initial : V → ℕ) (t : ℕ) (ht : t ≤ 2*height k.palette) : ∀ v,
    misProgram.program.run H k ids initial (fun _ _ => false) t v =
      ⟨colorProgram.program.run H k ids initial (fun _ _ => false) t v,
        2*height k.palette-t,0,false⟩ := by
  induction t with
  | zero => intro v; rfl
  | succ t ih =>
    intro v
    have hpos : 0 < 2*height k.palette-t := by omega
    rw [SmoothedMIS.LocalAlg.run]
    simp only [ih (by omega)]
    simp only [misProgram]
    simp only [hpos,if_true,Multiset.filterMap_map,Function.comp_def]
    change (⟨colorProgram.program.step
      (colorProgram.program.run H k ids initial (fun _ _ => false) t v)
        (Multiset.filterMap (some ∘ (fun w => (colorProgram.program.run H k ids initial (fun _ _ => false) t w).color))
          (univ.filter (H.Adj v)).val),2*height k.palette-t-1,0,false⟩ : MISState) = _
    rw [Multiset.filterMap_eq_map]
    congr 1

lemma greedy_bool_update {V : Type} [Fintype V] (H : SimpleGraph V) (col : V → ℕ)
    (i : ℕ) (v : V) :
    (decide (v ∈ greedy H col i) || (decide (col v = i) &&
      !decide (Sum.inr true ∈ ((univ.filter (H.Adj v)).val.map fun w =>
        (Sum.inr (decide (w ∈ greedy H col i)) : ℕ ⊕ Bool))))) =
      decide (v ∈ greedy H col (i+1)) := by
  have hm : (Sum.inr true ∈ ((univ.filter (H.Adj v)).val.map fun w =>
      (Sum.inr (decide (w ∈ greedy H col i)) : ℕ ⊕ Bool))) ↔
        ∃ w, H.Adj v w ∧ w ∈ greedy H col i := by simp
  have hn : (∀ w, H.Adj v w → w ∉ greedy H col i) ↔
      ¬∃ w, H.Adj v w ∧ w ∈ greedy H col i := by aesop
  simp only [greedy_step,hn,hm]
  by_cases h₁ : v ∈ greedy H col i <;> by_cases h₂ : col v = i <;>
    by_cases h₃ : ∃ w, H.Adj v w ∧ w ∈ greedy H col i <;> simp [h₁,h₂,h₃]

lemma mis_greedy {V : Type} [Fintype V] (H : SimpleGraph V) (k : ColorParameters)
    (ids initial : V → ℕ) (i : ℕ) : ∀ v,
    misProgram.program.run H k ids initial (fun _ _ => false) (2*height k.palette+i) v =
      ⟨colorProgram.program.run H k ids initial (fun _ _ => false) (2*height k.palette) v,
        0,i,decide (v ∈ greedy H
          (colorProgram.program.output H k ids initial (fun _ _ => false)) i)⟩ := by
  induction i with
  | zero =>
    intro v
    simpa only [Nat.add_zero,Nat.sub_self,greedy,notMem_empty,decide_false] using
      mis_prefix H k ids initial (2*height k.palette) le_rfl v
  | succ i ih =>
    intro v
    rw [show 2*height k.palette+(i+1) = (2*height k.palette+i)+1 by omega,SmoothedMIS.LocalAlg.run]
    simp only [ih]
    simp only [misProgram,Nat.lt_irrefl,if_false]
    change (⟨_,0,i+1,_⟩ : MISState) = _
    congr 1
    exact greedy_bool_update H _ i v

lemma mis_correct {V : Type} [Fintype V] (H : SimpleGraph V) (k : ColorParameters)
    (ids initial : V → ℕ) (hinit : Proper H k.palette initial)
    (hD2 : 2 ≤ k.degree) (hD : ∀ v, H.degree v ≤ k.degree) :
    (∀ v w, misProgram.program.output H k ids initial (fun _ _ => false) v = true →
      misProgram.program.output H k ids initial (fun _ _ => false) w = true → ¬ H.Adj v w) ∧
    ∀ v, misProgram.program.output H k ids initial (fun _ _ => false) v = true ∨
      ∃ w, H.Adj v w ∧ misProgram.program.output H k ids initial (fun _ _ => false) w = true := by
  let col := colorProgram.program.output H k ids initial (fun _ _ => false)
  have hcol := colorProgram_correct H k ids initial hinit hD2 hD
  have hout (v : V) : misProgram.program.output H k ids initial (fun _ _ => false) v =
      decide (v ∈ greedy H col (k.degree^64)) := by
    change (misProgram.program.run H k ids initial (fun _ _ => false)
      (2*height k.palette+k.degree^64) v).selected = _
    rw [mis_greedy]
  constructor
  · intro v w hv hw
    rw [hout,decide_eq_true_eq] at hv hw
    exact greedy_independent H col hcol.2 _ v hv w hw
  · intro v
    rcases greedy_dominates H col _ v (hcol.1 v) with h | ⟨w,hw,hs⟩
    · exact Or.inl (by rw [hout,decide_eq_true_eq]; exact h)
    · exact Or.inr ⟨w,hw,by rw [hout,decide_eq_true_eq]; exact hs⟩

end BlockColorProof

-- Solutions/Sol_bipartite_runtime_parameters.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteRounding

lemma degreeLog_one (D : ℕ) : 1 ≤ degreeLog D := le_max_left _ _
lemma doubleLog_one (D : ℕ) : 1 ≤ doubleLog D := le_max_left _ _

lemma exponent_real_bound (D : ℕ) : (startExponent D:ℝ) ≤ 16*degreeLog D := by
  have hc := clog_real_bound D
  have hL := degreeLog_one D
  unfold startExponent initialExponent
  rw [Nat.cast_max]
  push_cast
  apply max_le <;> linarith

lemma stageCount_real_bound (D : ℕ) : (stageCount D:ℝ) ≤ 16*degreeLog D := by
  have hn : stageCount D ≤ startExponent D := by unfold stageCount; omega
  exact (show (stageCount D:ℝ) ≤ (startExponent D:ℝ) by exact_mod_cast hn).trans (exponent_real_bound D)

lemma length_real_bound (D : ℕ) : (blockLength D:ℝ) ≤ 2048*Real.sqrt (degreeLog D) := by
  have hL := degreeLog_one D
  have hK := exponent_real_bound D
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ 256*Real.sqrt ((startExponent D:ℝ)+1) by positivity)).le
  change (blockLength D:ℝ) ≤ 256*Real.sqrt ((startExponent D:ℝ)+1)+1 at hceil
  have hrad : (startExponent D:ℝ)+1 ≤ 25*degreeLog D := by linarith
  have hroot := Real.sqrt_le_sqrt hrad
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 25)] at hroot
  norm_num at hroot
  have hs : 1 ≤ Real.sqrt (degreeLog D) := Real.one_le_sqrt.mpr hL
  linarith

lemma length_log_bound (D : ℕ) : 1 ≤ logTwo (blockLength D:ℝ) ∧
    logTwo (blockLength D:ℝ) ≤ 12*doubleLog D := by
  have hL := degreeLog_one D
  have hJ := doubleLog_one D
  have hlen := length_large D
  have hell : (2:ℝ) ≤ blockLength D := by exact_mod_cast hlen
  have hlow : 1 ≤ logTwo (blockLength D:ℝ) :=
    (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ) < 2) (by linarith)).mpr (by simpa using hell)
  have hsqrt : Real.sqrt (degreeLog D) ≤ degreeLog D := Real.sqrt_le_self_iff.mpr (Or.inr hL)
  have hbound : (blockLength D:ℝ) ≤ 2048*degreeLog D := (length_real_bound D).trans (by linarith)
  have hlog : logTwo (blockLength D:ℝ) ≤ logTwo (2048*degreeLog D) :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) hbound
  have h2048 : logTwo 2048 = 11 := by
    change Real.logb 2 (2048:ℝ) = 11
    rw [show (2048:ℝ) = 2^11 by norm_num,Real.logb_pow]
    norm_num
  have hmul : logTwo (2048*degreeLog D) = 11+logTwo (degreeLog D) := by
    unfold logTwo
    rw [Real.logb_mul (by norm_num) (by linarith : degreeLog D ≠ 0)]
    change logTwo 2048+logTwo (degreeLog D) = _
    rw [h2048]
    rfl
  rw [hmul] at hlog
  have hlogL : logTwo (degreeLog D) ≤ doubleLog D := le_max_right _ _
  exact ⟨hlow,by linarith⟩

lemma length_linear_bound (D : ℕ) : blockLength D ≤ 4096*(max 2 D) := by
  let X := max 2 D
  have hX : 2 ≤ X := le_max_left _ _
  have hc : Nat.clog 2 X ≤ X := (BlockColorProof.clog_lt_self X hX).le
  have hK : startExponent D ≤ 8*X := by
    unfold startExponent initialExponent
    change max 16 (Nat.clog 2 X+1+3) ≤ _
    apply max_le <;> omega
  have hs : Real.sqrt ((startExponent D:ℝ)+1) ≤ (startExponent D:ℝ)+1 :=
    Real.sqrt_le_self_iff.mpr (Or.inr (by have h : 0 ≤ (startExponent D:ℝ) := Nat.cast_nonneg _; linarith))
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ 256*Real.sqrt ((startExponent D:ℝ)+1) by positivity)).le
  change (blockLength D:ℝ) ≤ 256*Real.sqrt ((startExponent D:ℝ)+1)+1 at hceil
  have hKr : (startExponent D:ℝ) ≤ 8*(X:ℝ) := by exact_mod_cast hK
  have hXr : (2:ℝ) ≤ X := by exact_mod_cast hX
  have hh : (blockLength D:ℝ) ≤ 4096*(X:ℝ) := by linarith
  exact_mod_cast hh

end BipartiteRounding

-- Solutions/Sol_bipartite_palette_runtime.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteRounding
open BlockColorProof

lemma height_le_clog (n : ℕ) : height n ≤ 1+Nat.clog 2 n := by
  rw [height]
  split_ifs with hn
  · omega
  · have h := height_le_self (Nat.clog 2 n)
    omega

lemma logStar_degree_bound (D : ℕ) : (logStar D:ℝ) ≤ doubleLog D+4 := by
  let X := max 2 D
  let c := Nat.clog 2 X
  have hX : 2 ≤ X := le_max_left _ _
  have hL := degreeLog_one D
  have hJ := doubleLog_one D
  have hc : (c:ℝ) ≤ degreeLog D+1 := clog_real_bound D
  have hpad : max 2 (c:ℝ) ≤ 2*degreeLog D := max_le (by linarith) (by linarith)
  have hlog : logTwo (max 2 (c:ℝ)) ≤ logTwo (2*degreeLog D) :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith [le_max_left 2 (c:ℝ)]) hpad
  have hmul : logTwo (2*degreeLog D) = 1+logTwo (degreeLog D) := by
    unfold logTwo
    rw [Real.logb_mul (by norm_num) (by linarith : degreeLog D ≠ 0)]
    norm_num
  rw [hmul] at hlog
  have hlogL : logTwo (degreeLog D) ≤ doubleLog D := le_max_right _ _
  have hLc : degreeLog c ≤ doubleLog D+1 := by
    unfold degreeLog
    apply max_le <;> linarith
  have hcc : (Nat.clog 2 c:ℝ) ≤ doubleLog D+2 := by
    have hh := clog_real_bound c
    have hm : (Nat.clog 2 c:ℝ) ≤ (Nat.clog 2 (max 2 c):ℝ) := by exact_mod_cast Nat.clog_mono_right 2 (le_max_right 2 c)
    linarith
  have hheight : logStar D ≤ 2+Nat.clog 2 c := by
    rw [←height_max_two]
    change height X ≤ _
    rw [height,dif_neg (by omega : ¬X ≤ 1)]
    change 1+height c ≤ 2+Nat.clog 2 c
    have hh := height_le_clog c
    omega
  have hcast : (logStar D:ℝ) ≤ 2+(Nat.clog 2 c:ℝ) := by exact_mod_cast hheight
  linarith

def paletteLogConstant (a : ℕ) : ℕ := 4096*a+9

lemma palette_logStar_bound (a D : ℕ) :
    (logStar (2*(max 2 D)^(a*blockLength D)):ℝ) ≤ (paletteLogConstant a:ℝ)*doubleLog D := by
  let X := max 2 D
  let Z := 2*X^(a*blockLength D)
  let k := 4096*a+1
  let c := k+2
  have hX : 2 ≤ X := le_max_left _ _
  have hclog : Nat.clog 2 X ≤ X := (clog_lt_self X hX).le
  have hell := length_linear_bound D
  have hprod : Nat.clog 2 X*blockLength D ≤ X*(4096*X) := Nat.mul_le_mul hclog hell
  have hExp : 1+Nat.clog 2 X*(a*blockLength D) ≤ k*X^2 := by
    have h := Nat.mul_le_mul_left a hprod
    have hXsq : 1 ≤ X^2 := by nlinarith
    dsimp [k]
    nlinarith
  have hk : k ≤ X^k := by
    exact (Nat.lt_pow_self (n:=k) (by decide : 1 < 2)).le.trans (Nat.pow_le_pow_left hX k)
  have hExp' : k*X^2 ≤ X^c := by
    dsimp [c]
    rw [pow_add]
    exact Nat.mul_le_mul_right _ hk
  have hZ : Z ≤ 2^(X^c) := by
    calc
      Z ≤ 2*(2^Nat.clog 2 X)^(a*blockLength D) :=
        Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) X) _)
      _ = 2^(1+Nat.clog 2 X*(a*blockLength D)) := by
        rw [pow_add,pow_one]
        exact congrArg (fun n : ℕ => 2*n) (pow_mul 2 (Nat.clog 2 X) (a*blockLength D)).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide : 0 < 2) (hExp.trans hExp')
  have hZtwo : 2 ≤ Z := by
    have hp : 0 < X^(a*blockLength D) := pow_pos (by omega) _
    dsimp [Z]
    omega
  have hpow : 1 ≤ X^c := by have hp : 0 < X^c := pow_pos (by omega) _; omega
  have hh := height_mono hZ
  rw [height_pow_two (X^c) hpow] at hh
  have hp := height_power X c hX
  have hXheight : height X = logStar D := height_max_two D
  rw [hXheight] at hp
  have hZheight : height Z = logStar Z := by rw [←height_max_two,max_eq_right hZtwo]
  rw [hZheight] at hh
  have hNat : logStar Z ≤ logStar D+c+1 := by omega
  have hreal : (logStar Z:ℝ) ≤ (logStar D:ℝ)+(c:ℝ)+1 := by exact_mod_cast hNat
  have hstar := logStar_degree_bound D
  have hJ := doubleLog_one D
  change (logStar Z:ℝ) ≤ _
  unfold paletteLogConstant
  dsimp [c,k] at hreal
  push_cast at hreal ⊢
  have ha0 : 0 ≤ (a:ℝ) := Nat.cast_nonneg _
  nlinarith

end BipartiteRounding

-- Solutions/Sol_bipartite_time_domination.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteRounding

def stageWork (a D : ℕ) : ℝ := (blockLength D:ℝ)*
  ((logTwo (blockLength D:ℝ))^2+logTwo (blockLength D:ℝ)*(logStar (2*(max 2 D)^(a*blockLength D)):ℝ)+1)

lemma degree_three_halves (D : ℕ) : (degreeLog D)^(3/2:ℝ) = degreeLog D*Real.sqrt (degreeLog D) := by
  rw [show (3/2:ℝ) = 1+1/2 by norm_num,Real.rpow_add (by linarith [degreeLog_one D]),Real.rpow_one,←Real.sqrt_eq_rpow]

lemma stageWork_one (a D : ℕ) : 1 ≤ stageWork a D := by
  have hell : (2:ℝ) ≤ blockLength D := by exact_mod_cast length_large D
  have hl := (length_log_bound D).1
  have hS : 0 ≤ (logStar (2*(max 2 D)^(a*blockLength D)):ℝ) := Nat.cast_nonneg _
  unfold stageWork
  nlinarith [sq_nonneg (logTwo (blockLength D:ℝ)),mul_nonneg (by linarith : 0 ≤ logTwo (blockLength D:ℝ)) hS]

lemma total_stageWork_bound (a D : ℕ) :
    (stageCount D:ℝ)*stageWork a D ≤
      32768*(145+12*(paletteLogConstant a:ℝ))*(degreeLog D)^(3/2:ℝ)*(doubleLog D)^2 := by
  let L := degreeLog D
  let J := doubleLog D
  let l := logTwo (blockLength D:ℝ)
  let S : ℝ := logStar (2*(max 2 D)^(a*blockLength D))
  let P : ℝ := paletteLogConstant a
  have hL : 1 ≤ L := degreeLog_one D
  have hJ : 1 ≤ J := doubleLog_one D
  have hl : 1 ≤ l := (length_log_bound D).1
  have hlup : l ≤ 12*J := (length_log_bound D).2
  have hS : 0 ≤ S := Nat.cast_nonneg _
  have hSup : S ≤ P*J := palette_logStar_bound a D
  have hP : 0 ≤ P := Nat.cast_nonneg _
  have hl0 : 0 ≤ l := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hlSq : l^2 ≤ 144*J^2 := by
    have hh := mul_self_le_mul_self hl0 hlup
    nlinarith
  have hcross : l*S ≤ 12*P*J^2 := by
    have hh := mul_le_mul hlup hSup hS (show 0 ≤ 12*J by positivity)
    nlinarith
  have hbracket : l^2+l*S+1 ≤ (145+12*P)*J^2 := by nlinarith
  have hbracket0 : 0 ≤ l^2+l*S+1 := by positivity
  have he := length_real_bound D
  have hn := stageCount_real_bound D
  have hwork : stageWork a D ≤ 2048*Real.sqrt L*((145+12*P)*J^2) :=
    mul_le_mul he hbracket hbracket0 (by positivity)
  have hprod := mul_le_mul hn hwork (show 0 ≤ stageWork a D from by linarith [stageWork_one a D])
    (show 0 ≤ 16*L by positivity)
  rw [degree_three_halves]
  change _ ≤ 32768*(145+12*P)*(L*Real.sqrt L)*J^2
  nlinarith

lemma time_basic_bounds (n D : ℕ) : 1 ≤ matchingTime n D ∧ degreeLog D ≤ matchingTime n D ∧
    Real.sqrt (degreeLog D)*(logStar n:ℝ) ≤ matchingTime n D := by
  have hL := degreeLog_one D
  have hJ := doubleLog_one D
  have hs : 1 ≤ Real.sqrt (degreeLog D) := Real.one_le_sqrt.mpr hL
  have hterm : degreeLog D ≤ (degreeLog D)^(3/2:ℝ)*(doubleLog D)^2 := by
    rw [degree_three_halves]
    have hJ2 : 1 ≤ (doubleLog D)^2 := by nlinarith
    have hh := mul_le_mul hs hJ2 (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0 ≤ Real.sqrt (degreeLog D))
    have hscaled := mul_le_mul_of_nonneg_left hh (by linarith : 0 ≤ degreeLog D)
    nlinarith
  have hsecond : 0 ≤ Real.sqrt (degreeLog D)*(logStar n:ℝ) := by positivity
  have hfirst : 0 ≤ (degreeLog D)^(3/2:ℝ)*(doubleLog D)^2 := by positivity
  unfold matchingTime
  exact ⟨by linarith,by linarith,by linarith⟩

lemma time_domination (a n D : ℕ) (F Z B K : ℝ) (hF : 0 ≤ F) (hZ : 0 ≤ Z) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    F*degreeLog D+Z*(blockLength D:ℝ)*(logStar n:ℝ)+B*(stageCount D:ℝ)*stageWork a D+K ≤
      (F+2048*Z+32768*(145+12*(paletteLogConstant a:ℝ))*B+K)*matchingTime n D := by
  have ht := time_basic_bounds n D
  have hFterm := mul_le_mul_of_nonneg_left ht.2.1 hF
  have hZlen := mul_le_mul_of_nonneg_right (length_real_bound D) (show 0 ≤ (logStar n:ℝ) by positivity)
  have hZterm := mul_le_mul_of_nonneg_left (hZlen.trans
    (by nlinarith [ht.2.2] : 2048*Real.sqrt (degreeLog D)*(logStar n:ℝ) ≤ 2048*matchingTime n D)) hZ
  have hstage := total_stageWork_bound a D
  have htime : (degreeLog D)^(3/2:ℝ)*(doubleLog D)^2 ≤ matchingTime n D :=
    le_add_of_nonneg_right (by positivity)
  have hcoeff : 0 ≤ 32768*(145+12*(paletteLogConstant a:ℝ)) := by positivity
  have hstageTime : (stageCount D:ℝ)*stageWork a D ≤ 32768*(145+12*(paletteLogConstant a:ℝ))*matchingTime n D := by
    calc
      _ ≤ (32768*(145+12*(paletteLogConstant a:ℝ)))*((degreeLog D)^(3/2:ℝ)*(doubleLog D)^2) := by nlinarith [hstage]
      _ ≤ _ := mul_le_mul_of_nonneg_left htime hcoeff
  have hBterm := mul_le_mul_of_nonneg_left hstageTime hB
  have hKterm := mul_le_mul_of_nonneg_left ht.1 hK
  nlinarith

end BipartiteRounding

-- Solutions/Sol_bipartite_phase_runtime.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteProgram
open BipartiteRounding

lemma budget_real_upper (t : ℕ) (C f : ℝ) (hC : 0 ≤ C) (hf : 0 ≤ f) (ht : t ≤ budget C f) :
    (t:ℝ) ≤ C*f+1 := by
  have hh := (Nat.ceil_lt_add_one (mul_nonneg hC hf)).le
  exact (show (t:ℝ) ≤ (budget C f:ℝ) by exact_mod_cast ht).trans hh

lemma stageWork_dominates (a D : ℕ) : (blockLength D:ℝ) ≤ stageWork a D ∧
    (blockLength D:ℝ)*(1+(logStar (2*(max 2 D)^(a*blockLength D)):ℝ)) ≤ stageWork a D := by
  have hl := (length_log_bound D).1
  have hS : 0 ≤ (logStar (2*(max 2 D)^(a*blockLength D)):ℝ) := Nat.cast_nonneg _
  have hell : 0 ≤ (blockLength D:ℝ) := Nat.cast_nonneg _
  unfold stageWork
  constructor
  · nlinarith [sq_nonneg (logTwo (blockLength D:ℝ)),mul_nonneg (by linarith : 0 ≤ logTwo (blockLength D:ℝ)) hS]
  · have hb : 1+(logStar (2*(max 2 D)^(a*blockLength D)):ℝ) ≤
        (logTwo (blockLength D:ℝ))^2+logTwo (blockLength D:ℝ)*(logStar (2*(max 2 D)^(a*blockLength D)):ℝ)+1 := by nlinarith
    exact mul_le_mul_of_nonneg_left hb hell

lemma stage_runtime_generic
    (AB : Deterministic StageParameters StageInput (ℕ → Option Key))
    (AC : Deterministic StageParameters StageInput (ℕ → Bool))
    (AR : Deterministic StageParameters StageInput (ℕ → ℝ))
    (AU : Deterministic Unit (Finset ℕ × (ℕ → ℝ)) (ℕ → ℝ))
    (k : StageParameters) (CB CC CR W : ℝ) (T : ℕ)
    (hB : 0 ≤ CB) (hC : 0 ≤ CC) (hR : 0 ≤ CR) (hW : 1 ≤ W)
    (hdB : (k.ell:ℝ)*(1+(logStar k.zeta:ℝ)) ≤ W) (hdR : (k.ell:ℝ) ≤ W)
    (hb : AB.program.rounds k ≤ budget CB ((k.ell:ℝ)*(1+(logStar k.zeta:ℝ))))
    (hc : AC.program.rounds k ≤ budget CC W)
    (hr : AR.program.rounds k ≤ budget CR k.ell) (hu : AU.program.rounds () ≤ T) :
    (stage AB AC AR AU k).program.rounds () ≤ budget (CB+CC+CR+(T:ℝ)+8) W := by
  have hb' : (AB.program.rounds k:ℝ) ≤ CB*W+1 := by
    have hh := budget_real_upper _ CB _ hB (by positivity : 0 ≤ (k.ell:ℝ)*(1+(logStar k.zeta:ℝ))) hb
    nlinarith [mul_le_mul_of_nonneg_left hdB hB]
  have hc' : (AC.program.rounds k:ℝ) ≤ CC*W+1 := budget_real_upper _ CC W hC (by linarith) hc
  have hr' : (AR.program.rounds k:ℝ) ≤ CR*W+1 := by
    have hh := budget_real_upper _ CR (k.ell:ℝ) hR (by positivity) hr
    nlinarith [mul_le_mul_of_nonneg_left hdR hR]
  have hu' : (AU.program.rounds ():ℝ) ≤ (T:ℝ) := by exact_mod_cast hu
  have htW := mul_le_mul_of_nonneg_left hW (show 0 ≤ (T:ℝ) by positivity)
  have hreal : ((stage AB AC AR AU k).program.rounds ():ℝ) ≤ (CB+CC+CR+(T:ℝ)+7)*W := by
    rw [stage_rounds]
    push_cast
    nlinarith
  have hcast := hreal.trans (show (CB+CC+CR+(T:ℝ)+7)*W ≤ (CB+CC+CR+(T:ℝ)+8)*W by nlinarith)
  exact_mod_cast hcast.trans (Nat.le_ceil ((CB+CC+CR+(T:ℝ)+8)*W))

lemma phase_runtime_bound (b : ℕ) (base : Bounds) (t : ℕ) :
    (phaseProgram b base t).program.rounds () ≤
      budget ((lemma_3_2 b).choose_spec.choose_spec.choose+
        lemma_3_5.choose_spec.choose+lemma_3_6.choose_spec.choose+(lemma_3_7.choose_spec.choose:ℝ)+8)
        (stageWork (paletteExponent b) base.degree) := by
  have hB := (lemma_3_2 b).choose_spec.choose_spec.choose_spec
  have hC := lemma_3_5.choose_spec.choose_spec
  have hR := lemma_3_6.choose_spec.choose_spec
  have hU := lemma_3_7.choose_spec.choose_spec
  let k := phaseParameters b base t
  have hell : 2 ≤ k.ell := length_large base.degree
  have hdom := stageWork_dominates (paletteExponent b) base.degree
  exact stage_runtime_generic (blockAlgorithm b) cutAlgorithm roundingAlgorithm cleanupAlgorithm k _ _ _ _ _
    hB.1.le hC.1.le hR.1.le (stageWork_one _ _) hdom.2 hdom.1
    (hB.2.2.1 k hell) (hC.2.1 k hell) (hR.2.1 k hell) hU.1

end BipartiteProgram

-- Solutions/Sol_bipartite_runtime.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteProgram
open BipartiteRounding

abbrev initializationConstant := lemma_2_1.choose_spec.choose
abbrev coloringConstant (b : ℕ) := (lemma_3_3.2.2 b).choose_spec.choose
abbrev phaseConstant (b : ℕ) : ℝ := (lemma_3_2 b).choose_spec.choose_spec.choose+
  lemma_3_5.choose_spec.choose+lemma_3_6.choose_spec.choose+(lemma_3_7.choose_spec.choose:ℝ)+8

lemma phaseConstant_pos (b : ℕ) : 0 < phaseConstant b := by
  have hB := (lemma_3_2 b).choose_spec.choose_spec.choose_spec.1
  have hC := lemma_3_5.choose_spec.choose_spec.1
  have hR := lemma_3_6.choose_spec.choose_spec.1
  have hT : 0 ≤ (lemma_3_7.choose_spec.choose:ℝ) := Nat.cast_nonneg _
  unfold phaseConstant
  linarith

lemma matching_rounds_real (b : ℕ) (base : Bounds) :
    ((matchingAlgorithm b).program.rounds base:ℝ) ≤
      initializationConstant*degreeLog base.degree+
      coloringConstant b*(blockLength base.degree:ℝ)*(logStar base.n:ℝ)+
      (phaseConstant b+2)*(stageCount base.degree:ℝ)*stageWork (paletteExponent b) base.degree+458764 := by
  let ell := blockLength base.degree
  let n := stageCount base.degree
  let W := stageWork (paletteExponent b) base.degree
  let F := initializationConstant
  let Z := coloringConstant b
  let B := phaseConstant b
  have hF := lemma_2_1.choose_spec.choose_spec
  have hZ := (lemma_3_3.2.2 b).choose_spec.choose_spec.choose_spec
  have hell : 2 ≤ ell := length_large base.degree
  have hW : 1 ≤ W := stageWork_one _ _
  have hFreal : (initialAlgorithm.program.rounds base:ℝ) ≤ F*degreeLog base.degree+1 :=
    budget_real_upper _ F _ hF.1.le (by linarith [degreeLog_one base.degree]) (hF.2.1 base)
  have hZreal : ((colorAlgorithm b).program.rounds (base,ell):ℝ) ≤ Z*(ell:ℝ)*(logStar base.n:ℝ)+1 := by
    have hh := budget_real_upper _ Z ((ell:ℝ)*(logStar base.n:ℝ)) hZ.1.le (by positivity) (hZ.2.2.1 base ell hell)
    nlinarith
  have hphase (t : ℕ) : ((phaseProgram b base t).program.rounds ():ℝ) ≤ B*W+1 :=
    budget_real_upper _ B W (phaseConstant_pos b).le (by linarith) (phase_runtime_bound b base t)
  have hsum : (∑ t ∈ range n, ((phaseProgram b base t).program.rounds ():ℝ)) ≤ (n:ℝ)*(B*W+1) := by
    calc
      _ ≤ ∑ _ ∈ range n, (B*W+1) := sum_le_sum (fun t _ => hphase t)
      _ = _ := by simp; ring
  have hround := matching_pipeline_rounds b base
  have hroundR : ((matchingAlgorithm b).program.rounds base:ℝ) ≤ (initialAlgorithm.program.rounds base:ℝ)+
      ((colorAlgorithm b).program.rounds (base,ell):ℝ)+(n:ℝ)+
      (∑ t ∈ range n, ((phaseProgram b base t).program.rounds ():ℝ))+458762 := by
    have hcast : ((matchingAlgorithm b).program.rounds base:ℝ) ≤
        ((fractionalPipeline b base).program.rounds ():ℝ)+1+7*(65536+1) := by exact_mod_cast hround
    have heq : (fractionalPipeline b base).program.rounds () = initialAlgorithm.program.rounds base+1+
        ((colorAlgorithm b).program.rounds (base,ell)+1+(LocalRepeat.programs (phaseProgram b base) n).program.rounds ()) := rfl
    rw [heq,LocalRepeat.repeat_rounds] at hcast
    push_cast at hcast
    nlinarith
  have hnW := mul_le_mul_of_nonneg_left hW (show 0 ≤ (n:ℝ) by positivity)
  change _ ≤ F*degreeLog base.degree+Z*(ell:ℝ)*(logStar base.n:ℝ)+(B+2)*(n:ℝ)*W+458764
  nlinarith

lemma matching_runtime (b : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ base,
    (matchingAlgorithm b).program.rounds base ≤ budget C (matchingTime base.n base.degree) := by
  let F := initializationConstant
  let Z := coloringConstant b
  let B := phaseConstant b+2
  let P : ℝ := paletteLogConstant (paletteExponent b)
  let C := F+2048*Z+32768*(145+12*P)*B+458764
  have hF : 0 < F := lemma_2_1.choose_spec.choose_spec.1
  have hZ : 0 < Z := (lemma_3_3.2.2 b).choose_spec.choose_spec.choose_spec.1
  have hB : 0 < B := by have hh := phaseConstant_pos b; dsimp [B]; linarith
  have hP : 0 ≤ P := Nat.cast_nonneg _
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro base
  have hraw := matching_rounds_real b base
  have hdom := time_domination (paletteExponent b) base.n base.degree F Z B 458764 hF.le hZ.le hB.le (by norm_num)
  have hr : ((matchingAlgorithm b).program.rounds base:ℝ) ≤ C*matchingTime base.n base.degree := hraw.trans hdom
  exact_mod_cast hr.trans (Nat.le_ceil (C*matchingTime base.n base.degree))

end BipartiteProgram

-- Solutions/Sol_bipartite_approximation.lean
open FasterDistributedMatching.ApproximateMatching
open BipartiteProgram

/- Lemma 3.1, printed p.7 / PDF p.9, proof §§3.1--3.4.
The bipartition is part of each node's permitted local input. -/
theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ b : ℕ,
      ∃ (A : Deterministic Bounds (Finset ℕ × Bool) (Option ℕ)) (C : ℝ), 0 < C ∧
      (∀ k, A.program.rounds k ≤ budget C (matchingTime k.n k.degree)) ∧
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (k : Bounds), boundedGraph G k.n k.degree →
        ∀ side : Fin N → Bool, Bipartition G side →
        ∀ ids : Fin N → ℕ, Identifiers k.n (b + 1) ids →
          ∃ M : SimpleGraph (Fin N),
            ReportsMatching G ids
              (execute A G k ids (fun v => (neighborIDs G ids v, side v))) M ∧
            c * (optimum G : ℝ) ≤ (matchingSize M : ℝ)  := by
  refine ⟨1/512,by norm_num,?_⟩
  intro b
  obtain ⟨C,hC,hTime⟩ := matching_runtime b
  refine ⟨matchingAlgorithm b,C,hC,hTime,?_⟩
  intro N G base hb side hside ids hid
  obtain ⟨M,hout,hsize⟩ := matching_pipeline_correct b G base hb side hside ids hid
  exact ⟨M,hout,by linarith⟩

