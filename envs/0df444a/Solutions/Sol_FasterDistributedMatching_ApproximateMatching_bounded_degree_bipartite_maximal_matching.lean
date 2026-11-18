-- Prove2me | solution 1 for FasterDistributedMatching.ApproximateMatching.bounded_degree_bipartite_maximal_matching
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T21:52:15.800816+00:00
-- url     : https://prove2.me/submissions/8d80d364-bd1b-4ed3-9801-d5e8afe9393f

import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Local
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_StageData

-- Solutions/Sol_local_exchange.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace LocalExchange
variable {I O : Type}

def oneRound (f : ℕ → I → Multiset (ℕ × I) → O) : Deterministic Unit I O where
  program := {
    State := ℕ × I × Multiset (ℕ × I)
    Msg := ℕ × I
    rounds := fun _ => 1
    init := fun _ id inp _ => (id,inp,0)
    send := fun st => (st.1,st.2.1)
    step := fun st msgs => (st.1,st.2.1,msgs)
    out := fun st => f st.1 st.2.1 st.2.2 }
  tape_independent := by intros; rfl

lemma oneRound_output (f : ℕ → I → Multiset (ℕ × I) → O) {V : Type} [Fintype V]
    (H : SimpleGraph V) (ids : V → ℕ) (inp : V → I) (v : V) :
    (oneRound f).program.output H () ids inp (fun _ _ => false) v =
      f (ids v) (inp v) ((H.neighborFinset v).val.map (fun w => (ids w,inp w))) := by
  have hn : univ.filter (H.Adj v) = H.neighborFinset v := by ext w; simp
  change f (ids v) (inp v) ((univ.filter (H.Adj v)).val.map (fun w => (ids w,inp w))) = _
  rw [hn]

end LocalExchange

-- Solutions/Sol_local_neighbor_filter.lean

open Classical Finset
noncomputable section
namespace LocalExchange

def namedFilter {I : Type} (neighbors : Finset ℕ) (Q : ℕ → I → Prop) (msgs : Multiset (ℕ × I)) : Finset ℕ :=
  (msgs.toFinset.filter (fun r => r.1 ∈ neighbors ∧ Q r.1 r.2)).image Prod.fst

lemma namedFilter_correct {V I : Type} [Fintype V] (G H : SimpleGraph V) (hHG : H ≤ G)
    (ids : V → ℕ) (hi : Function.Injective ids) (inp : V → I) (v : V) (Q : ℕ → I → Prop)
    [DecidablePred (fun w => Q (ids w) (inp w))] :
    namedFilter ((H.neighborFinset v).image ids) Q ((G.neighborFinset v).val.map (fun w => (ids w,inp w))) =
      ((H.neighborFinset v).filter (fun w => Q (ids w) (inp w))).image ids := by
  ext j
  constructor
  · intro hj
    obtain ⟨r,hr,hrj⟩ := mem_image.mp hj
    obtain ⟨hrmsg,hrN,hrQ⟩ := mem_filter.mp hr
    obtain ⟨w,hw,heq⟩ := Multiset.mem_map.mp (Multiset.mem_toFinset.mp hrmsg)
    subst r
    obtain ⟨u,hu,he⟩ := mem_image.mp hrN
    have huw : u = w := hi he
    subst u
    exact mem_image.mpr ⟨w,mem_filter.mpr ⟨hu,hrQ⟩,hrj⟩
  · intro hj
    obtain ⟨w,hw,heq⟩ := mem_image.mp hj
    have hH := (SimpleGraph.mem_neighborFinset H v w).mp (mem_filter.mp hw).1
    have hG := (SimpleGraph.mem_neighborFinset G v w).mpr (hHG hH)
    refine mem_image.mpr ⟨(ids w,inp w),mem_filter.mpr ⟨?_,?_,(mem_filter.mp hw).2⟩,heq⟩
    · exact Multiset.mem_toFinset.mpr (Multiset.mem_map.mpr ⟨w,hG,rfl⟩)
    · exact mem_image.mpr ⟨w,(mem_filter.mp hw).1,rfl⟩

end LocalExchange

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

-- Solutions/Sol_bipartite_greedy_program.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteGreedy

@[ext] structure Memory where
  neighbors : Finset ℕ
  side : Bool
  partner : Option ℕ
  proposal : Option ℕ
  accepted : Option ℕ

def first (S : Finset ℕ) : Option ℕ := S.sort.head?

def statusStep (id : ℕ) (st : Memory) (msgs : Multiset (ℕ × Memory)) : Memory :=
  {st with proposal := if st.partner = none ∧ st.side = false then
      first (LocalExchange.namedFilter st.neighbors (fun _ other => other.partner = none) msgs) else none,accepted := none}

def proposalStep (id : ℕ) (st : Memory) (msgs : Multiset (ℕ × Memory)) : Memory :=
  {st with accepted := if st.partner = none ∧ st.side = true then
      first (LocalExchange.namedFilter st.neighbors (fun _ other => other.proposal = some id) msgs) else none}

def acceptStep (id : ℕ) (st : Memory) (msgs : Multiset (ℕ × Memory)) : Memory :=
  let partner := match st.partner with
    | some j => some j
    | none => if st.side = false then
      match st.proposal with
      | none => none
      | some j => if j ∈ LocalExchange.namedFilter st.neighbors (fun _ other => other.accepted = some id) msgs then some j else none
      else st.accepted
  {st with partner := partner,proposal := none,accepted := none}

def stepProgram : Deterministic Unit Memory Memory :=
  LocalSequence.sequence (LocalExchange.oneRound statusStep)
    (LocalSequence.sequence (LocalExchange.oneRound proposalStep) (LocalExchange.oneRound acceptStep)
      (fun _ _ _ out => out)) (fun _ _ _ out => out)

def initial (inp : Finset ℕ × Bool) : Memory := ⟨inp.1,inp.2,none,none,none⟩

def memoryProgram (D : ℕ) : Deterministic Unit (Finset ℕ × Bool) Memory :=
  LocalSequence.sequence (LocalTransform.pointwise (fun _ inp => initial inp))
    (LocalRepeat.programs (fun _ => stepProgram) D) (fun _ _ _ out => out)

def protocol (D : ℕ) : Deterministic Unit (Finset ℕ × Bool) (Option ℕ) :=
  LocalTransform.transform (memoryProgram D) (fun _ inp => inp) (fun _ _ st => st.partner)

lemma step_rounds : stepProgram.program.rounds () = 5 := rfl

lemma protocol_rounds (D : ℕ) : (protocol D).program.rounds () = 6*D+1 := by
  change (memoryProgram D).program.rounds () = _
  change 0+1+(LocalRepeat.programs (fun _ => stepProgram) D).program.rounds () = _
  rw [LocalRepeat.repeat_rounds]
  simp only [step_rounds,sum_const,card_range,smul_eq_mul]
  omega

end BipartiteGreedy

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

-- Solutions/Sol_bipartite_proposals.lean

open Classical Finset
noncomputable section
namespace BipartiteProposals
section Selection
variable {V : Type} [DecidableEq V] (ids : V → ℕ) (hi : Function.Injective ids)

def least (S : Finset V) : Option V := (LocalPairing.sortedBy S ids hi).head?

lemma least_mem (S : Finset V) (v : V) (hv : least ids hi S = some v) : v ∈ S := by
  apply (LocalPairing.mem_sortedBy S ids hi v).mp
  have hmem : v ∈ least ids hi S := by rw [hv]; exact Option.mem_def.mpr rfl
  exact List.mem_of_mem_head? hmem

lemma least_complete (S : Finset V) (hS : S.Nonempty) : ∃ v, least ids hi S = some v := by
  cases h : least ids hi S with
  | none =>
    have he : LocalPairing.sortedBy S ids hi = [] := List.head?_eq_none_iff.mp h
    obtain ⟨v,hv⟩ := hS
    have hv' := (LocalPairing.mem_sortedBy S ids hi v).mpr hv
    rw [he] at hv'
    exact (List.not_mem_nil hv').elim
  | some v => exact ⟨v,rfl⟩

lemma least_named (S : Finset V) : (least ids hi S).map ids = (S.image ids).sort.head? := by
  rw [least,←List.head?_map,LocalPairing.map_sortedBy]

end Selection

section Proposals
variable {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (side : V → Bool) (hside : ∀ u v, H.Adj u v → side u ≠ side v)
    (ids : V → ℕ) (hi : Function.Injective ids)

def Free (M : SimpleGraph V) (v : V) : Prop := ∀ w, ¬M.Adj v w

def freeNeighbors (M : SimpleGraph V) (v : V) : Finset V := (H.neighborFinset v).filter (Free M)

def propose (M : SimpleGraph V) (v : V) : Option V :=
  if Free M v ∧ side v = false then least ids hi (freeNeighbors H M v) else none

def accept (M : SimpleGraph V) (w : V) : Option V :=
  if Free M w ∧ side w = true then least ids hi (univ.filter (fun v => propose H side ids hi M v = some w)) else none

def Chosen (M : SimpleGraph V) (u v : V) : Prop :=
  propose H side ids hi M u = some v ∧ accept H side ids hi M v = some u

include hside in
lemma propose_spec (M : SimpleGraph V) (u v : V) (h : propose H side ids hi M u = some v) :
    Free M u ∧ Free M v ∧ H.Adj u v ∧ side u = false ∧ side v = true := by
  unfold propose at h
  split_ifs at h with hu
  · have hm := least_mem ids hi _ v h
    have hAdj := (SimpleGraph.mem_neighborFinset H u v).mp (mem_filter.mp hm).1
    have hneq := hside u v hAdj
    have hv : side v = true := by cases hvs : side v <;> simp_all
    exact ⟨hu.1,(mem_filter.mp hm).2,hAdj,hu.2,hv⟩

lemma accept_spec (M : SimpleGraph V) (u v : V) (h : accept H side ids hi M v = some u) :
    Chosen H side ids hi M u v := by
  unfold accept at h
  split_ifs at h with hv
  · have hm := least_mem ids hi _ u h
    exact ⟨(mem_filter.mp hm).2,by unfold accept; rw [if_pos hv]; exact h⟩

lemma propose_complete (M : SimpleGraph V) (v : V) (hv : Free M v) (hleft : side v = false)
    (hn : (freeNeighbors H M v).Nonempty) : ∃ w, propose H side ids hi M v = some w := by
  unfold propose
  rw [if_pos ⟨hv,hleft⟩]
  exact least_complete ids hi _ hn

include hside in
lemma accept_complete (M : SimpleGraph V) (u v : V) (hu : propose H side ids hi M u = some v) :
    ∃ w, accept H side ids hi M v = some w := by
  have hp := propose_spec H side hside ids hi M u v hu
  unfold accept
  rw [if_pos ⟨hp.2.1,hp.2.2.2.2⟩]
  exact least_complete ids hi _ ⟨u,mem_filter.mpr ⟨mem_univ _,hu⟩⟩

end Proposals
end BipartiteProposals

-- Solutions/Sol_matching_mate.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteProposals
variable {V : Type} [Fintype V] [DecidableEq V]
    (ids : V → ℕ) (hi : Function.Injective ids) (M : SimpleGraph V)

def mate (v : V) : Option V := least ids hi (M.neighborFinset v)

lemma mate_some (hM : ∀ u v w, M.Adj u v → M.Adj u w → v = w) (u v : V) :
    mate ids hi M u = some v ↔ M.Adj u v := by
  constructor
  · intro h
    exact (SimpleGraph.mem_neighborFinset M u v).mp (least_mem ids hi _ v h)
  · intro h
    obtain ⟨w,hw⟩ := least_complete ids hi (M.neighborFinset u)
      ⟨v,(SimpleGraph.mem_neighborFinset M u v).mpr h⟩
    have huw := (SimpleGraph.mem_neighborFinset M u w).mp (least_mem ids hi _ w hw)
    have heq := hM u w v huw h
    exact hw.trans (congrArg some heq)

lemma mate_none (u : V) : mate ids hi M u = none ↔ Free M u := by
  constructor
  · intro h w hw
    obtain ⟨v,hv⟩ := least_complete ids hi (M.neighborFinset u)
      ⟨w,(SimpleGraph.mem_neighborFinset M u w).mpr hw⟩
    change mate ids hi M u = some v at hv
    rw [h] at hv
    cases hv
  · intro h
    cases hm : mate ids hi M u with
    | none => rfl
    | some v =>
      have hv := (SimpleGraph.mem_neighborFinset M u v).mp (least_mem ids hi _ v hm)
      exact (h v hv).elim

lemma unique_graph_matching {N : ℕ} (G M : SimpleGraph (Fin N)) (hsub : M ≤ G)
    (hM : ∀ u v w, M.Adj u v → M.Adj u w → v = w) : Matching G M := by
  refine ⟨hsub,?_⟩
  intro e he f hf hne v hve hvf
  obtain ⟨u,hu⟩ := Sym2.mem_iff_exists.mp hve
  obtain ⟨w,hw⟩ := Sym2.mem_iff_exists.mp hvf
  have hvu : M.Adj v u := M.mem_edgeSet.mp (by rw [←hu]; exact e.property)
  have hvw : M.Adj v w := M.mem_edgeSet.mp (by rw [←hw]; exact f.property)
  have heq := hM v u w hvu hvw
  exact hne (Subtype.ext (hu.trans ((congrArg (fun z => s(v,z)) heq).trans hw.symm)))

lemma named_mate_reports {N : ℕ} (G M : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
    (hi : Function.Injective ids) (hsub : M ≤ G)
    (hM : ∀ u v w, M.Adj u v → M.Adj u w → v = w) :
    ReportsMatching G ids (fun v => (mate ids hi M v).map ids) M := by
  refine ⟨unique_graph_matching G M hsub hM,?_⟩
  intro v
  constructor
  · rw [Option.map_eq_none_iff,mate_none]
    rfl
  · intro j
    constructor
    · intro h
      obtain ⟨w,hw,hj⟩ := Option.map_eq_some_iff.mp h
      exact ⟨w,(mate_some ids hi M hM v w).mp hw,hj⟩
    · rintro ⟨w,hw,hj⟩
      dsimp only
      rw [(mate_some ids hi M hM v w).mpr hw]
      exact congrArg some hj

end BipartiteProposals

-- Solutions/Sol_bipartite_greedy_status.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteGreedy
open BipartiteProposals
section Reference
variable {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (side : V → Bool) (ids : V → ℕ) (hi : Function.Injective ids) (M : SimpleGraph V)

def reference (v : V) : Memory :=
  ⟨(H.neighborFinset v).image ids,side v,(mate ids hi M v).map ids,none,none⟩

def proposed (v : V) : Memory :=
  {reference H side ids hi M v with proposal := (propose H side ids hi M v).map ids}

def accepted (v : V) : Memory :=
  {proposed H side ids hi M v with accepted := (accept H side ids hi M v).map ids}

lemma reference_free (v : V) : (reference H side ids hi M v).partner = none ↔ Free M v := by
  change (mate ids hi M v).map ids = none ↔ _
  rw [Option.map_eq_none_iff,mate_none]

include hi in
lemma map_ids_some (o : Option V) (v : V) : o.map ids = some (ids v) ↔ o = some v := by
  cases o with
  | none => simp
  | some w => simp only [Option.map_some,Option.some.injEq,hi.eq_iff]

lemma status_correct (G : SimpleGraph V) (hHG : H ≤ G) (v : V) :
    statusStep (ids v) (reference H side ids hi M v)
      ((G.neighborFinset v).val.map (fun w => (ids w,reference H side ids hi M w))) = proposed H side ids hi M v := by
  have hfilter := LocalExchange.namedFilter_correct G H hHG ids hi (reference H side ids hi M) v (fun _ other => other.partner = none)
  have hpred : (H.neighborFinset v).filter (fun w => (reference H side ids hi M w).partner = none) = freeNeighbors H M v := by
    ext w
    simp only [freeNeighbors,mem_filter,reference_free]
  try dsimp only at hfilter
  rw [hpred] at hfilter
  have hfree := reference_free H side ids hi M v
  unfold statusStep proposed
  apply Memory.ext
  · rfl
  · rfl
  · rfl
  · change (if (mate ids hi M v).map ids = none ∧ side v = false then
        first (LocalExchange.namedFilter ((H.neighborFinset v).image ids) (fun _ other => other.partner = none)
          ((G.neighborFinset v).val.map (fun w => (ids w,reference H side ids hi M w)))) else none) =
        (propose H side ids hi M v).map ids
    rw [hfilter]
    simp only [Option.map_eq_none_iff,mate_none]
    unfold propose
    split_ifs with h
    · exact (least_named ids hi _).symm
    · rfl
  · rfl

end Reference
end BipartiteGreedy

-- Solutions/Sol_bipartite_greedy_proposal.lean

open Classical Finset
noncomputable section
namespace BipartiteGreedy
open BipartiteProposals

lemma proposal_correct {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (side : V → Bool) (hside : ∀ u v, H.Adj u v → side u ≠ side v)
    (ids : V → ℕ) (hi : Function.Injective ids) (M G : SimpleGraph V) (hHG : H ≤ G) (v : V) :
    proposalStep (ids v) (proposed H side ids hi M v)
      ((G.neighborFinset v).val.map (fun w => (ids w,proposed H side ids hi M w))) = accepted H side ids hi M v := by
  have hfilter := LocalExchange.namedFilter_correct G H hHG ids hi (proposed H side ids hi M) v (fun _ other => other.proposal = some (ids v))
  try dsimp only at hfilter
  have hpred : (H.neighborFinset v).filter (fun w => (proposed H side ids hi M w).proposal = some (ids v)) =
      univ.filter (fun w => propose H side ids hi M w = some v) := by
    ext w
    simp only [mem_filter,mem_univ,true_and]
    have hh : (proposed H side ids hi M w).proposal = some (ids v) ↔ propose H side ids hi M w = some v :=
      map_ids_some ids hi _ v
    rw [hh]
    constructor
    · exact And.right
    · intro hp
      exact ⟨(SimpleGraph.mem_neighborFinset H v w).mpr (propose_spec H side hside ids hi M w v hp).2.2.1.symm,hp⟩
  rw [hpred] at hfilter
  unfold proposalStep accepted
  apply Memory.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · change (if (mate ids hi M v).map ids = none ∧ side v = true then
        first (LocalExchange.namedFilter ((H.neighborFinset v).image ids) (fun _ other => other.proposal = some (ids v))
          ((G.neighborFinset v).val.map (fun w => (ids w,proposed H side ids hi M w)))) else none) =
        (accept H side ids hi M v).map ids
    rw [hfilter]
    simp only [Option.map_eq_none_iff,mate_none]
    unfold accept
    split_ifs with h
    · exact (least_named ids hi _).symm
    · rfl

end BipartiteGreedy

-- Solutions/Sol_bipartite_matching_growth.lean

open Classical Finset
noncomputable section
namespace BipartiteProposals
section Growth
variable {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (side : V → Bool) (hside : ∀ u v, H.Adj u v → side u ≠ side v)
    (ids : V → ℕ) (hi : Function.Injective ids)

def grow (M : SimpleGraph V) : SimpleGraph V where
  Adj u v := M.Adj u v ∨ Chosen H side ids hi M u v ∨ Chosen H side ids hi M v u
  symm := ⟨by
    intro u v h
    rcases h with h|h|h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩
  loopless := ⟨by
    intro u h
    rcases h with h|h|h
    · exact h.ne rfl
    · exact (propose_spec H side hside ids hi M u u h.1).2.2.1.ne rfl
    · exact (propose_spec H side hside ids hi M u u h.1).2.2.1.ne rfl⟩

include hside

lemma grow_contains (M : SimpleGraph V) : M ≤ grow H side hside ids hi M := fun _ _ h => Or.inl h

lemma grow_le (M : SimpleGraph V) (hM : M ≤ H) : grow H side hside ids hi M ≤ H := by
  intro u v h
  rcases h with h|h|h
  · exact hM h
  · exact (propose_spec H side hside ids hi M u v h.1).2.2.1
  · exact (propose_spec H side hside ids hi M v u h.1).2.2.1.symm

lemma free_before (M : SimpleGraph V) (v : V) (hv : Free (grow H side hside ids hi M) v) : Free M v :=
  fun w h => hv w (Or.inl h)

lemma chosen_not_free (M : SimpleGraph V) (u v : V) (h : Chosen H side ids hi M u v) :
    ¬Free (grow H side hside ids hi M) u ∧ ¬Free (grow H side hside ids hi M) v :=
  ⟨fun hu => hu v (Or.inr (Or.inl h)),fun hv => hv u (Or.inr (Or.inr h))⟩

lemma new_edge_free (M : SimpleGraph V) (u v : V)
    (h : Chosen H side ids hi M u v ∨ Chosen H side ids hi M v u) : Free M u ∧ Free M v := by
  rcases h with h|h
  · exact (propose_spec H side hside ids hi M u v h.1).imp_right (fun h => h.1)
  · have hh := propose_spec H side hside ids hi M v u h.1
    exact ⟨hh.2.1,hh.1⟩

lemma new_edge_unique (M : SimpleGraph V) (u v w : V)
    (hv : Chosen H side ids hi M u v ∨ Chosen H side ids hi M v u)
    (hw : Chosen H side ids hi M u w ∨ Chosen H side ids hi M w u) : v = w := by
  rcases hv with hv|hv <;> rcases hw with hw|hw
  · exact Option.some.inj (hv.1.symm.trans hw.1)
  · have hleft := (propose_spec H side hside ids hi M u v hv.1).2.2.2.1
    have hright := (propose_spec H side hside ids hi M w u hw.1).2.2.2.2
    exact (Bool.false_ne_true (hleft.symm.trans hright)).elim
  · have hright := (propose_spec H side hside ids hi M v u hv.1).2.2.2.2
    have hleft := (propose_spec H side hside ids hi M u w hw.1).2.2.2.1
    exact (Bool.false_ne_true (hleft.symm.trans hright)).elim
  · exact Option.some.inj (hv.2.symm.trans hw.2)

lemma grow_unique (M : SimpleGraph V)
    (hM : ∀ u v w, M.Adj u v → M.Adj u w → v = w) :
    ∀ u v w, (grow H side hside ids hi M).Adj u v → (grow H side hside ids hi M).Adj u w → v = w := by
  intro u v w hv hw
  rcases hv with hv|hv
  · rcases hw with hw|hw
    · exact hM u v w hv hw
    · exact ((new_edge_free H side hside ids hi M u w hw).1 v hv).elim
  · rcases hw with hw|hw
    · exact ((new_edge_free H side hside ids hi M u v hv).1 w hw).elim
    · exact new_edge_unique H side hside ids hi M u v w hv hw

lemma freeNeighbors_decrease (M : SimpleGraph V) (v : V) :
    freeNeighbors H (grow H side hside ids hi M) v ⊆ freeNeighbors H M v := by
  intro w hw
  exact mem_filter.mpr ⟨(mem_filter.mp hw).1,free_before H side hside ids hi M w (mem_filter.mp hw).2⟩

lemma freeNeighbors_shrink (M : SimpleGraph V) (v : V) (hv : Free (grow H side hside ids hi M) v)
    (hleft : side v = false) (hn : (freeNeighbors H (grow H side hside ids hi M) v).Nonempty) :
    (freeNeighbors H (grow H side hside ids hi M) v).card < (freeNeighbors H M v).card := by
  have hsub := freeNeighbors_decrease H side hside ids hi M v
  have hnold : (freeNeighbors H M v).Nonempty := hn.mono hsub
  obtain ⟨w,hw⟩ := propose_complete H side ids hi M v (free_before H side hside ids hi M v hv) hleft hnold
  have hp := propose_spec H side hside ids hi M v w hw
  obtain ⟨u,hu⟩ := accept_complete H side hside ids hi M v w hw
  have hchosen := accept_spec H side ids hi M u w hu
  have hgone := (chosen_not_free H side hside ids hi M u w hchosen).2
  have hwold : w ∈ freeNeighbors H M v := mem_filter.mpr ⟨(SimpleGraph.mem_neighborFinset H v w).mpr hp.2.2.1,hp.2.1⟩
  have hwnew : w ∉ freeNeighbors H (grow H side hside ids hi M) v := fun h => hgone (mem_filter.mp h).2
  apply card_lt_card
  exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub,fun heq => hwnew (heq.symm ▸ hwold)⟩

end Growth
end BipartiteProposals

-- Solutions/Sol_matching_mate_update.lean

open Classical Finset
noncomputable section
namespace BipartiteProposals
section Update
variable {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (side : V → Bool) (hside : ∀ u v, H.Adj u v → side u ≠ side v)
    (ids : V → ℕ) (hi : Function.Injective ids) (M : SimpleGraph V)
include hside

lemma grow_left_adj (u v : V) (hu : Free M u) (hs : side u = false) :
    (grow H side hside ids hi M).Adj u v ↔ Chosen H side ids hi M u v := by
  constructor
  · rintro (h|h|h)
    · exact (hu v h).elim
    · exact h
    · have hright := (propose_spec H side hside ids hi M v u h.1).2.2.2.2
      rw [hs] at hright
      cases hright
  · exact fun h => Or.inr (Or.inl h)

lemma grow_right_adj (u v : V) (hu : Free M u) (hs : side u = true) :
    (grow H side hside ids hi M).Adj u v ↔ Chosen H side ids hi M v u := by
  constructor
  · rintro (h|h|h)
    · exact (hu v h).elim
    · have hleft := (propose_spec H side hside ids hi M u v h.1).2.2.2.1
      rw [hs] at hleft
      cases hleft
    · exact h
  · exact fun h => Or.inr (Or.inr h)

def updatedMate (u : V) : Option V :=
  if Free M u then
    if side u = false then (propose H side ids hi M u).bind (fun w =>
      if accept H side ids hi M w = some u then some w else none)
    else accept H side ids hi M u
  else mate ids hi M u

lemma mate_grow (hM : ∀ u v w, M.Adj u v → M.Adj u w → v = w) (u : V) :
    mate ids hi (grow H side hside ids hi M) u = updatedMate H side ids hi M u := by
  have hnew := grow_unique H side hside ids hi M hM
  unfold updatedMate
  by_cases hu : Free M u
  · rw [if_pos hu]
    by_cases hs : side u = false
    · rw [if_pos hs]
      cases hp : propose H side ids hi M u with
      | none =>
        simp only [Option.bind_none]
        apply (mate_none ids hi _ u).mpr
        intro v hv
        have hchosen := (grow_left_adj H side hside ids hi M u v hu hs).mp hv
        unfold Chosen at hchosen
        rw [hp] at hchosen
        cases hchosen.1
      | some w =>
        simp only [Option.bind_some]
        by_cases ha : accept H side ids hi M w = some u
        · rw [if_pos ha]
          apply (mate_some ids hi _ hnew u w).mpr
          exact (grow_left_adj H side hside ids hi M u w hu hs).mpr ⟨hp,ha⟩
        · rw [if_neg ha]
          apply (mate_none ids hi _ u).mpr
          intro v hv
          have hchosen := (grow_left_adj H side hside ids hi M u v hu hs).mp hv
          have hwv : w = v := Option.some.inj (hp.symm.trans hchosen.1)
          apply ha
          simpa only [hwv] using hchosen.2
    · rw [if_neg hs]
      have htrue : side u = true := by cases he : side u <;> simp_all
      cases ha : accept H side ids hi M u with
      | none =>
        apply (mate_none ids hi _ u).mpr
        intro v hv
        have hchosen := (grow_right_adj H side hside ids hi M u v hu htrue).mp hv
        unfold Chosen at hchosen
        rw [ha] at hchosen
        cases hchosen.2
      | some w =>
        apply (mate_some ids hi _ hnew u w).mpr
        exact (grow_right_adj H side hside ids hi M u w hu htrue).mpr (accept_spec H side ids hi M w u ha)
  · rw [if_neg hu]
    have hneigh : (grow H side hside ids hi M).neighborFinset u = M.neighborFinset u := by
      ext v
      rw [SimpleGraph.mem_neighborFinset,SimpleGraph.mem_neighborFinset]
      constructor
      · rintro (h|hnew)
        · exact h
        · exact (hu (new_edge_free H side hside ids hi M u v hnew).1).elim
      · exact fun h => Or.inl h
    unfold mate
    rw [hneigh]

end Update
end BipartiteProposals

-- Solutions/Sol_bipartite_greedy_accept.lean

open Classical Finset
noncomputable section
namespace BipartiteGreedy
open BipartiteProposals

lemma accept_correct {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (side : V → Bool) (hside : ∀ u v, H.Adj u v → side u ≠ side v)
    (ids : V → ℕ) (hi : Function.Injective ids) (M G : SimpleGraph V) (hHG : H ≤ G)
    (hM : ∀ u v w, M.Adj u v → M.Adj u w → v = w) (v : V) :
    acceptStep (ids v) (accepted H side ids hi M v)
      ((G.neighborFinset v).val.map (fun w => (ids w,accepted H side ids hi M w))) =
        reference H side ids hi (grow H side hside ids hi M) v := by
  let msgs := (G.neighborFinset v).val.map (fun w => (ids w,accepted H side ids hi M w))
  let acknowledgments := LocalExchange.namedFilter ((H.neighborFinset v).image ids)
    (fun _ other => other.accepted = some (ids v)) msgs
  have hfilter := LocalExchange.namedFilter_correct G H hHG ids hi (accepted H side ids hi M) v
    (fun _ other => other.accepted = some (ids v))
  try dsimp only at hfilter
  have hmem (w : V) (hw : H.Adj v w) : ids w ∈ acknowledgments ↔ accept H side ids hi M w = some v := by
    change ids w ∈ LocalExchange.namedFilter _ _ _ ↔ _
    rw [hfilter]
    constructor
    · intro h
      obtain ⟨u,hu,heq⟩ := mem_image.mp h
      have huw : u = w := hi heq
      subst u
      exact (map_ids_some ids hi _ v).mp (mem_filter.mp hu).2
    · intro h
      refine mem_image.mpr ⟨w,mem_filter.mpr ⟨(SimpleGraph.mem_neighborFinset H v w).mpr hw,?_⟩,rfl⟩
      exact (map_ids_some ids hi _ v).mpr h
  apply Memory.ext
  · rfl
  · rfl
  · change (acceptStep (ids v) (accepted H side ids hi M v) msgs).partner = (mate ids hi (grow H side hside ids hi M) v).map ids
    rw [mate_grow H side hside ids hi M hM v]
    by_cases hu : Free M v
    · have hm := (mate_none ids hi M v).mpr hu
      dsimp only [acceptStep,accepted,proposed,reference]
      rw [hm]
      dsimp only [Option.map_none]
      unfold updatedMate
      rw [if_pos hu]
      by_cases hs : side v = false
      · rw [if_pos hs,if_pos hs]
        cases hp : propose H side ids hi M v with
        | none => rfl
        | some w =>
          have hadj := (propose_spec H side hside ids hi M v w hp).2.2.1
          have hack := hmem w hadj
          by_cases ha : accept H side ids hi M w = some v
          · have hyes := hack.mpr ha
            change (if ids w ∈ acknowledgments then some (ids w) else none) = (if accept H side ids hi M w = some v then some w else none).map ids
            rw [if_pos hyes,if_pos ha]
            rfl
          · have hno := fun h => ha (hack.mp h)
            change (if ids w ∈ acknowledgments then some (ids w) else none) = (if accept H side ids hi M w = some v then some w else none).map ids
            rw [if_neg hno,if_neg ha]
            rfl
      · rw [if_neg hs,if_neg hs]
    · have hm : mate ids hi M v ≠ none := fun h => hu ((mate_none ids hi M v).mp h)
      cases hpartner : mate ids hi M v with
      | none => exact (hm hpartner).elim
      | some w =>
        dsimp only [acceptStep,accepted,proposed,reference]
        rw [hpartner]
        unfold updatedMate
        rw [if_neg hu,hpartner]
        rfl
  · rfl
  · rfl

end BipartiteGreedy

-- Solutions/Sol_bipartite_maximality.lean

open Classical Finset
noncomputable section
namespace BipartiteProposals
section Iteration
variable {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (side : V → Bool) (hside : ∀ u v, H.Adj u v → side u ≠ side v)
    (ids : V → ℕ) (hi : Function.Injective ids)

def matchings : ℕ → SimpleGraph V
  | 0 => ⊥
  | t+1 => grow H side hside ids hi (matchings t)

lemma matchings_le (t : ℕ) : matchings H side hside ids hi t ≤ H := by
  induction t with
  | zero => exact bot_le
  | succ t ih => exact grow_le H side hside ids hi _ ih

lemma matchings_unique (t : ℕ) : ∀ u v w,
    (matchings H side hside ids hi t).Adj u v → (matchings H side hside ids hi t).Adj u w → v = w := by
  induction t with
  | zero => intro u v w h; cases h
  | succ t ih => exact grow_unique H side hside ids hi _ ih

lemma free_neighbor_budget (D : ℕ) (hD : ∀ v, H.degree v ≤ D) (v : V) (hleft : side v = false) :
    ∀ t, Free (matchings H side hside ids hi t) v →
      (freeNeighbors H (matchings H side hside ids hi t) v).Nonempty →
      t+(freeNeighbors H (matchings H side hside ids hi t) v).card ≤ D := by
  intro t
  induction t with
  | zero =>
    intro hv hn
    change 0+(freeNeighbors H ⊥ v).card ≤ D
    simpa only [Nat.zero_add,freeNeighbors] using (card_le_card (filter_subset (Free (⊥ : SimpleGraph V)) (H.neighborFinset v))).trans ((H.card_neighborFinset_eq_degree v).trans_le (hD v))
  | succ t ih =>
    intro hv hn
    have hf := free_before H side hside ids hi (matchings H side hside ids hi t) v hv
    have hsub := freeNeighbors_decrease H side hside ids hi (matchings H side hside ids hi t) v
    have hnold := hn.mono hsub
    have hi' := ih hf hnold
    have hlt := freeNeighbors_shrink H side hside ids hi (matchings H side hside ids hi t) v hv hleft hn
    change t+1+(freeNeighbors H (grow H side hside ids hi (matchings H side hside ids hi t)) v).card ≤ D
    omega

lemma no_free_edge (D : ℕ) (hD : ∀ v, H.degree v ≤ D) (u v : V) (huv : H.Adj u v)
    (hu : Free (matchings H side hside ids hi D) u) (hv : Free (matchings H side hside ids hi D) v) : False := by
  have aux (u v : V) (huv : H.Adj u v) (hu : Free (matchings H side hside ids hi D) u)
      (hv : Free (matchings H side hside ids hi D) v) (hleft : side u = false) : False := by
    have hn : (freeNeighbors H (matchings H side hside ids hi D) u).Nonempty :=
      ⟨v,mem_filter.mpr ⟨(SimpleGraph.mem_neighborFinset H u v).mpr huv,hv⟩⟩
    have hb := free_neighbor_budget H side hside ids hi D hD u hleft D hu hn
    have hp := card_pos.mpr hn
    omega
  by_cases hleft : side u = false
  · exact aux u v huv hu hv hleft
  · have hneq := hside u v huv
    have hvleft : side v = false := by cases hs : side u <;> cases ht : side v <;> simp_all
    exact aux v u huv.symm hv hu hvleft

lemma matchings_cover (D : ℕ) (hD : ∀ v, H.degree v ≤ D) (e : H.edgeSet) :
    ∃ v, v ∈ e.val ∧ ∃ w, (matchings H side hside ids hi D).Adj v w := by
  obtain ⟨⟨u,v⟩,he⟩ := e.val.exists_rep
  change s(u,v) = e.val at he
  have hadj : H.Adj u v := H.mem_edgeSet.mp (by rw [he]; exact e.property)
  by_contra h
  have hu : Free (matchings H side hside ids hi D) u := by
    intro w hw
    exact h ⟨u,by rw [←he]; exact Sym2.mem_mk_left _ _,w,hw⟩
  have hv : Free (matchings H side hside ids hi D) v := by
    intro w hw
    exact h ⟨v,by rw [←he]; exact Sym2.mem_mk_right _ _,w,hw⟩
  exact no_free_edge H side hside ids hi D hD u v hadj hu hv

end Iteration
end BipartiteProposals

-- Solutions/Sol_bipartite_greedy_execution.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace BipartiteGreedy
open BipartiteProposals
section Execution
variable {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (side : V → Bool) (hside : ∀ u v, H.Adj u v → side u ≠ side v)
    (ids : V → ℕ) (hi : Function.Injective ids) (G : SimpleGraph V) (hHG : H ≤ G)

include hHG in
lemma step_correct (M : SimpleGraph V) (hM : ∀ u v w, M.Adj u v → M.Adj u w → v = w) :
    stepProgram.program.output G () ids (reference H side ids hi M) (fun _ _ => false) =
      reference H side ids hi (grow H side hside ids hi M) := by
  have hs : (LocalExchange.oneRound statusStep).program.output G () ids (reference H side ids hi M) (fun _ _ => false) = proposed H side ids hi M := by
    funext v
    rw [LocalExchange.oneRound_output]
    exact status_correct H side ids hi M G hHG v
  have hp : (LocalExchange.oneRound proposalStep).program.output G () ids (proposed H side ids hi M) (fun _ _ => false) = accepted H side ids hi M := by
    funext v
    rw [LocalExchange.oneRound_output]
    exact proposal_correct H side hside ids hi M G hHG v
  have ha : (LocalExchange.oneRound acceptStep).program.output G () ids (accepted H side ids hi M) (fun _ _ => false) = reference H side ids hi (grow H side hside ids hi M) := by
    funext v
    rw [LocalExchange.oneRound_output]
    exact accept_correct H side hside ids hi M G hHG hM v
  funext v
  unfold stepProgram
  rw [LocalSequence.sequence_output]
  change (LocalSequence.sequence (LocalExchange.oneRound proposalStep) (LocalExchange.oneRound acceptStep) (fun _ _ _ out => out)).program.output G () ids
    ((LocalExchange.oneRound statusStep).program.output G () ids (reference H side ids hi M) (fun _ _ => false)) (fun _ _ => false) v = _
  rw [hs,LocalSequence.sequence_output]
  change (LocalExchange.oneRound acceptStep).program.output G () ids
    ((LocalExchange.oneRound proposalStep).program.output G () ids (proposed H side ids hi M) (fun _ _ => false)) (fun _ _ => false) v = _
  rw [hp,ha]

lemma reference_initial (v : V) :
    reference H side ids hi (⊥ : SimpleGraph V) v = initial ((H.neighborFinset v).image ids,side v) := by
  have hm : mate ids hi (⊥ : SimpleGraph V) v = none := (mate_none ids hi _ v).mpr (fun w h => h.elim)
  unfold reference
  rw [hm]
  rfl

include hHG in
lemma configurations_correct (t : ℕ) :
    LocalRepeat.configurations (fun _ => stepProgram) G ids (reference H side ids hi (⊥ : SimpleGraph V)) t =
      reference H side ids hi (matchings H side hside ids hi t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change stepProgram.program.output G () ids
      (LocalRepeat.configurations (fun _ => stepProgram) G ids (reference H side ids hi (⊥ : SimpleGraph V)) t) (fun _ _ => false) = _
    rw [ih]
    exact step_correct H side hside ids hi G hHG _ (matchings_unique H side hside ids hi t)

include hHG in
lemma protocol_output (D : ℕ) (v : V) :
    (protocol D).program.output G () ids (fun v => ((H.neighborFinset v).image ids,side v)) (fun _ _ => false) v =
      (mate ids hi (matchings H side hside ids hi D) v).map ids := by
  have hinit : (fun v => initial ((H.neighborFinset v).image ids,side v)) = reference H side ids hi (⊥ : SimpleGraph V) :=
    funext (fun v => (reference_initial H side ids hi v).symm)
  have hconf := configurations_correct H side hside ids hi G hHG D
  rw [protocol,LocalTransform.transform_output]
  change ((memoryProgram D).program.output G () ids (fun v => ((H.neighborFinset v).image ids,side v)) (fun _ _ => false) v).partner = _
  unfold memoryProgram
  rw [LocalSequence.sequence_output]
  change ((LocalRepeat.programs (fun _ => stepProgram) D).program.output G () ids (fun v => initial ((H.neighborFinset v).image ids,side v)) (fun _ _ => false) v).partner = _
  rw [hinit,LocalRepeat.repeat_output,hconf]
  rfl

end Execution
end BipartiteGreedy

-- Solutions/Sol_bipartite_bounded_matching.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section

theorem solution :
    ∃ A : Deterministic ℕ (Finset ℕ × Bool) (Option ℕ),
      (∀ D, A.program.rounds D ≤ 7*(D+1)) ∧
      ∀ (N : ℕ) (G H : SimpleGraph (Fin N)) (D : ℕ), H ≤ G → (∀ v, H.degree v ≤ D) →
        ∀ side : Fin N → Bool, Bipartition H side →
          ∀ ids : Fin N → ℕ, Function.Injective ids → ∃ M : SimpleGraph (Fin N),
            ReportsMatching H ids (execute A G D ids (fun v => (neighborIDs H ids v,side v))) M ∧
            ∀ e ∈ H.edgeSet, ∃ v, v ∈ e ∧ ∃ w, M.Adj v w := by
  let A := LocalFamily.select BipartiteGreedy.protocol
  refine ⟨A,?_,?_⟩
  · intro D
    change (BipartiteGreedy.protocol D).program.rounds () ≤ _
    rw [BipartiteGreedy.protocol_rounds]
    omega
  · intro N G H D hHG hD side hside ids hi
    let M := BipartiteProposals.matchings H side hside ids hi D
    have hle : M ≤ H := BipartiteProposals.matchings_le H side hside ids hi D
    have hM : ∀ u v w, M.Adj u v → M.Adj u w → v = w :=
      BipartiteProposals.matchings_unique H side hside ids hi D
    have hout : execute A G D ids (fun v => (neighborIDs H ids v,side v)) =
        (fun v => (BipartiteProposals.mate ids hi M v).map ids) := by
      funext v
      change (LocalFamily.select BipartiteGreedy.protocol).program.output G D ids (fun v => (neighborIDs H ids v,side v)) (fun _ _ => false) v = _
      rw [LocalFamily.select_output]
      exact BipartiteGreedy.protocol_output H side hside ids hi G hHG D v
    refine ⟨M,?_,?_⟩
    · rw [hout]
      exact BipartiteProposals.named_mate_reports H M ids hi hle hM
    · intro e he
      exact BipartiteProposals.matchings_cover H side hside ids hi D hD ⟨e,he⟩
