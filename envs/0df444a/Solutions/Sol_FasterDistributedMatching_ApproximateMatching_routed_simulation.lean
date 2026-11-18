-- Prove2me | solution 1 for FasterDistributedMatching.ApproximateMatching.routed_simulation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:39:02.13066+00:00
-- url     : https://prove2.me/submissions/22c786e0-fe70-44ce-9b5e-da6e56d57b43

import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Routing

open Classical Finset
open FasterDistributedMatching.ApproximateMatching

noncomputable section
namespace RoutedProof

abbrev Record (I : Type) := ℕ × I × Finset (ℕ × List ℕ)

def findRecord {I : Type} (R : Finset (Record I)) (j : ℕ) : Option (Record I) :=
  if h : ∃ z ∈ R, z.1 = j then some h.choose else none

def neighborKeys {I : Type} (z : Record I) : Finset ℕ := z.2.2.image Prod.fst

def simulate {K I O : Type} (A : Deterministic K I O) (k : K)
    (R : Finset (Record I)) : ℕ → ℕ → Option A.program.State
  | 0,j => (findRecord R j).map fun z => A.program.init k j z.2.1 (fun _ => false)
  | t+1,j => (findRecord R j).bind fun z =>
      (simulate A k R t j).map fun s => A.program.step s
        ((neighborKeys z).val.filterMap fun b => (simulate A k R t b).map A.program.send)

structure FloodState (K I : Type) where
  knowledge : K
  iterations : ℕ
  records : Finset (Record I)

def merge {I : Type} (R : Finset (Record I)) (msgs : Multiset (Finset (Record I))) : Finset (Record I) :=
  R ∪ msgs.toFinset.biUnion id

def simulator {K I O : Type} (A : Deterministic K I O) :
    Deterministic (K × ℕ) (Finset ℕ × RouteInput I) (ℕ → Option O) where
  program := {
    State := FloodState K I
    Msg := Finset (Record I)
    rounds := fun k => (k.2+1) * A.program.rounds k.1
    init := fun k _ inp _ => ⟨k.1,A.program.rounds k.1,inp.2⟩
    send := FloodState.records
    step := fun s msgs => {s with records := merge s.records msgs}
    out := fun s j => (simulate A s.knowledge s.records s.iterations j).map A.program.out }
  tape_independent := by intros; rfl

variable {N : ℕ} {G : SimpleGraph (Fin N)} {V I : Type} [Fintype V]
    (D : Routed G V) (ids : Fin N → ℕ) (inp : V → I)

def record (a : V) : Record I :=
  (D.identity a, inp a,
    (univ.filter (D.graph.Adj a)).attach.image fun b =>
      (D.identity b.val, (D.route a b.val (mem_filter.mp b.property).2).support.map ids))

def localRecords (v : Fin N) : Finset (Record I) :=
  (univ.filter (fun a => D.owner a = v)).image (record D ids inp)

lemma routeInput_records (v : Fin N) :
    (routeInput D ids inp v).2 = localRecords D ids inp v := rfl

lemma record_keys (a : V) :
    neighborKeys (record D ids inp a) = (univ.filter (D.graph.Adj a)).image D.identity := by
  unfold neighborKeys record
  rw [image_image]
  change (univ.filter (D.graph.Adj a)).attach.image (fun b => D.identity b.val) = _
  ext j
  simp only [mem_image, mem_attach, true_and, Subtype.exists, exists_prop]

lemma record_injective : Function.Injective (record D ids inp) := by
  intro a b h
  exact D.identity_injective (congrArg Prod.fst h)

lemma find_record {R : Finset (Record I)} (hauth : ∀ z ∈ R, ∃ a, record D ids inp a = z)
    (a : V) (ha : record D ids inp a ∈ R) :
    findRecord R (D.identity a) = some (record D ids inp a) := by
  unfold findRecord
  have hex : ∃ z ∈ R, z.1 = D.identity a := ⟨record D ids inp a,ha,rfl⟩
  rw [dif_pos hex]
  congr 1
  have hmem := hex.choose_spec.1
  obtain ⟨b,hb⟩ := hauth _ hmem
  have heq : D.identity b = D.identity a := by
    change (record D ids inp b).1 = _
    rw [hb]
    exact hex.choose_spec.2
  rw [← hb, D.identity_injective heq]

def flood : ℕ → Fin N → Finset (Record I)
  | 0,v => localRecords D ids inp v
  | t+1,v => merge (flood t v)
      ((univ.filter (G.Adj v)).val.map fun w => flood t w)

lemma flood_succ_mem (t : ℕ) (v : Fin N) (z : Record I) :
    z ∈ flood D ids inp (t+1) v ↔ z ∈ flood D ids inp t v ∨
      ∃ w, G.Adj v w ∧ z ∈ flood D ids inp t w := by
  simp only [flood,merge,mem_union,mem_biUnion,Multiset.mem_toFinset,Multiset.mem_map,
    mem_val,mem_filter,mem_univ,true_and,id_eq]
  aesop

lemma flood_mono (v : Fin N) : Monotone (fun t => flood D ids inp t v) := by
  apply monotone_nat_of_le_succ
  intro t z hz
  exact (flood_succ_mem D ids inp t v z).mpr (Or.inl hz)

lemma flood_authentic (t : ℕ) :
    ∀ v z, z ∈ flood D ids inp t v → ∃ a, record D ids inp a = z := by
  induction t with
  | zero =>
    intro v z hz
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hz
    exact ⟨a,rfl⟩
  | succ t ih =>
    intro v z hz
    rcases (flood_succ_mem D ids inp t v z).mp hz with h | ⟨w,hw,hz⟩
    · exact ih v z h
    · exact ih w z hz

lemma record_in_flood (a : V) {v u : Fin N} (w : G.Walk v u) (hu : u = D.owner a) :
    record D ids inp a ∈ flood D ids inp w.length v := by
  induction w with
  | nil =>
    apply mem_image.mpr
    exact ⟨a,mem_filter.mpr ⟨mem_univ a,hu.symm⟩,rfl⟩
  | cons h w ih =>
    apply (flood_succ_mem D ids inp w.length _ _).mpr
    exact Or.inr ⟨_,h,ih hu⟩

lemma record_in_flood_of_close (t : ℕ) (a : V) (v : Fin N) (h : Close G t v (D.owner a)) :
    record D ids inp a ∈ flood D ids inp t v := by
  obtain ⟨w,hw⟩ := h
  exact flood_mono D ids inp v hw (record_in_flood D ids inp a w rfl)

lemma physical_walk (r : ℕ) (hr : RouteLength D r) {a b : V} (w : D.graph.Walk a b) :
    ∃ path : G.Walk (D.owner a) (D.owner b), path.length ≤ r * w.length := by
  induction w with
  | nil => exact ⟨.nil,by simp⟩
  | @cons a b c h w ih =>
    obtain ⟨path,hpath⟩ := ih
    refine ⟨(D.route a b h).append path,?_⟩
    rw [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_cons]
    have hh := hr a b h
    nlinarith

lemma physical_close (r : ℕ) (hr : RouteLength D r) (t : ℕ) (a b : V)
    (h : Close D.graph t a b) : Close G (r*t) (D.owner a) (D.owner b) := by
  obtain ⟨w,hw⟩ := h
  obtain ⟨path,hpath⟩ := physical_walk D r hr w
  exact ⟨path,hpath.trans (Nat.mul_le_mul_left r hw)⟩

lemma filterMap_congr {α β : Type*} {s : Multiset α} {f g : α → Option β}
    (h : ∀ a ∈ s, f a = g a) : s.filterMap f = s.filterMap g := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | @cons a s ih =>
    rw [Multiset.filterMap_cons,Multiset.filterMap_cons,h a (by simp)]
    rw [ih (fun b hb => h b (by simp [hb]))]

lemma simulate_correct {K O : Type} (A : Deterministic K I O) (k : K)
    (R : Finset (Record I)) (hauth : ∀ z ∈ R, ∃ b, record D ids inp b = z)
    (t : ℕ) (a : V)
    (hall : ∀ b, Close D.graph t a b → record D ids inp b ∈ R) :
    simulate A k R t (D.identity a) =
      some (A.program.run D.graph k D.identity inp (fun _ _ => false) t a) := by
  induction t generalizing a with
  | zero =>
    have hself : record D ids inp a ∈ R := hall a ⟨.nil,by simp⟩
    rw [simulate, find_record D ids inp hauth a hself]
    rfl
  | succ t ih =>
    have hself : record D ids inp a ∈ R := hall a ⟨.nil,by simp⟩
    have hprev : ∀ b, Close D.graph t a b → record D ids inp b ∈ R := by
      intro b hb
      obtain ⟨w,hw⟩ := hb
      exact hall b ⟨w,by omega⟩
    have hneighbor (b : V) (hb : D.graph.Adj a b) :
        simulate A k R t (D.identity b) =
          some (A.program.run D.graph k D.identity inp (fun _ _ => false) t b) := by
      apply ih
      intro c hc
      obtain ⟨w,hw⟩ := hc
      exact hall c ⟨.cons hb w,by simpa using Nat.succ_le_succ hw⟩
    rw [simulate, find_record D ids inp hauth a hself, Option.bind_some,
      ih a hprev, Option.map_some]
    congr 1
    rw [record_keys]
    rw [image_val_of_injOn (fun b _ c _ h => D.identity_injective h), Multiset.filterMap_map]
    have heq : ∀ b ∈ (univ.filter (D.graph.Adj a)).val,
        (simulate A k R t (D.identity b)).map A.program.send =
          some (A.program.send (A.program.run D.graph k D.identity inp (fun _ _ => false) t b)) := by
      intro b hb
      have hadj := (mem_filter.mp hb).2
      rw [hneighbor b hadj]
      rfl
    simp only [Function.comp_def]
    rw [filterMap_congr heq]
    change A.program.step _ (Multiset.filterMap (some ∘
      (fun b => A.program.send (A.program.run D.graph k D.identity inp (fun _ _ => false) t b))) _) = _
    rw [Multiset.filterMap_eq_map]
    rfl

lemma simulator_run {K O : Type} (A : Deterministic K I O) (k : K) (r t : ℕ) (v : Fin N) :
    (simulator A).program.run G (k,r) ids (routeInput D ids inp) (fun _ _ => false) t v =
      ⟨k,A.program.rounds k,flood D ids inp t v⟩ := by
  induction t generalizing v with
  | zero => rfl
  | succ t ih =>
    rw [SmoothedMIS.LocalAlg.run]
    simp only [ih]
    rfl

end RoutedProof


theorem solution : RoutedSimulation := by
  refine ⟨1,by decide,?_⟩
  intro K I O A
  refine ⟨RoutedProof.simulator A,?_,?_⟩
  · intro k r
    simp [RoutedProof.simulator]
  · intro N G V _ D r hr ids hi k inp a
    unfold execute SmoothedMIS.LocalAlg.output
    rw [RoutedProof.simulator_run]
    change (RoutedProof.simulate A k
      (RoutedProof.flood D ids inp ((r+1)*A.program.rounds k) (D.owner a))
      (A.program.rounds k) (D.identity a)).map A.program.out = _
    rw [RoutedProof.simulate_correct D ids inp A k _
      (RoutedProof.flood_authentic D ids inp _ (D.owner a)) (A.program.rounds k) a ?_]
    · rfl
    · intro b hb
      apply RoutedProof.record_in_flood_of_close
      obtain ⟨path,hpath⟩ := RoutedProof.physical_close D r hr (A.program.rounds k) a b hb
      refine ⟨path,hpath.trans ?_⟩
      exact Nat.mul_le_mul_right _ (Nat.le_succ r)
