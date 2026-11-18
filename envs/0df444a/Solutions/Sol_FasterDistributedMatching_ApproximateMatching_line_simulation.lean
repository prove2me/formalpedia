-- Prove2me | solution 1 for FasterDistributedMatching.ApproximateMatching.line_simulation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:48:30.933197+00:00
-- url     : https://prove2.me/submissions/3fdce776-516e-40d7-80e5-4669241357e7

import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Routing

open Classical Finset
open FasterDistributedMatching.ApproximateMatching

noncomputable section
namespace LineProof

abbrev EdgeRecord (I : Type) := ℕ × I

def ends (j : ℕ) : Finset ℕ := {j.unpair.1,j.unpair.2}

def keys {I : Type} (R : Finset (EdgeRecord I)) : Finset ℕ := R.image Prod.fst

def keyGraph {I : Type} (R : Finset (EdgeRecord I)) : SimpleGraph ℕ where
  Adj j k := j ≠ k ∧ j ∈ keys R ∧ k ∈ keys R ∧ ¬ Disjoint (ends j) (ends k)
  symm := ⟨by intro a b h; exact ⟨h.1.symm,h.2.2.1,h.2.1,fun hd => h.2.2.2 hd.symm⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

variable {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ)

lemma ends_key (e : Sym2 (Fin N)) : ends (edgeIdentity ids e) = e.toFinset.image ids := by
  obtain ⟨⟨u,v⟩,rfl⟩ := e.exists_rep
  by_cases h : ids u ≤ ids v
  · simp [ends,edgeIdentity,Sym2.toFinset_mk_eq,min_eq_left h,max_eq_right h]
  · simp [ends,edgeIdentity,Sym2.toFinset_mk_eq,min_eq_right (le_of_not_ge h),
      max_eq_left (le_of_not_ge h),pair_comm]

lemma mem_ends_key (hi : Function.Injective ids) (e : Sym2 (Fin N)) (v : Fin N) :
    ids v ∈ ends (edgeIdentity ids e) ↔ v ∈ e := by
  rw [ends_key]
  constructor
  · intro hm
    obtain ⟨w,hw,h⟩ := mem_image.mp hm
    exact hi h ▸ (Sym2.mem_toFinset.mp hw)
  · intro h
    exact mem_image.mpr ⟨v,Sym2.mem_toFinset.mpr h,rfl⟩

lemma edgeIdentity_injective (hi : Function.Injective ids) : Function.Injective (edgeIdentity ids) := by
  intro e f hef
  apply Sym2.ext
  intro v
  rw [← mem_ends_key ids hi e v, ← mem_ends_key ids hi f v,hef]

lemma edgeKey_injective (hi : Function.Injective ids) :
    Function.Injective (fun e : G.edgeSet => edgeIdentity ids e.val) := by
  intro e f h
  apply Subtype.ext
  exact edgeIdentity_injective ids hi h

lemma key_adj {I : Type} (R : Finset (EdgeRecord I)) (hi : Function.Injective ids)
    (a b : G.edgeSet) :
    (keyGraph R).Adj (edgeIdentity ids a.val) (edgeIdentity ids b.val) ↔
      edgeIdentity ids a.val ∈ keys R ∧ edgeIdentity ids b.val ∈ keys R ∧ (lineGraph G).Adj a b := by
  constructor
  · intro h
    refine ⟨h.2.1,h.2.2.1,?_,?_⟩
    · intro hab; exact h.1 (congrArg (fun e : G.edgeSet => edgeIdentity ids e.val) hab)
    · obtain ⟨j,hja,hjb⟩ := not_disjoint_iff.mp h.2.2.2
      rw [ends_key] at hja
      obtain ⟨v,hv,hj⟩ := mem_image.mp hja
      refine ⟨v,Sym2.mem_toFinset.mp hv,?_⟩
      apply (mem_ends_key ids hi b.val v).mp
      simpa only [hj] using hjb
  · rintro ⟨ha,hb,hne,v,hva,hvb⟩
    refine ⟨fun h => hne (edgeKey_injective G ids hi h),ha,hb,?_⟩
    exact not_disjoint_iff.mpr ⟨ids v,(mem_ends_key ids hi a.val v).mpr hva,
      (mem_ends_key ids hi b.val v).mpr hvb⟩

lemma lower_walk {I : Type} (R : Finset (EdgeRecord I)) (hi : Function.Injective ids)
    {a b : G.edgeSet} (w : (lineGraph G).Walk a b)
    (hall : ∀ c ∈ w.support, edgeIdentity ids c.val ∈ keys R) :
    ∃ path : (keyGraph R).Walk (edgeIdentity ids a.val) (edgeIdentity ids b.val),
      path.length = w.length := by
  induction w with
  | nil => exact ⟨.nil,rfl⟩
  | @cons a b c h w ih =>
    obtain ⟨path,hpath⟩ := ih (fun d hd => hall d (by simp [hd]))
    have ha := hall a (by simp)
    have hb := hall b (by simp)
    exact ⟨.cons ((key_adj G ids R hi a b).mpr ⟨ha,hb,h⟩) path,by simp [hpath]⟩

lemma key_has_edge {I : Type} (R : Finset (EdgeRecord I)) (inp : G.edgeSet → I)
    (hauth : ∀ z ∈ R, ∃ e : G.edgeSet, (edgeIdentity ids e.val,inp e) = z)
    (j : ℕ) (hj : j ∈ keys R) : ∃ e : G.edgeSet, edgeIdentity ids e.val = j := by
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hj
  obtain ⟨e,he⟩ := hauth z hz
  exact ⟨e,congrArg Prod.fst he⟩

lemma lift_walk {I : Type} (R : Finset (EdgeRecord I)) (inp : G.edgeSet → I)
    (hi : Function.Injective ids)
    (hauth : ∀ z ∈ R, ∃ e : G.edgeSet, (edgeIdentity ids e.val,inp e) = z)
    {j k : ℕ} (w : (keyGraph R).Walk j k) :
    ∀ a b : G.edgeSet, edgeIdentity ids a.val = j → edgeIdentity ids b.val = k →
      ∃ path : (lineGraph G).Walk a b, path.length = w.length := by
  induction w with
  | nil =>
    intro a b ha hb
    have hab := edgeKey_injective G ids hi (ha.trans hb.symm)
    subst b
    exact ⟨.nil,rfl⟩
  | @cons j k l h w ih =>
    intro a b ha hb
    obtain ⟨c,hc⟩ := key_has_edge G ids R inp hauth k h.2.2.1
    have hac : (lineGraph G).Adj a c := by
      have hx : (keyGraph R).Adj (edgeIdentity ids a.val) (edgeIdentity ids c.val) := by
        simpa only [ha,hc] using h
      exact ((key_adj G ids R hi a c).mp hx).2.2
    obtain ⟨path,hpath⟩ := ih c b hc hb
    exact ⟨.cons hac path,by simp [hpath]⟩

lemma power_keys {I : Type} (R : Finset (EdgeRecord I)) (inp : G.edgeSet → I)
    (hi : Function.Injective ids)
    (hauth : ∀ z ∈ R, ∃ e : G.edgeSet, (edgeIdentity ids e.val,inp e) = z)
    (r : ℕ) (a : G.edgeSet)
    (hall : ∀ b, Close (lineGraph G) r a b → edgeIdentity ids b.val ∈ keys R) :
    (keys R).filter ((graphPower (keyGraph R) r).Adj (edgeIdentity ids a.val)) =
      (univ.filter ((graphPower (lineGraph G) r).Adj a)).image
        (fun b => edgeIdentity ids b.val) := by
  ext j
  constructor
  · intro hj
    obtain ⟨b,hb⟩ := key_has_edge G ids R inp hauth j (mem_filter.mp hj).1
    apply mem_image.mpr
    refine ⟨b,mem_filter.mpr ⟨mem_univ b,?_,?_⟩,hb⟩
    · intro heq
      exact (mem_filter.mp hj).2.1 (by simpa only [heq] using hb)
    · obtain ⟨w,hw⟩ := (mem_filter.mp hj).2.2
      obtain ⟨path,hpath⟩ := lift_walk G ids R inp hi hauth w a b rfl hb
      exact ⟨path,by omega⟩
  · intro hj
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hj
    obtain ⟨w,hw⟩ := (mem_filter.mp hb).2.2
    have hseen (c : G.edgeSet) (hc : c ∈ w.support) : edgeIdentity ids c.val ∈ keys R :=
      hall c ⟨w.takeUntil c hc,(w.length_takeUntil_le_length hc).trans hw⟩
    obtain ⟨path,hpath⟩ := lower_walk G ids R hi w hseen
    exact mem_filter.mpr ⟨hall b ⟨w,hw⟩,
      fun h => (mem_filter.mp hb).2.1 (edgeKey_injective G ids hi h),path,by omega⟩

def findEdge {I : Type} (R : Finset (EdgeRecord I)) (j : ℕ) : Option (EdgeRecord I) :=
  if h : ∃ z ∈ R, z.1 = j then some h.choose else none

def simulate {K I O : Type} (A : Deterministic K I O) (k : K) (r : ℕ)
    (R : Finset (EdgeRecord I)) : ℕ → ℕ → Option A.program.State
  | 0,j => (findEdge R j).map fun z => A.program.init k j z.2 (fun _ => false)
  | t+1,j => (simulate A k r R t j).map fun state => A.program.step state
      (((keys R).filter ((graphPower (keyGraph R) r).Adj j)).val.filterMap
        fun b => (simulate A k r R t b).map A.program.send)

lemma filterMap_congr {α β : Type*} {s : Multiset α} {f g : α → Option β}
    (h : ∀ a ∈ s, f a = g a) : s.filterMap f = s.filterMap g := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | @cons a s ih =>
    rw [Multiset.filterMap_cons,Multiset.filterMap_cons,h a (by simp)]
    rw [ih (fun b hb => h b (by simp [hb]))]

lemma find_edge {I : Type} (R : Finset (EdgeRecord I)) (inp : G.edgeSet → I)
    (hi : Function.Injective ids)
    (hauth : ∀ z ∈ R, ∃ e : G.edgeSet, (edgeIdentity ids e.val,inp e) = z)
    (a : G.edgeSet) (ha : (edgeIdentity ids a.val,inp a) ∈ R) :
    findEdge R (edgeIdentity ids a.val) = some (edgeIdentity ids a.val,inp a) := by
  unfold findEdge
  have hex : ∃ z ∈ R, z.1 = edgeIdentity ids a.val := ⟨_,ha,rfl⟩
  rw [dif_pos hex]
  congr 1
  obtain ⟨b,hb⟩ := hauth _ hex.choose_spec.1
  have heq : edgeIdentity ids b.val = edgeIdentity ids a.val := by
    change (edgeIdentity ids b.val,inp b).1 = _
    rw [hb]; exact hex.choose_spec.2
  rw [← hb,edgeKey_injective G ids hi heq]

lemma simulate_correct {K I O : Type} (A : Deterministic K I O) (k : K) (r : ℕ)
    (R : Finset (EdgeRecord I)) (inp : G.edgeSet → I) (hi : Function.Injective ids)
    (hauth : ∀ z ∈ R, ∃ e : G.edgeSet, (edgeIdentity ids e.val,inp e) = z)
    (t : ℕ) (a : G.edgeSet)
    (hall : ∀ b, Close (lineGraph G) (r*t) a b → (edgeIdentity ids b.val,inp b) ∈ R) :
    simulate A k r R t (edgeIdentity ids a.val) =
      some (A.program.run (graphPower (lineGraph G) r) k
        (fun e => edgeIdentity ids e.val) inp (fun _ _ => false) t a) := by
  induction t generalizing a with
  | zero =>
    rw [simulate,find_edge G ids R inp hi hauth a (hall a ⟨.nil,by simp⟩)]
    rfl
  | succ t ih =>
    have hprev : ∀ b, Close (lineGraph G) (r*t) a b → (edgeIdentity ids b.val,inp b) ∈ R := by
      intro b hb
      obtain ⟨w,hw⟩ := hb
      exact hall b ⟨w,by nlinarith⟩
    have hneighbor (b : G.edgeSet) (hb : (graphPower (lineGraph G) r).Adj a b) :
        simulate A k r R t (edgeIdentity ids b.val) =
          some (A.program.run (graphPower (lineGraph G) r) k
            (fun e => edgeIdentity ids e.val) inp (fun _ _ => false) t b) := by
      apply ih
      intro c hc
      obtain ⟨w,hw⟩ := hb.2
      obtain ⟨w',hw'⟩ := hc
      exact hall c ⟨w.append w',by rw [SimpleGraph.Walk.length_append]; nlinarith⟩
    have hkeys : ∀ b, Close (lineGraph G) r a b → edgeIdentity ids b.val ∈ keys R := by
      intro b hb
      obtain ⟨w,hw⟩ := hb
      exact mem_image.mpr ⟨_,hall b ⟨w,by nlinarith⟩,rfl⟩
    rw [simulate,ih a hprev,Option.map_some,power_keys G ids R inp hi hauth r a hkeys]
    congr 1
    rw [image_val_of_injOn (fun b _ c _ h => edgeKey_injective G ids hi h),Multiset.filterMap_map]
    simp only [Function.comp_def]
    have hfn : ∀ b ∈ (univ.filter ((graphPower (lineGraph G) r).Adj a)).val,
        (simulate A k r R t (edgeIdentity ids b.val)).map A.program.send =
          some (A.program.send (A.program.run (graphPower (lineGraph G) r) k
            (fun e => edgeIdentity ids e.val) inp (fun _ _ => false) t b)) := by
      intro b hb
      rw [hneighbor b (mem_filter.mp (mem_val.mp hb)).2]
      rfl
    rw [filterMap_congr hfn]
    change A.program.step _ (Multiset.filterMap (some ∘
      (fun b => A.program.send (A.program.run (graphPower (lineGraph G) r) k
        (fun e => edgeIdentity ids e.val) inp (fun _ _ => false) t b))) _) = _
    rw [Multiset.filterMap_eq_map]
    rfl

def host (e : G.edgeSet) : Fin N :=
  if ids e.val.out.1 ≤ ids e.val.out.2 then e.val.out.1 else e.val.out.2

lemma host_mem (e : G.edgeSet) : host G ids e ∈ e.val := by
  unfold host
  split_ifs
  · exact Sym2.out_fst_mem _
  · exact Sym2.out_snd_mem _

lemma host_reports (e : G.edgeSet) : HostsEdge ids e.val (host G ids e) := by
  refine ⟨host_mem G ids e,?_⟩
  intro w hw
  have hw' : w = e.val.out.1 ∨ w = e.val.out.2 := by
    rwa [← e.val.out_eq,Sym2.mem_iff] at hw
  unfold host
  split_ifs with h
  · rcases hw' with rfl | rfl <;> omega
  · rcases hw' with rfl | rfl <;> omega

lemma host_eq (hi : Function.Injective ids) (e : G.edgeSet) (v : Fin N)
    (hv : HostsEdge ids e.val v) : host G ids e = v := by
  apply hi
  exact le_antisymm ((host_reports G ids e).2 v hv.1) (hv.2 _ (host_mem G ids e))

lemma endpoint_walk (e : G.edgeSet) (u v : Fin N) (hu : u ∈ e.val) (hv : v ∈ e.val) :
    ∃ path : G.Walk u v, path.length ≤ 1 := by
  by_cases h : u = v
  · subst v
    exact ⟨.nil,by simp⟩
  · have he : e.val = s(u,v) := (Sym2.mem_and_mem_iff h).mp ⟨hu,hv⟩
    have hadj : G.Adj u v := G.mem_edgeSet.mp (by simpa only [he] using e.property)
    exact ⟨.cons hadj .nil,by simp⟩

lemma line_route (a b : G.edgeSet) (hab : (lineGraph G).Adj a b) :
    ∃ path : G.Walk (host G ids a) (host G ids b), path.length ≤ 2 := by
  obtain ⟨v,hva,hvb⟩ := hab.2
  obtain ⟨p,hp⟩ := endpoint_walk G a _ v (host_mem G ids a) hva
  obtain ⟨q,hq⟩ := endpoint_walk G b v _ hvb (host_mem G ids b)
  exact ⟨p.append q,by rw [SimpleGraph.Walk.length_append]; omega⟩

lemma line_physical {a b : G.edgeSet} (w : (lineGraph G).Walk a b) :
    ∃ path : G.Walk (host G ids a) (host G ids b), path.length ≤ 2*w.length := by
  induction w with
  | nil => exact ⟨.nil,by simp⟩
  | @cons a b c h w ih =>
    obtain ⟨p,hp⟩ := line_route G ids a b h
    obtain ⟨q,hq⟩ := ih
    exact ⟨p.append q,by rw [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_cons]; omega⟩

structure FloodState (K I : Type) where
  knowledge : K
  radius : ℕ
  iterations : ℕ
  records : Finset (EdgeRecord I)

def merge {I : Type} (R : Finset (EdgeRecord I)) (msgs : Multiset (Finset (EdgeRecord I))) :
    Finset (EdgeRecord I) := R ∪ msgs.toFinset.biUnion id

def simulator {K I O : Type} (A : Deterministic K I O) :
    Deterministic (K × ℕ) (Finset ℕ × Finset (ℕ × I)) (ℕ → Option O) where
  program := {
    State := FloodState K I
    Msg := Finset (EdgeRecord I)
    rounds := fun k => 2 * (k.2+2) * (A.program.rounds k.1+1)
    init := fun k _ inp _ => ⟨k.1,k.2,A.program.rounds k.1,inp.2⟩
    send := FloodState.records
    step := fun s msgs => {s with records := merge s.records msgs}
    out := fun s j => (simulate A s.knowledge s.radius s.records s.iterations j).map A.program.out }
  tape_independent := by intros; rfl

variable {I : Type} (inp : G.edgeSet → I)

def flood : ℕ → Fin N → Finset (EdgeRecord I)
  | 0,v => (lineInput G ids inp v).2
  | t+1,v => merge (flood t v) ((univ.filter (G.Adj v)).val.map fun w => flood t w)

lemma flood_succ_mem (t : ℕ) (v : Fin N) (z : EdgeRecord I) :
    z ∈ flood G ids inp (t+1) v ↔ z ∈ flood G ids inp t v ∨
      ∃ w, G.Adj v w ∧ z ∈ flood G ids inp t w := by
  simp only [flood,merge,mem_union,mem_biUnion,Multiset.mem_toFinset,Multiset.mem_map,
    mem_val,mem_filter,mem_univ,true_and,id_eq]
  aesop

lemma flood_mono (v : Fin N) : Monotone (fun t => flood G ids inp t v) := by
  apply monotone_nat_of_le_succ
  intro t z hz
  exact (flood_succ_mem G ids inp t v z).mpr (Or.inl hz)

lemma flood_authentic (t : ℕ) : ∀ v z, z ∈ flood G ids inp t v →
    ∃ e : G.edgeSet, (edgeIdentity ids e.val,inp e) = z := by
  induction t with
  | zero =>
    intro v z hz
    obtain ⟨e,he,rfl⟩ := mem_image.mp hz
    exact ⟨e,rfl⟩
  | succ t ih =>
    intro v z hz
    rcases (flood_succ_mem G ids inp t v z).mp hz with h | ⟨w,hw,hz⟩
    · exact ih v z h
    · exact ih w z hz

lemma edge_in_flood (a : G.edgeSet) {v u : Fin N} (w : G.Walk v u)
    (hu : u = host G ids a) : (edgeIdentity ids a.val,inp a) ∈ flood G ids inp w.length v := by
  induction w with
  | nil =>
    apply mem_image.mpr
    exact ⟨a,mem_filter.mpr ⟨mem_univ a,hu.symm ▸ host_reports G ids a⟩,rfl⟩
  | cons h w ih =>
    apply (flood_succ_mem G ids inp w.length _ _).mpr
    exact Or.inr ⟨_,h,ih hu⟩

lemma simulator_run {K O : Type} (A : Deterministic K I O) (k : K) (r t : ℕ) (v : Fin N) :
    (simulator A).program.run G (k,r) ids (lineInput G ids inp) (fun _ _ => false) t v =
      ⟨k,r,A.program.rounds k,flood G ids inp t v⟩ := by
  induction t generalizing v with
  | zero => rfl
  | succ t ih =>
    rw [SmoothedMIS.LocalAlg.run]
    simp only [ih]
    rfl

end LineProof


theorem solution : LineSimulation := by
  refine ⟨2,by decide,?_⟩
  intro K I O A
  refine ⟨LineProof.simulator A,?_,?_⟩
  · intro k r
    exact le_rfl
  · intro N G ids hi k r inp e v hv
    have hhost : LineProof.host G ids e = v := LineProof.host_eq G ids hi e v hv
    unfold execute SmoothedMIS.LocalAlg.output
    rw [LineProof.simulator_run]
    change (LineProof.simulate A k r
      (LineProof.flood G ids inp (2*(r+2)*(A.program.rounds k+1)) v)
      (A.program.rounds k) (edgeIdentity ids e.val)).map A.program.out = _
    rw [LineProof.simulate_correct G ids A k r _ inp hi
      (LineProof.flood_authentic G ids inp _ v) (A.program.rounds k) e ?_]
    · rfl
    · intro b hb
      obtain ⟨walk,hwalk⟩ := hb
      obtain ⟨path,hpath⟩ := LineProof.line_physical G ids walk
      have hmem := LineProof.edge_in_flood G ids inp b path rfl
      have hfinal : (edgeIdentity ids b.val,inp b) ∈
          LineProof.flood G ids inp (2*(r+2)*(A.program.rounds k+1)) (LineProof.host G ids e) :=
        LineProof.flood_mono G ids inp _ (by nlinarith) hmem
      simpa only [hhost] using hfinal
