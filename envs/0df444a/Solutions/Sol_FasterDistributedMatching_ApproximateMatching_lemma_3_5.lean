-- Prove2me | solution 1 for FasterDistributedMatching.ApproximateMatching.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T20:01:36.584419+00:00
-- url     : https://prove2.me/submissions/df747da4-fde2-43be-88c2-8ca16c4a7e31

import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Virtual
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Routing
import Mathlib
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Pairwise
import Theorems.Thm_FasterDistributedMatching_ApproximateMatching_lemma_3_4
import Theorems.Thm_FasterDistributedMatching_ApproximateMatching_lemma_2_2

-- Solutions/Sol_local_flood.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace LocalFlood

def merge {I : Type} (own : Finset (ℕ × I)) (msgs : Multiset (Finset (ℕ × I))) : Finset (ℕ × I) :=
  own ∪ msgs.toFinset.biUnion id

section Flood
variable {V I : Type} [Fintype V] (H : SimpleGraph V) (ids : V → ℕ) (inp : V → I)

def flood : ℕ → V → Finset (ℕ × I)
  | 0,v => {(ids v,inp v)}
  | t+1,v => merge (flood t v) ((H.neighborFinset v).val.map (flood t))

lemma flood_self (t : ℕ) (v : V) : (ids v,inp v) ∈ flood H ids inp t v := by
  induction t with
  | zero => exact mem_singleton_self _
  | succ t ih => exact mem_union_left _ ih

lemma flood_mono (t : ℕ) (v : V) : flood H ids inp t v ⊆ flood H ids inp (t+1) v :=
  subset_union_left

lemma flood_neighbor (t : ℕ) (v u : V) (hvu : H.Adj v u) :
    flood H ids inp t u ⊆ flood H ids inp (t+1) v := by
  intro r hr
  apply mem_union_right
  apply mem_biUnion.mpr
  refine ⟨flood H ids inp t u,?_,hr⟩
  apply Multiset.mem_toFinset.mpr
  exact Multiset.mem_map.mpr ⟨u,(SimpleGraph.mem_neighborFinset H v u).mpr hvu,rfl⟩

lemma flood_authentic (t : ℕ) (v : V) : ∀ r ∈ flood H ids inp t v, ∃ u, r = (ids u,inp u) := by
  induction t generalizing v with
  | zero =>
    intro r hr
    exact ⟨v,mem_singleton.mp hr⟩
  | succ t ih =>
    intro r hr
    rcases mem_union.mp hr with hr|hr
    · exact ih v r hr
    · obtain ⟨S,hS,hr⟩ := mem_biUnion.mp hr
      obtain ⟨u,hu,he⟩ := Multiset.mem_map.mp (Multiset.mem_toFinset.mp hS)
      subst S
      exact ih u r hr

lemma flood_walk (t : ℕ) {v u : V} (w : H.Walk v u) (hw : w.length ≤ t) :
    (ids u,inp u) ∈ flood H ids inp t v := by
  induction t generalizing v with
  | zero =>
    have he : v = u := by
      have hz : w.length = 0 := by omega
      exact (SimpleGraph.Walk.length_eq_zero_iff.mp hz).eq
    subst u
    exact flood_self H ids inp 0 v
  | succ t ih =>
    cases w with
    | nil => exact flood_self H ids inp (t+1) _
    | @cons v u z h w =>
      exact flood_neighbor H ids inp t v u h (ih w (by simpa using hw))

lemma flood_close (t : ℕ) (v u : V) (hc : Close H t v u) :
    (ids u,inp u) ∈ flood H ids inp t v := by
  obtain ⟨w,hw⟩ := hc
  exact flood_walk H ids inp t w hw

lemma flood_unique (hi : Function.Injective ids) (t : ℕ) (v : V) :
    ∀ r ∈ flood H ids inp t v, ∀ s ∈ flood H ids inp t v, r.1 = s.1 → r = s := by
  intro r hr s hs he
  obtain ⟨u,rfl⟩ := flood_authentic H ids inp t v r hr
  obtain ⟨w,rfl⟩ := flood_authentic H ids inp t v s hs
  have huw : u = w := hi he
  rw [huw]

end Flood
end LocalFlood

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

-- Solutions/Sol_cut_snapshot_keys.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace CutSnapshot

abbrev PhysicalRecord := ℕ × StageInput

def emptyInput : StageInput := ⟨∅,fun _ => 0,[],fun _ => none,fun _ => 0,fun _ => false,none⟩

def lookup (R : Finset PhysicalRecord) (id : ℕ) : StageInput :=
  if h : ∃ r ∈ R, r.1 = id then h.choose.2 else emptyInput

def keys (R : Finset PhysicalRecord) : Finset Key :=
  R.biUnion fun r => (range r.2.groups.length).image (fun i => (r.1,i))

def leader (R : Finset PhysicalRecord) (a : Key) : Option Key := (lookup R a.1).leader a.2

def color (R : Finset PhysicalRecord) (a : Key) : ℕ := (lookup R a.1).color a.2

def blockKeys (R : Finset PhysicalRecord) (a : Key) : Finset Key :=
  (keys R).filter (fun c => leader R c = some a)

def interaction (R : Finset PhysicalRecord) : SimpleGraph Key where
  Adj a b := a ≠ b ∧ leader R a = some a ∧ leader R b = some b ∧
    ∃ c ∈ blockKeys R a, ∃ d ∈ blockKeys R b, c.1 = d.1
  symm := ⟨by
    rintro a b ⟨hne,ha,hb,c,hc,d,hd,he⟩
    exact ⟨hne.symm,hb,ha,d,hd,c,hc,he.symm⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

def neighbors (R : Finset PhysicalRecord) (a : Key) : Finset Key := (keys R).filter ((interaction R).Adj a)

section Keys
variable {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (hi : Function.Injective ids)
    (x : Sym2 (Fin N) → ℝ) (p : Pairing N) (B : BlockAssignment p) (col : Copy p → ℕ)

abbrev physicalInput := stageInput G ids x p (some B) (some col) (fun _ => false) (fun _ => none)

def authentic (R : Finset PhysicalRecord) : Prop := ∀ r ∈ R, ∃ v, r = (ids v,physicalInput G ids x p B col v)

include hi in
lemma lookup_correct (R : Finset PhysicalRecord) (hauth : authentic G ids x p B col R)
    (v : Fin N) (hv : (ids v,physicalInput G ids x p B col v) ∈ R) :
    lookup R (ids v) = physicalInput G ids x p B col v := by
  let h : ∃ r ∈ R, r.1 = ids v := ⟨_,hv,rfl⟩
  unfold lookup
  rw [dif_pos h]
  obtain ⟨u,hu⟩ := hauth h.choose h.choose_spec.1
  have he : ids u = ids v := by simpa only [hu] using h.choose_spec.2
  have huv := hi he
  rw [hu,huv]

lemma key_mem (R : Finset PhysicalRecord) (a : Copy p)
    (ha : (ids a.1,physicalInput G ids x p B col a.1) ∈ R) : copyKey ids a ∈ keys R := by
  apply mem_biUnion.mpr
  refine ⟨_,ha,mem_image.mpr ⟨a.2.val,?_,rfl⟩⟩
  apply mem_range.mpr
  simpa only [physicalInput,stageInput,List.length_map] using a.2.isLt

lemma key_authentic (R : Finset PhysicalRecord) (hauth : authentic G ids x p B col R)
    (k : Key) (hk : k ∈ keys R) :
    ∃ a : Copy p, copyKey ids a = k ∧ (ids a.1,physicalInput G ids x p B col a.1) ∈ R := by
  obtain ⟨r,hr,hkr⟩ := mem_biUnion.mp hk
  obtain ⟨i,hi',he⟩ := mem_image.mp hkr
  obtain ⟨v,hv⟩ := hauth r hr
  have hindex : i < (p v).length := by
    simpa only [hv,physicalInput,stageInput,List.length_map,mem_range] using hi'
  refine ⟨⟨v,⟨i,hindex⟩⟩,?_,?_⟩
  · simpa only [copyKey,hv] using he
  · simpa only [hv] using hr

include hi in
lemma leader_correct (R : Finset PhysicalRecord) (hauth : authentic G ids x p B col R)
    (a : Copy p) (ha : (ids a.1,physicalInput G ids x p B col a.1) ∈ R) :
    leader R (copyKey ids a) = (B a).map (copyKey ids) := by
  unfold leader
  change (lookup R (ids a.1)).leader a.2.val = _
  rw [lookup_correct G ids hi x p B col R hauth a.1 ha]
  simp only [physicalInput,stageInput,dif_pos a.2.isLt,Option.bind_some]

include hi in
lemma color_correct (R : Finset PhysicalRecord) (hauth : authentic G ids x p B col R)
    (a : Copy p) (ha : (ids a.1,physicalInput G ids x p B col a.1) ∈ R) :
    color R (copyKey ids a) = col a := by
  unfold color
  change (lookup R (ids a.1)).color a.2.val = _
  rw [lookup_correct G ids hi x p B col R hauth a.1 ha]
  simp only [physicalInput,stageInput,dif_pos a.2.isLt,Option.map_some,Option.getD_some]

end Keys
end CutSnapshot

-- Solutions/Sol_cut_snapshot_blocks.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace CutSnapshot
section Blocks
variable {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (hi : Function.Injective ids)
    (x : Sym2 (Fin N) → ℝ) (p : Pairing N) (B : BlockAssignment p) (col : Copy p → ℕ)
    (R : Finset PhysicalRecord) (hauth : authentic G ids x p B col R)
include hi

lemma copyKey_injective : Function.Injective (copyKey ids (p:=p)) := by
  intro a b he
  apply DeterministicCuts.copyIdentity_injective ids hi
  exact congrArg (fun k : Key => Nat.pair k.1 k.2) he

lemma leader_option (a b : Copy p) : (B a).map (copyKey ids) = some (copyKey ids b) ↔ B a = some b := by
  constructor
  · intro h
    cases hba : B a with
    | none => simp only [hba,Option.map_none] at h; cases h
    | some c =>
      have he : copyKey ids c = copyKey ids b := by simpa only [hba,Option.map_some,Option.some.injEq] using h
      have hcb := copyKey_injective ids hi p he
      exact congrArg some hcb
  · intro h
    rw [h,Option.map_some]

include hauth

lemma blockKeys_sound (a : Copy p) (c : Key) (hc : c ∈ blockKeys R (copyKey ids a)) :
    ∃ d ∈ block B a, copyKey ids d = c := by
  obtain ⟨hkey,hlead⟩ := mem_filter.mp hc
  obtain ⟨d,hd,hR⟩ := key_authentic G ids x p B col R hauth c hkey
  refine ⟨d,mem_filter.mpr ⟨mem_univ _,?_⟩,hd⟩
  apply (leader_option ids hi p B d a).mp
  rw [←leader_correct G ids hi x p B col R hauth d hR,hd]
  exact hlead

lemma blockKeys_complete (a d : Copy p) (hd : d ∈ block B a)
    (hR : (ids d.1,physicalInput G ids x p B col d.1) ∈ R) :
    copyKey ids d ∈ blockKeys R (copyKey ids a) := by
  apply mem_filter.mpr
  refine ⟨key_mem G ids x p B col R d hR,?_⟩
  rw [leader_correct G ids hi x p B col R hauth d hR,(mem_filter.mp hd).2,Option.map_some]

lemma blockKeys_eq (a : Copy p)
    (hfull : ∀ d ∈ block B a, (ids d.1,physicalInput G ids x p B col d.1) ∈ R) :
    blockKeys R (copyKey ids a) = (block B a).image (copyKey ids) := by
  ext c
  constructor
  · intro hc
    obtain ⟨d,hd,he⟩ := blockKeys_sound G ids hi x p B col R hauth a c hc
    exact mem_image.mpr ⟨d,hd,he⟩
  · rintro hc
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hc
    exact blockKeys_complete G ids hi x p B col R hauth a d hd (hfull d hd)

lemma interaction_sound (a b : Copy p)
    (hRa : (ids a.1,physicalInput G ids x p B col a.1) ∈ R)
    (hRb : (ids b.1,physicalInput G ids x p B col b.1) ∈ R)
    (hab : (interaction R).Adj (copyKey ids a) (copyKey ids b)) :
    (DeterministicCuts.interaction B).Adj a b := by
  obtain ⟨hne,ha,hb,c,hc,d,hd,he⟩ := hab
  have hane : a ≠ b := fun h => hne (congrArg (copyKey ids) h)
  rw [leader_correct G ids hi x p B col R hauth a hRa] at ha
  rw [leader_correct G ids hi x p B col R hauth b hRb] at hb
  have hla := (leader_option ids hi p B a a).mp ha
  have hlb := (leader_option ids hi p B b b).mp hb
  obtain ⟨ca,hca,hce⟩ := blockKeys_sound G ids hi x p B col R hauth a c hc
  obtain ⟨db,hdb,hde⟩ := blockKeys_sound G ids hi x p B col R hauth b d hd
  refine ⟨hane,hla,hlb,ca,hca,db,hdb,?_⟩
  apply hi
  have hh := congrArg Prod.fst hce
  have hh' := congrArg Prod.fst hde
  exact hh.trans (he.trans hh'.symm)

lemma interaction_complete (a b : Copy p)
    (hRa : (ids a.1,physicalInput G ids x p B col a.1) ∈ R)
    (hRb : (ids b.1,physicalInput G ids x p B col b.1) ∈ R)
    (hfulla : ∀ d ∈ block B a, (ids d.1,physicalInput G ids x p B col d.1) ∈ R)
    (hfullb : ∀ d ∈ block B b, (ids d.1,physicalInput G ids x p B col d.1) ∈ R)
    (hab : (DeterministicCuts.interaction B).Adj a b) :
    (interaction R).Adj (copyKey ids a) (copyKey ids b) := by
  obtain ⟨hne,ha,hb,c,hc,d,hd,he⟩ := hab
  refine ⟨fun h => hne (copyKey_injective ids hi p h),?_,?_,
    copyKey ids c,blockKeys_complete G ids hi x p B col R hauth a c hc (hfulla c hc),
    copyKey ids d,blockKeys_complete G ids hi x p B col R hauth b d hd (hfullb d hd),?_⟩
  · rw [leader_correct G ids hi x p B col R hauth a hRa,ha,Option.map_some]
  · rw [leader_correct G ids hi x p B col R hauth b hRb,hb,Option.map_some]
  · exact congrArg ids he

end Blocks
end CutSnapshot

-- Solutions/Sol_hosted_snapshot.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace HostedSnapshot

abbrev Record (I : Type) := ℕ × I × Finset ℕ

def findRecord {I : Type} (R : Finset (Record I)) (id : ℕ) : Option (Record I) :=
  if h : ∃ r ∈ R, r.1 = id then some h.choose else none

def simulate {K I O : Type} (A : Deterministic K I O) (k : K) (R : Finset (Record I)) :
    ℕ → ℕ → Option A.program.State
  | 0,id => (findRecord R id).map (fun r => A.program.init k id r.2.1 (fun _ => false))
  | t+1,id => (findRecord R id).bind fun r => (simulate A k R t id).map fun st =>
      A.program.step st (r.2.2.val.filterMap fun j => (simulate A k R t j).map A.program.send)

lemma findRecord_eq {I : Type} (R : Finset (Record I))
    (hu : ∀ r ∈ R, ∀ s ∈ R, r.1 = s.1 → r = s) (r : Record I) (hr : r ∈ R) :
    findRecord R r.1 = some r := by
  let h : ∃ s ∈ R, s.1 = r.1 := ⟨r,hr,rfl⟩
  unfold findRecord
  rw [dif_pos h]
  congr 1
  exact hu h.choose h.choose_spec.1 r hr h.choose_spec.2

lemma filterMap_congr {X Y : Type} {s : Multiset X} {f g : X → Option Y}
    (h : ∀ x ∈ s, f x = g x) : s.filterMap f = s.filterMap g := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | @cons x s ih =>
    rw [Multiset.filterMap_cons,Multiset.filterMap_cons,h x (by simp)]
    rw [ih (fun y hy => h y (by simp [hy]))]

lemma simulate_correct {V K I O : Type} [Fintype V]
    (A : Deterministic K I O) (H : SimpleGraph V) (k : K)
    (ids : V → ℕ) (hi : Function.Injective ids) (inp : V → I)
    (R : Finset (Record I)) (hu : ∀ r ∈ R, ∀ s ∈ R, r.1 = s.1 → r = s)
    (t : ℕ) (a : V)
    (hall : ∀ b, Close H t a b → ∃ r ∈ R, r.1 = ids b ∧ r.2.1 = inp b ∧
      r.2.2 = (H.neighborFinset b).image ids) :
    simulate A k R t (ids a) = some (A.program.run H k ids inp (fun _ _ => false) t a) := by
  induction t generalizing a with
  | zero =>
    obtain ⟨r,hr,hid,hinput,hkeys⟩ := hall a ⟨.nil,by simp⟩
    have hf : findRecord R (ids a) = some r := by rw [←hid]; exact findRecord_eq R hu r hr
    rw [simulate,hf,Option.map_some,hinput]
    rfl
  | succ t ih =>
    obtain ⟨r,hr,hid,hinput,hkeys⟩ := hall a ⟨.nil,by simp⟩
    have hf : findRecord R (ids a) = some r := by rw [←hid]; exact findRecord_eq R hu r hr
    have hprev : simulate A k R t (ids a) = some (A.program.run H k ids inp (fun _ _ => false) t a) := by
      apply ih
      intro b hb
      obtain ⟨w,hw⟩ := hb
      exact hall b ⟨w,by omega⟩
    have hneighbor (b : V) (hb : H.Adj a b) :
        simulate A k R t (ids b) = some (A.program.run H k ids inp (fun _ _ => false) t b) := by
      apply ih
      intro c hc
      obtain ⟨w,hw⟩ := hc
      exact hall c ⟨.cons hb w,by simpa using Nat.succ_le_succ hw⟩
    rw [simulate,hf,Option.bind_some,hprev,Option.map_some,hkeys,
      image_val_of_injOn (fun b _ c _ he => hi he),Multiset.filterMap_map]
    congr 1
    have he : ∀ b ∈ (H.neighborFinset a).val,
        (simulate A k R t (ids b)).map A.program.send =
          some (A.program.send (A.program.run H k ids inp (fun _ _ => false) t b)) := by
      intro b hb
      rw [hneighbor b ((SimpleGraph.mem_neighborFinset H a b).mp hb)]
      rfl
    simp only [Function.comp_def]
    rw [filterMap_congr he]
    change A.program.step _ (Multiset.filterMap (some ∘
      (fun b => A.program.send (A.program.run H k ids inp (fun _ _ => false) t b))) _) = _
    rw [Multiset.filterMap_eq_map]
    have hn : H.neighborFinset a = univ.filter (H.Adj a) := by ext b; simp
    rw [hn]
    rfl

end HostedSnapshot

-- Solutions/Sol_cut_snapshot_objective.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace CutSnapshot

def encode (a : Key) : ℕ := Nat.pair a.1 a.2

lemma encode_injective : Function.Injective encode := by
  intro a b h
  have hh := Nat.pair_eq_pair.mp h
  exact Prod.ext hh.1 hh.2

def labelKeys (R : Finset PhysicalRecord) (a : Key) : Finset Key :=
  if leader R a = some a then blockKeys R a else {a}

def labels (R : Finset PhysicalRecord) (a : Key) : Finset ℕ := (labelKeys R a).image encode

def probability (R : Finset PhysicalRecord) (a : Key) (label : ℕ) : ℝ :=
  if label ∈ labels R a then 1/((labels R a).card:ℝ) else 0

def parity (R : Finset PhysicalRecord) (q : ℝ) (id : ℕ) : ℕ :=
  (((lookup R id).neighbors.filter (fun j => (lookup R id).edgeValue j = q)).card)%2

def unaryCost (R : Finset PhysicalRecord) (q : ℝ) (a : Key) (label : ℕ) : ℝ :=
  if leader R a = some a then 8*q^2*(1+(parity R q (Nat.unpair label).1:ℝ)) else 0

def pairCost (R : Finset PhysicalRecord) (q : ℝ) (a b : Key) (label other : ℕ) : ℝ :=
  if leader R a = some a ∧ leader R b = some b ∧ (Nat.unpair label).1 = (Nat.unpair other).1 then 8*q^2 else 0

def expectedUnary (R : Finset PhysicalRecord) (q : ℝ) (a : Key) : ℝ :=
  ∑ label ∈ labels R a, probability R a label*unaryCost R q a label

def expectedPair (R : Finset PhysicalRecord) (q : ℝ) (a b : Key) : ℝ :=
  ∑ label ∈ labels R a, ∑ other ∈ labels R b,
    probability R a label*probability R b other*pairCost R q a b label other

def objective (R : Finset PhysicalRecord) (q : ℝ) (a : Key) : ObjectiveInput where
  neighbors := (neighbors R a).image encode
  labels := labels R a
  probability := probability R a
  unaryUtility := fun label => if label ∈ labels R a then 2*expectedUnary R q a else 0
  unaryCost := fun label => if label ∈ labels R a then unaryCost R q a label else 0
  tables := fun id =>
    (fun label other => if Nat.unpair id ∈ neighbors R a ∧ label ∈ labels R a ∧ other ∈ labels R (Nat.unpair id)
      then 2*expectedPair R q a (Nat.unpair id) else 0,
     fun label other => if Nat.unpair id ∈ neighbors R a ∧ label ∈ labels R a ∧ other ∈ labels R (Nat.unpair id)
      then pairCost R q a (Nat.unpair id) label other else 0,
     fun label other => if Nat.unpair id ∈ neighbors R a ∧ label ∈ labels R a ∧ other ∈ labels R (Nat.unpair id)
      then 2*expectedPair R q (Nat.unpair id) a else 0,
     fun label other => if Nat.unpair id ∈ neighbors R a ∧ label ∈ labels R a ∧ other ∈ labels R (Nat.unpair id)
      then pairCost R q (Nat.unpair id) a other label else 0)
  color := color R a

def records (R : Finset PhysicalRecord) (q : ℝ) : Finset (HostedSnapshot.Record ObjectiveInput) :=
  (keys R).image fun a => (encode a,objective R q a,(neighbors R a).image encode)

lemma records_unique (R : Finset PhysicalRecord) (q : ℝ) :
    ∀ r ∈ records R q, ∀ s ∈ records R q, r.1 = s.1 → r = s := by
  intro r hr s hs he
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hr
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hs
  have hab : a = b := encode_injective he
  rw [hab]

end CutSnapshot

-- Solutions/Sol_cut_snapshot_parity.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace CutSnapshot
section Parity
variable {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (hi : Function.Injective ids)
    (x : Sym2 (Fin N) → ℝ) (p : Pairing N) (B : BlockAssignment p) (col : Copy p → ℕ)
include hi

lemma edgeValue_correct (v u : Fin N) (hu : G.Adj v u) :
    (physicalInput G ids x p B col v).edgeValue (ids u) = x s(v,u) := by
  change (∑ w ∈ G.neighborFinset v, if ids w = ids u then x s(v,w) else 0) = x s(v,u)
  rw [sum_eq_single u]
  · rw [if_pos rfl]
  · intro w hw hwu
    rw [if_neg (fun h => hwu (hi h))]
  · exact fun h => (h ((SimpleGraph.mem_neighborFinset G v u).mpr hu)).elim

lemma activeNeighbors_correct (q : ℝ) (v : Fin N) :
    ((physicalInput G ids x p B col v).neighbors.filter
      (fun j => (physicalInput G ids x p B col v).edgeValue j = q)) =
      ((G.neighborFinset v).filter (fun u => x s(v,u) = q)).image ids := by
  ext j
  constructor
  · intro hj
    obtain ⟨hjneigh,hq⟩ := mem_filter.mp hj
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hjneigh
    have hadj := (SimpleGraph.mem_neighborFinset G v u).mp hu
    rw [edgeValue_correct G ids hi x p B col v u hadj] at hq
    exact mem_image.mpr ⟨u,mem_filter.mpr ⟨hu,hq⟩,rfl⟩
  · intro hj
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hj
    have hadj := (SimpleGraph.mem_neighborFinset G v u).mp (mem_filter.mp hu).1
    apply mem_filter.mpr
    refine ⟨mem_image.mpr ⟨u,(mem_filter.mp hu).1,rfl⟩,?_⟩
    rw [edgeValue_correct G ids hi x p B col v u hadj]
    exact (mem_filter.mp hu).2

lemma parity_correct (R : Finset PhysicalRecord) (hauth : authentic G ids x p B col R)
    (q : ℝ) (v : Fin N) (hv : (ids v,physicalInput G ids x p B col v) ∈ R) :
    parity R q (ids v) = activeDegree G x q v%2 := by
  unfold parity
  rw [lookup_correct G ids hi x p B col R hauth v hv,activeNeighbors_correct G ids hi x p B col q v,
    card_image_of_injective _ hi]
  rfl

end Parity
end CutSnapshot

-- Solutions/Sol_finite_product_law.lean

open Classical Finset
noncomputable section
namespace FiniteProductLaw

variable {V L : Type} [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L]

def mass (p : V → L → ℝ) (s : V → L) : ℝ := ∏ v, p v (s v)

lemma weighted_product (p f : V → L → ℝ) :
    (∑ s : V → L, mass p s*(∏ v, f v (s v))) = ∏ v, ∑ a, p v a*f v a := by
  simp only [mass,←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun v (a : L) => p v a*f v a)).symm

lemma normalize (p : V → L → ℝ) (hn : ∀ v, (∑ a, p v a) = 1) :
    (∑ s : V → L, mass p s) = 1 := by
  calc
    _ = ∏ v, ∑ a, p v a := (Fintype.prod_sum p).symm
    _ = 1 := by simp only [hn,prod_const_one]

lemma marginal (p : V → L → ℝ) (hn : ∀ v, (∑ a, p v a) = 1) (v : V) (a : L) :
    (∑ s : V → L, if s v = a then mass p s else 0) = p v a := by
  let f : V → L → ℝ := fun w b => if w = v then if b = a then 1 else 0 else 1
  have hf (s : V → L) : (∏ w, f w (s w)) = if s v = a then 1 else 0 := by
    simp only [f]
    simp only [Finset.prod_ite_eq',mem_univ,ite_true]
  have he : (∑ s : V → L, if s v = a then mass p s else 0) =
      ∑ s : V → L, mass p s*(∏ w, f w (s w)) := by
    apply sum_congr rfl
    intro s hs
    rw [hf]
    split_ifs <;> simp only [mul_one,mul_zero]
  rw [he,weighted_product]
  have hg (w : V) : (∑ b, p w b*f w b) = if w = v then p v a else 1 := by
    by_cases hw : w = v
    · subst w
      simp only [f,ite_true,mul_ite,mul_one,mul_zero,sum_ite_eq',mem_univ,ite_true]
    · simp only [f,if_neg hw,mul_one,hn]
  simp only [hg]
  simp only [Finset.prod_ite_eq',mem_univ,ite_true]

lemma joint (p : V → L → ℝ) (hn : ∀ v, (∑ a, p v a) = 1)
    (v u : V) (hvu : v ≠ u) (a b : L) :
    (∑ s : V → L, if s v = a ∧ s u = b then mass p s else 0) = p v a*p u b := by
  let f : V → L → ℝ := fun w c =>
    (if w = v then if c = a then 1 else 0 else 1)*(if w = u then if c = b then 1 else 0 else 1)
  have hf (s : V → L) : (∏ w, f w (s w)) = if s v = a ∧ s u = b then 1 else 0 := by
    unfold f
    rw [Finset.prod_mul_distrib]
    have h1 : (∏ w, if w = v then if s w = a then (1:ℝ) else 0 else 1) = if s v = a then 1 else 0 := by
      simp only [Finset.prod_ite_eq',mem_univ,ite_true]
    have h2 : (∏ w, if w = u then if s w = b then (1:ℝ) else 0 else 1) = if s u = b then 1 else 0 := by
      simp only [Finset.prod_ite_eq',mem_univ,ite_true]
    rw [h1,h2]
    by_cases ha : s v = a <;> by_cases hb : s u = b <;> simp only [ha,hb,not_false_eq_true,ite_true,ite_false,true_and,false_and,and_false,mul_one,mul_zero,zero_mul]
  have he : (∑ s : V → L, if s v = a ∧ s u = b then mass p s else 0) =
      ∑ s : V → L, mass p s*(∏ w, f w (s w)) := by
    apply sum_congr rfl
    intro s hs
    rw [hf]
    split_ifs <;> simp only [mul_one,mul_zero]
  rw [he,weighted_product]
  have hg (w : V) : (∑ c, p w c*f w c) =
      (if w = v then p v a else 1)*(if w = u then p u b else 1) := by
    by_cases hwv : w = v
    · subst w
      simp only [f,ite_true,if_neg hvu,mul_one,mul_ite,mul_zero,sum_ite_eq',mem_univ]
    · by_cases hwu : w = u
      · subst w
        simp only [f,ite_true,if_neg hvu.symm,one_mul,mul_ite,mul_one,mul_zero,sum_ite_eq',mem_univ]
      · simp only [f,if_neg hwv,if_neg hwu,mul_one,one_mul,hn]
  simp only [hg,prod_mul_distrib]
  simp only [Finset.prod_ite_eq',mem_univ,ite_true]

end FiniteProductLaw

-- Solutions/Sol_cut_product.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace DeterministicCuts
variable {N : ℕ} {p : Pairing N}

def cutLabels (B : BlockAssignment p) (a : Copy p) : Finset (Copy p) :=
  if B a = some a then block B a else {a}

def cutProbability (B : BlockAssignment p) (a c : Copy p) : ℝ :=
  if c ∈ cutLabels B a then 1/((cutLabels B a).card:ℝ) else 0

lemma cutLabels_nonempty (B : BlockAssignment p) (ell : ℕ) (hell : 2 ≤ ell)
    (hB : ValidBlocks ell B) (a : Copy p) : (cutLabels B a).Nonempty := by
  unfold cutLabels
  split_ifs with ha
  · apply card_pos.mp
    have hh := (hB.2 a a ha).2.1
    omega
  · exact singleton_nonempty a

lemma cutProbability_normalize (B : BlockAssignment p) (ell : ℕ) (hell : 2 ≤ ell)
    (hB : ValidBlocks ell B) (a : Copy p) : (∑ c, cutProbability B a c) = 1 := by
  have hf : univ.filter (fun c => c ∈ cutLabels B a) = cutLabels B a := by ext c; simp
  have hn : ((cutLabels B a).card:ℝ) ≠ 0 := by
    exact_mod_cast (card_pos.mpr (cutLabels_nonempty B ell hell hB a)).ne'
  simp only [cutProbability,sum_ite,hf,sum_const_zero,add_zero,sum_const,nsmul_eq_mul]
  exact mul_one_div_cancel hn

lemma cutProbability_nonneg (B : BlockAssignment p) (a c : Copy p) : 0 ≤ cutProbability B a c := by
  unfold cutProbability
  split_ifs <;> positivity

lemma cutProbability_support (B : BlockAssignment p) (a c : Copy p) (h : cutProbability B a c ≠ 0) :
    c ∈ cutLabels B a := by
  by_contra hc
  exact h (if_neg hc)

lemma cutProbability_lower (B : BlockAssignment p) (ell : ℕ) (hell : 2 ≤ ell)
    (hB : ValidBlocks ell B) (a c : Copy p) (hc : c ∈ cutLabels B a) :
    1/(65*(ell:ℝ)+1) ≤ cutProbability B a c := by
  have hcard : (cutLabels B a).card ≤ 65*ell+1 := by
    unfold cutLabels
    split_ifs with ha
    · exact (hB.2 a a ha).2.2.1
    · simp only [card_singleton]; omega
  have hpos : (0:ℝ) < (cutLabels B a).card := by
    exact_mod_cast card_pos.mpr (cutLabels_nonempty B ell hell hB a)
  unfold cutProbability
  rw [if_pos hc]
  apply one_div_le_one_div_of_le hpos
  exact_mod_cast hcard

set_option maxHeartbeats 1200000 in
lemma independentCuts (B : BlockAssignment p) (ell : ℕ) (hell : 2 ≤ ell)
    (hB : ValidBlocks ell B) : PairwiseUniformCuts B (FiniteProductLaw.mass (cutProbability B)) := by
  have hn := cutProbability_normalize B ell hell hB
  refine ⟨fun s => prod_nonneg (fun a _ => cutProbability_nonneg B a (s a)),
    FiniteProductLaw.normalize (cutProbability B) hn,?_,?_,?_⟩
  · intro s hs a ha
    have hfactor : cutProbability B a (s a) ≠ 0 := by
      intro hz
      exact hs (Finset.prod_eq_zero (mem_univ a) hz)
    have hc := cutProbability_support B a (s a) hfactor
    simpa only [cutLabels,if_pos ha] using hc
  · intro a ha c hc
    rw [FiniteProductLaw.marginal _ hn]
    simp only [cutProbability,cutLabels,if_pos ha,if_pos hc]
  · intro a b ha hb hab c hc d hd
    rw [FiniteProductLaw.joint _ hn a b hab]
    simp only [cutProbability,cutLabels,if_pos ha,if_pos hb,if_pos hc,if_pos hd]
    ring

end DeterministicCuts

-- Solutions/Sol_cut_expansion.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace DeterministicCuts

lemma indicator_square_expansion {V : Type} [Fintype V] [DecidableEq V] (I : V → ℝ)
    (hI : ∀ a, I a*I a = I a) (r : ℝ) (hr : r*r = r) :
    (2*(∑ a, I a)+r)^2 = r+(∑ a, (4+4*r)*I a)+
      ∑ a, ∑ b, if a ≠ b then 4*I a*I b else 0 := by
  have hs : (∑ a, I a)^2 = (∑ a, I a)+∑ a, ∑ b, if a ≠ b then I a*I b else 0 := by
    have he (a b : V) : I a*I b =
        (if b = a then I a*I b else 0)+(if a ≠ b then I a*I b else 0) := by
      by_cases hab : a = b
      · subst b; simp
      · rw [if_neg (Ne.symm hab),if_pos hab]; exact (zero_add _).symm
    have hprod : (∑ a, I a)^2 = ∑ a, ∑ b, I a*I b := by
      rw [pow_two,Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    rw [hprod]
    conv_lhs => arg 2; intro a; arg 2; intro b; rw [he]
    simp only [sum_add_distrib,sum_ite_eq',sum_ite_eq,mem_univ,ite_true,hI]
  have hp : (∑ a, ∑ b, if a ≠ b then 4*I a*I b else 0) =
      4*(∑ a, ∑ b, if a ≠ b then I a*I b else 0) := by
    simp only [mul_sum]
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    split_ifs <;> ring
  rw [hp,←mul_sum]
  nlinarith

variable {N : ℕ} {p : Pairing N}

def cutIndicator (B : BlockAssignment p) (v : Fin N) (a : Copy p) (s : Copy p → Copy p) : ℝ :=
  if B a = some a ∧ (s a).1 = v then 1 else 0

lemma cutIndicator_square (B : BlockAssignment p) (v : Fin N) (a : Copy p) (s : Copy p → Copy p) :
    cutIndicator B v a s*cutIndicator B v a s = cutIndicator B v a s := by
  unfold cutIndicator
  split_ifs <;> norm_num

lemma cutIndicator_sum (B : BlockAssignment p) (v : Fin N) (s : Copy p → Copy p) :
    (∑ a, cutIndicator B v a s) = (cutCount B s v:ℝ) := by
  simp only [cutIndicator,cutCount,card_eq_sum_ones,sum_filter,Nat.cast_sum,
    Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

lemma parity_square (n : ℕ) : ((n%2:ℕ):ℝ)*((n%2:ℕ):ℝ) = ((n%2:ℕ):ℝ) := by
  have hn : n%2 = 0 ∨ n%2 = 1 := by omega
  rcases hn with hn|hn <;> simp only [hn] <;> norm_num

lemma vertex_cut_expansion (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (B : BlockAssignment p) (v : Fin N) (s : Copy p → Copy p) :
    (2*(cutCount B s v:ℝ)+(activeDegree G x q v%2:ℕ))^2 =
      (activeDegree G x q v%2:ℕ)+
      (∑ a, (4+4*((activeDegree G x q v%2:ℕ):ℝ))*cutIndicator B v a s)+
      ∑ a, ∑ b, if a ≠ b then 4*cutIndicator B v a s*cutIndicator B v b s else 0 := by
  rw [←cutIndicator_sum]
  exact indicator_square_expansion (cutIndicator B v · s) (fun a => cutIndicator_square B v a s)
    ((activeDegree G x q v%2:ℕ):ℝ) (parity_square (activeDegree G x q v))

end DeterministicCuts

-- Solutions/Sol_cut_cost_tables.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace DeterministicCuts
variable {N : ℕ} {p : Pairing N}

def unaryCost (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (B : BlockAssignment p) (a c : Copy p) : ℝ :=
  if B a = some a then 8*q^2*(1+((activeDegree G x q c.1%2:ℕ):ℝ)) else 0

def pairCost (q : ℝ) (B : BlockAssignment p) (a b c d : Copy p) : ℝ :=
  if B a = some a ∧ B b = some b ∧ c.1 = d.1 then 8*q^2 else 0

lemma unaryCost_nonneg (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (B : BlockAssignment p) (a c : Copy p) : 0 ≤ unaryCost G x q B a c := by
  unfold unaryCost
  split_ifs <;> positivity

lemma pairCost_nonneg (q : ℝ) (B : BlockAssignment p) (a b c d : Copy p) :
    0 ≤ pairCost q B a b c d := by
  unfold pairCost
  split_ifs <;> positivity

lemma unaryCost_expansion (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (B : BlockAssignment p) (s : Copy p → Copy p) (a : Copy p) :
    unaryCost G x q B a (s a) =
      ∑ v, 2*q^2*(4+4*((activeDegree G x q v%2:ℕ):ℝ))*cutIndicator B v a s := by
  by_cases ha : B a = some a
  · unfold unaryCost
    rw [if_pos ha]
    have he (v : Fin N) : 2*q^2*(4+4*((activeDegree G x q v%2:ℕ):ℝ))*cutIndicator B v a s =
        if v = (s a).1 then 2*q^2*(4+4*((activeDegree G x q v%2:ℕ):ℝ)) else 0 := by
      unfold cutIndicator
      by_cases hv : v = (s a).1
      · simp only [ha,hv,and_self,ite_true,mul_one]
      · simp only [ha,hv,Ne.symm hv,true_and,ite_false,mul_zero]
    rw [sum_congr rfl (fun v _ => he v)]
    simp only [sum_ite_eq',mem_univ,ite_true]
    ring
  · simp only [unaryCost,if_neg ha,cutIndicator,ha,false_and,ite_false,mul_zero,sum_const_zero]

lemma pairCost_expansion (q : ℝ) (B : BlockAssignment p) (s : Copy p → Copy p) (a b : Copy p) :
    pairCost q B a b (s a) (s b) = ∑ v, 8*q^2*cutIndicator B v a s*cutIndicator B v b s := by
  by_cases ha : B a = some a
  · by_cases hb : B b = some b
    · rw [sum_eq_single (s a).1]
      · simp only [pairCost,ha,hb,true_and,cutIndicator,and_self,ite_true,mul_one]
        by_cases he : (s a).1 = (s b).1
        · simp only [he,ite_true,mul_one]
        · simp only [he,Ne.symm he,ite_false,mul_zero]
      · intro v hv hne
        simp only [cutIndicator,ha,Ne.symm hne,true_and,ite_false,mul_zero,zero_mul]
      · exact fun h => (h (mem_univ _)).elim
    · simp only [pairCost,hb,and_false,false_and,ite_false,cutIndicator,mul_zero,sum_const_zero]
  · simp only [pairCost,ha,false_and,ite_false,cutIndicator,mul_zero,zero_mul,sum_const_zero]

lemma pairCost_off_graph (q : ℝ) (B : BlockAssignment p) (s : Copy p → Copy p)
    (hs : ValidCuts B s) (a b : Copy p) (hne : a ≠ b) (hn : ¬(interaction B).Adj a b) :
    pairCost q B a b (s a) (s b) = 0 := by
  unfold pairCost
  split_ifs with h
  · exact (hn ⟨hne,h.1,h.2.1,s a,hs a h.1,s b,hs b h.2.1,h.2.2⟩).elim
  · rfl

lemma graph_pairs_all (q : ℝ) (B : BlockAssignment p) (s : Copy p → Copy p)
    (hs : ValidCuts B s) :
    (∑ a, ∑ b ∈ (interaction B).neighborFinset a, pairCost q B a b (s a) (s b)) =
      ∑ a, ∑ b, if a ≠ b then pairCost q B a b (s a) (s b) else 0 := by
  apply sum_congr rfl
  intro a ha
  have hn : (interaction B).neighborFinset a = univ.filter ((interaction B).Adj a) := by ext b; simp
  rw [hn,sum_filter]
  apply sum_congr rfl
  intro b hb
  by_cases hab : (interaction B).Adj a b
  · rw [if_pos hab,if_pos hab.1]
  · rw [if_neg hab]
    by_cases he : a = b
    · rw [if_neg (not_not.mpr he)]
    · rw [if_pos he,pairCost_off_graph q B s hs a b he hab]

end DeterministicCuts

-- Solutions/Sol_cut_instance.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace DeterministicCuts
variable {N : ℕ} {p : Pairing N}

def copyID (ids : Fin N → ℕ) (a : Copy p) : ℕ := Nat.pair (ids a.1) a.2.val

lemma copyID_injective (ids : Fin N → ℕ) (hi : Function.Injective ids) :
    Function.Injective (copyID ids (p:=p)) := copyIdentity_injective ids hi

def encodedLabels (ids : Fin N → ℕ) (B : BlockAssignment p) (a : Copy p) : Finset ℕ :=
  (cutLabels B a).image (copyID ids)

def encodedUnary (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (ids : Fin N → ℕ) (B : BlockAssignment p) (a : Copy p) (label : ℕ) : ℝ :=
  ∑ c ∈ cutLabels B a, if copyID ids c = label then unaryCost G x q B a c else 0

def encodedPair (q : ℝ) (ids : Fin N → ℕ) (B : BlockAssignment p) (a b : Copy p)
    (label other : ℕ) : ℝ :=
  ∑ c ∈ cutLabels B a, ∑ d ∈ cutLabels B b,
    if copyID ids c = label ∧ copyID ids d = other then pairCost q B a b c d else 0

def expectedUnary (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (B : BlockAssignment p) (a : Copy p) : ℝ :=
  ∑ c ∈ cutLabels B a, (1/((cutLabels B a).card:ℝ))*unaryCost G x q B a c

def expectedPair (q : ℝ) (B : BlockAssignment p) (a b : Copy p) : ℝ :=
  ∑ c ∈ cutLabels B a, ∑ d ∈ cutLabels B b,
    (1/((cutLabels B a).card:ℝ))*(1/((cutLabels B b).card:ℝ))*pairCost q B a b c d

abbrev CopyIndex (p : Pairing N) := Fin (Fintype.card (Copy p))

def indexCopy (p : Pairing N) : CopyIndex p ≃ Copy p := (Fintype.equivFin (Copy p)).symm

def cutInstance (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (ids : Fin N → ℕ) (B : BlockAssignment p) : PairwiseInstance (Fintype.card (Copy p)) where
  graph := (interaction B).comap (indexCopy p)
  labels := fun i => encodedLabels ids B (indexCopy p i)
  probability := fun i label => if label ∈ encodedLabels ids B (indexCopy p i)
    then 1/((encodedLabels ids B (indexCopy p i)).card:ℝ) else 0
  unaryUtility := fun i _ => 2*expectedUnary G x q B (indexCopy p i)
  unaryCost := fun i label => encodedUnary G x q ids B (indexCopy p i) label
  pairUtility := fun i j _ _ => 2*expectedPair q B (indexCopy p i) (indexCopy p j)
  pairCost := fun i j label other => encodedPair q ids B (indexCopy p i) (indexCopy p j) label other

lemma encodedLabels_card (ids : Fin N → ℕ) (hi : Function.Injective ids) (B : BlockAssignment p) (a : Copy p) :
    (encodedLabels ids B a).card = (cutLabels B a).card :=
  card_image_of_injective _ (copyID_injective ids hi)

lemma encodedUnary_on_labels (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (ids : Fin N → ℕ) (hi : Function.Injective ids) (B : BlockAssignment p) (a c : Copy p)
    (hc : c ∈ cutLabels B a) : encodedUnary G x q ids B a (copyID ids c) = unaryCost G x q B a c := by
  unfold encodedUnary
  rw [sum_eq_single c]
  · rw [if_pos rfl]
  · intro d hd hdc
    rw [if_neg (fun he => hdc (copyID_injective ids hi he))]
  · exact fun h => (h hc).elim

lemma encodedPair_on_labels (q : ℝ) (ids : Fin N → ℕ) (hi : Function.Injective ids)
    (B : BlockAssignment p) (a b c d : Copy p) (hc : c ∈ cutLabels B a) (hd : d ∈ cutLabels B b) :
    encodedPair q ids B a b (copyID ids c) (copyID ids d) = pairCost q B a b c d := by
  unfold encodedPair
  rw [sum_eq_single c]
  · rw [sum_eq_single d]
    · simp only [and_self,ite_true]
    · intro e he hed
      simp only [show copyID ids e ≠ copyID ids d from fun h => hed (copyID_injective ids hi h),
        and_false,ite_false]
    · exact fun h => (h hd).elim
  · intro e he hec
    simp only [show copyID ids e ≠ copyID ids c from fun h => hec (copyID_injective ids hi h),
      false_and,ite_false,sum_const_zero]
  · exact fun h => (h hc).elim

end DeterministicCuts

-- Solutions/Sol_cut_snapshot_values.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace CutSnapshot
section Values
variable {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (hi : Function.Injective ids)
    (x : Sym2 (Fin N) → ℝ) (p : Pairing N) (B : BlockAssignment p) (col : Copy p → ℕ)
    (R : Finset PhysicalRecord) (hauth : authentic G ids x p B col R)
include hi hauth

lemma labelKeys_eq (a : Copy p)
    (hRa : (ids a.1,physicalInput G ids x p B col a.1) ∈ R)
    (hfull : ∀ c ∈ DeterministicCuts.cutLabels B a, (ids c.1,physicalInput G ids x p B col c.1) ∈ R) :
    labelKeys R (copyKey ids a) = (DeterministicCuts.cutLabels B a).image (copyKey ids) := by
  have hl := leader_correct G ids hi x p B col R hauth a hRa
  unfold labelKeys
  rw [hl]
  by_cases ha : B a = some a
  · rw [ha,Option.map_some,if_pos rfl]
    have hf : ∀ c ∈ block B a, (ids c.1,physicalInput G ids x p B col c.1) ∈ R := by
      simpa only [DeterministicCuts.cutLabels,if_pos ha] using hfull
    rw [blockKeys_eq G ids hi x p B col R hauth a hf]
    simp only [DeterministicCuts.cutLabels,if_pos ha]
  · have hne : (B a).map (copyKey ids) ≠ some (copyKey ids a) :=
      fun h => ha ((leader_option ids hi p B a a).mp h)
    simp only [if_neg hne,DeterministicCuts.cutLabels,if_neg ha,image_singleton]

lemma labels_eq (a : Copy p)
    (hRa : (ids a.1,physicalInput G ids x p B col a.1) ∈ R)
    (hfull : ∀ c ∈ DeterministicCuts.cutLabels B a, (ids c.1,physicalInput G ids x p B col c.1) ∈ R) :
    labels R (copyKey ids a) = DeterministicCuts.encodedLabels ids B a := by
  unfold labels
  rw [labelKeys_eq G ids hi x p B col R hauth a hRa hfull,image_image]
  rfl

lemma unaryCost_correct (q : ℝ) (a c : Copy p)
    (hRa : (ids a.1,physicalInput G ids x p B col a.1) ∈ R)
    (hRc : (ids c.1,physicalInput G ids x p B col c.1) ∈ R) :
    unaryCost R q (copyKey ids a) (DeterministicCuts.copyID ids c) =
      DeterministicCuts.unaryCost G x q B a c := by
  unfold unaryCost DeterministicCuts.unaryCost
  rw [leader_correct G ids hi x p B col R hauth a hRa]
  have hl := leader_option ids hi p B a a
  simp only [hl,DeterministicCuts.copyID,Nat.unpair_pair]
  rw [parity_correct G ids hi x p B col R hauth q c.1 hRc]

lemma pairCost_correct (q : ℝ) (a b c d : Copy p)
    (hRa : (ids a.1,physicalInput G ids x p B col a.1) ∈ R)
    (hRb : (ids b.1,physicalInput G ids x p B col b.1) ∈ R) :
    pairCost R q (copyKey ids a) (copyKey ids b) (DeterministicCuts.copyID ids c) (DeterministicCuts.copyID ids d) =
      DeterministicCuts.pairCost q B a b c d := by
  unfold pairCost DeterministicCuts.pairCost
  rw [leader_correct G ids hi x p B col R hauth a hRa,leader_correct G ids hi x p B col R hauth b hRb]
  simp only [leader_option ids hi p B a a,leader_option ids hi p B b b,
    DeterministicCuts.copyID,Nat.unpair_pair,hi.eq_iff]

lemma expectedUnary_correct (q : ℝ) (a : Copy p)
    (hRa : (ids a.1,physicalInput G ids x p B col a.1) ∈ R)
    (hfull : ∀ c ∈ DeterministicCuts.cutLabels B a, (ids c.1,physicalInput G ids x p B col c.1) ∈ R) :
    expectedUnary R q (copyKey ids a) = DeterministicCuts.expectedUnary G x q B a := by
  unfold expectedUnary
  have hl := labels_eq G ids hi x p B col R hauth a hRa hfull
  rw [hl]
  unfold DeterministicCuts.encodedLabels
  rw [sum_image (fun c _ d _ he => DeterministicCuts.copyID_injective ids hi he)]
  apply sum_congr rfl
  intro c hc
  rw [unaryCost_correct G ids hi x p B col R hauth q a c hRa (hfull c hc)]
  unfold probability
  have hcmem : DeterministicCuts.copyID ids c ∈ DeterministicCuts.encodedLabels ids B a := mem_image.mpr ⟨c,hc,rfl⟩
  rw [hl,if_pos hcmem,DeterministicCuts.encodedLabels_card ids hi]

lemma expectedPair_correct (q : ℝ) (a b : Copy p)
    (hRa : (ids a.1,physicalInput G ids x p B col a.1) ∈ R)
    (hRb : (ids b.1,physicalInput G ids x p B col b.1) ∈ R)
    (hfulla : ∀ c ∈ DeterministicCuts.cutLabels B a, (ids c.1,physicalInput G ids x p B col c.1) ∈ R)
    (hfullb : ∀ d ∈ DeterministicCuts.cutLabels B b, (ids d.1,physicalInput G ids x p B col d.1) ∈ R) :
    expectedPair R q (copyKey ids a) (copyKey ids b) = DeterministicCuts.expectedPair q B a b := by
  unfold expectedPair
  have hla := labels_eq G ids hi x p B col R hauth a hRa hfulla
  have hlb := labels_eq G ids hi x p B col R hauth b hRb hfullb
  rw [hla,hlb]
  unfold DeterministicCuts.encodedLabels
  rw [sum_image (fun c _ d _ he => DeterministicCuts.copyID_injective ids hi he)]
  apply sum_congr rfl
  intro c hc
  rw [sum_image (fun c _ d _ he => DeterministicCuts.copyID_injective ids hi he)]
  apply sum_congr rfl
  intro d hd
  rw [pairCost_correct G ids hi x p B col R hauth q a b c d hRa hRb]
  unfold probability
  have hcmem : DeterministicCuts.copyID ids c ∈ DeterministicCuts.encodedLabels ids B a := mem_image.mpr ⟨c,hc,rfl⟩
  have hdmem : DeterministicCuts.copyID ids d ∈ DeterministicCuts.encodedLabels ids B b := mem_image.mpr ⟨d,hd,rfl⟩
  rw [hla,hlb,if_pos hcmem,if_pos hdmem,
    DeterministicCuts.encodedLabels_card ids hi,DeterministicCuts.encodedLabels_card ids hi]

end Values
end CutSnapshot

-- Solutions/Sol_cut_snapshot_neighbors.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace CutSnapshot
section Neighbors
variable {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (hi : Function.Injective ids)
    (x : Sym2 (Fin N) → ℝ) (p : Pairing N) (B : BlockAssignment p) (col : Copy p → ℕ)
    (R : Finset PhysicalRecord) (hauth : authentic G ids x p B col R)
include hi hauth

lemma neighbors_eq (a : Copy p)
    (hRa : (ids a.1,physicalInput G ids x p B col a.1) ∈ R)
    (hfulla : ∀ c ∈ DeterministicCuts.cutLabels B a, (ids c.1,physicalInput G ids x p B col c.1) ∈ R)
    (hfullNeighbors : ∀ b, (DeterministicCuts.interaction B).Adj a b →
      (ids b.1,physicalInput G ids x p B col b.1) ∈ R ∧
      ∀ d ∈ DeterministicCuts.cutLabels B b, (ids d.1,physicalInput G ids x p B col d.1) ∈ R) :
    neighbors R (copyKey ids a) = ((DeterministicCuts.interaction B).neighborFinset a).image (copyKey ids) := by
  ext k
  constructor
  · intro hk
    obtain ⟨hkey,hAdj⟩ := mem_filter.mp hk
    obtain ⟨b,he,hRb⟩ := key_authentic G ids x p B col R hauth k hkey
    rw [←he] at hAdj
    have hab := interaction_sound G ids hi x p B col R hauth a b hRa hRb hAdj
    exact mem_image.mpr ⟨b,(SimpleGraph.mem_neighborFinset _ a b).mpr hab,he⟩
  · intro hk
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hk
    have hab := (SimpleGraph.mem_neighborFinset (DeterministicCuts.interaction B) a b).mp hb
    have hfb := hfullNeighbors b hab
    apply mem_filter.mpr
    refine ⟨key_mem G ids x p B col R b hfb.1,?_⟩
    have hfa : ∀ c ∈ block B a, (ids c.1,physicalInput G ids x p B col c.1) ∈ R := by
      simpa only [DeterministicCuts.cutLabels,if_pos hab.2.1] using hfulla
    have hfb' : ∀ d ∈ block B b, (ids d.1,physicalInput G ids x p B col d.1) ∈ R := by
      simpa only [DeterministicCuts.cutLabels,if_pos hab.2.2.1] using hfb.2
    exact interaction_complete G ids hi x p B col R hauth a b hRa hfb.1 hfa hfb' hab

end Neighbors
end CutSnapshot

-- Solutions/Sol_cut_instance_valid.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace DeterministicCuts
variable {N : ℕ} {p : Pairing N}

lemma cutLabels_card_bound (B : BlockAssignment p) (ell : ℕ) (hB : ValidBlocks ell B) (a : Copy p) :
    (cutLabels B a).card ≤ 65*ell+1 := by
  unfold cutLabels
  split_ifs with ha
  · exact (hB.2 a a ha).2.2.1
  · simp only [card_singleton]; omega

lemma encodedLabels_pos (ids : Fin N → ℕ) (hi : Function.Injective ids) (B : BlockAssignment p)
    (ell : ℕ) (hell : 2 ≤ ell) (hB : ValidBlocks ell B) (a : Copy p) :
    0 < ((encodedLabels ids B a).card:ℝ) := by
  rw [encodedLabels_card ids hi]
  exact_mod_cast card_pos.mpr (cutLabels_nonempty B ell hell hB a)

lemma expectedUnary_nonneg (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (B : BlockAssignment p) (a : Copy p) : 0 ≤ expectedUnary G x q B a :=
  sum_nonneg (fun c _ => mul_nonneg (by positivity) (unaryCost_nonneg G x q B a c))

lemma expectedPair_nonneg (q : ℝ) (B : BlockAssignment p) (a b : Copy p) : 0 ≤ expectedPair q B a b :=
  sum_nonneg (fun c _ => sum_nonneg (fun d _ => mul_nonneg (by positivity) (pairCost_nonneg q B a b c d)))

lemma cutInstance_valid (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (ids : Fin N → ℕ) (hi : Function.Injective ids) (B : BlockAssignment p)
    (ell : ℕ) (hell : 2 ≤ ell) (hB : ValidBlocks ell B) :
    ValidObjective (cutInstance G x q ids B) (1/(65*(ell:ℝ)+1)) := by
  have hden : (0:ℝ) < 65*(ell:ℝ)+1 := by positivity
  have hpos (a : Copy p) := encodedLabels_pos ids hi B ell hell hB a
  refine ⟨one_div_pos.mpr hden,?_,?_,?_,?_,?_⟩
  · apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2)
    have he : (2:ℝ) ≤ ell := by exact_mod_cast hell
    linarith
  · intro i
    change (∑ label ∈ encodedLabels ids B (indexCopy p i),
      if label ∈ encodedLabels ids B (indexCopy p i) then 1/((encodedLabels ids B (indexCopy p i)).card:ℝ) else 0) = 1
    rw [sum_congr rfl (fun label hl => if_pos hl)]
    simp only [sum_const,nsmul_eq_mul]
    exact mul_one_div_cancel (hpos _).ne'
  · intro i label
    change (0 ≤ if label ∈ encodedLabels ids B (indexCopy p i) then _ else 0) ∧ _
    refine ⟨by split_ifs <;> positivity,?_,?_⟩
    · intro hl
      exact if_neg hl
    · intro hp
      by_cases hl : label ∈ encodedLabels ids B (indexCopy p i)
      · change 1/(65*(ell:ℝ)+1) ≤ if label ∈ encodedLabels ids B (indexCopy p i) then _ else 0
        rw [if_pos hl]
        apply one_div_le_one_div_of_le (hpos _)
        rw [encodedLabels_card ids hi]
        exact_mod_cast cutLabels_card_bound B ell hB (indexCopy p i)
      · change 0 < if label ∈ encodedLabels ids B (indexCopy p i) then _ else 0 at hp
        rw [if_neg hl] at hp
        exact (lt_irrefl 0 hp).elim
  · intro i label
    constructor
    · exact mul_nonneg (by norm_num) (expectedUnary_nonneg G x q B _)
    · exact sum_nonneg (fun c _ => by split_ifs; exact unaryCost_nonneg G x q B _ _; rfl)
  · intro i j label other
    constructor
    · exact mul_nonneg (by norm_num) (expectedPair_nonneg q B _ _)
    · exact sum_nonneg (fun c _ => sum_nonneg (fun d _ => by split_ifs; exact pairCost_nonneg q B _ _ _ _; rfl))

end DeterministicCuts

-- Solutions/Sol_pairwise_expectation.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace PairwiseProof
section Expectation
variable {I : Type} [Fintype I] (labels : I → Finset ℕ) (p : I → ℕ → ℝ)

def expectation (f : (I → ℕ) → ℝ) : ℝ :=
  ∑ s : (i : I) → ↥(labels i), (∏ i, p i (s i)) * f (fun i => s i)

lemma expectation_add (f g : (I → ℕ) → ℝ) :
    expectation labels p (fun s => f s+g s) = expectation labels p f+expectation labels p g := by
  simp only [expectation,mul_add,sum_add_distrib]

lemma expectation_sum {J : Type} (S : Finset J) (f : J → (I → ℕ) → ℝ) :
    expectation labels p (fun s => ∑ j ∈ S, f j s) = ∑ j ∈ S, expectation labels p (f j) := by
  unfold expectation
  simp_rw [mul_sum]
  exact sum_comm

lemma expectation_mul (f : (I → ℕ) → ℝ) (c : ℝ) :
    expectation labels p (fun s => c*f s) = c*expectation labels p f := by
  unfold expectation
  simp_rw [←mul_assoc,mul_comm (∏ i, p i _) c,mul_assoc]
  exact (mul_sum _ _ _).symm

lemma expectation_product (g : I → ℕ → ℝ) :
    expectation labels p (fun s => ∏ i, g i (s i)) =
      ∏ i, ∑ a ∈ labels i, p i a*g i a := by
  unfold expectation
  simp_rw [←prod_mul_distrib]
  apply (Fintype.prod_sum (fun (i : I) (a : ↥(labels i)) => p i a*g i a)).symm.trans
  apply prod_congr rfl
  intro i hi
  exact sum_coe_sort (labels i) (fun a => p i a*g i a)

lemma expectation_unary (hn : ∀ i, ∑ a ∈ labels i, p i a = 1)
    (g : I → ℕ → ℝ) (v : I) :
    expectation labels p (fun s => g v (s v)) = ∑ a ∈ labels v, p v a*g v a := by
  let G := fun i a => if i = v then g i a else 1
  have hp : ∀ s : I → ℕ, (∏ i, G i (s i)) = g v (s v) := by
    intro s
    exact Fintype.prod_ite_eq' v (fun i => g i (s i))
  have hg (i : I) : (∑ a ∈ labels i, p i a*G i a) =
      if i = v then (∑ a ∈ labels i, p i a*g i a) else 1 := by
    by_cases hi : i = v
    · simp only [G,hi,ite_true]
    · simp only [G,hi,ite_false,mul_one,hn]
  have he := expectation_product labels p G
  simp only [hp,hg,Fintype.prod_ite_eq'] at he
  exact he

lemma expectation_two_factors (hn : ∀ i, ∑ a ∈ labels i, p i a = 1)
    (g h : I → ℕ → ℝ) (v w : I) (hvw : v ≠ w) :
    expectation labels p (fun s => g v (s v)*h w (s w)) =
      (∑ a ∈ labels v, p v a*g v a)*(∑ a ∈ labels w, p w a*h w a) := by
  let G := fun i a => (if i = v then g i a else 1)*(if i = w then h i a else 1)
  have hp : ∀ s : I → ℕ, (∏ i, G i (s i)) = g v (s v)*h w (s w) := by
    intro s
    simp only [G,prod_mul_distrib,Fintype.prod_ite_eq']
  have hg (i : I) : (∑ a ∈ labels i, p i a*G i a) =
      (if i = v then (∑ a ∈ labels i, p i a*g i a) else 1)*
      (if i = w then (∑ a ∈ labels i, p i a*h i a) else 1) := by
    by_cases hi : i = v
    · subst i
      simp only [G,ite_true,if_neg hvw,mul_one]
    · by_cases hj : i = w
      · subst i
        simp only [G,if_neg hi,ite_true,one_mul]
      · simp only [G,if_neg hi,if_neg hj,mul_one,hn]
  have he := expectation_product labels p G
  simp only [hp,hg,prod_mul_distrib,Fintype.prod_ite_eq'] at he
  exact he

lemma expectation_congr (f g : (I → ℕ) → ℝ)
    (h : ∀ s : (i : I) → ↥(labels i), f (fun i => s i) = g (fun i => s i)) :
    expectation labels p f = expectation labels p g := by
  unfold expectation
  apply sum_congr rfl
  intro s hs
  rw [h s]

lemma expectation_pair (hn : ∀ i, ∑ a ∈ labels i, p i a = 1)
    (v w : I) (hvw : v ≠ w) (f : ℕ → ℕ → ℝ) :
    expectation labels p (fun s => f (s v) (s w)) =
      ∑ a ∈ labels v, ∑ b ∈ labels w, p v a*p w b*f a b := by
  have hexpand : expectation labels p (fun s => f (s v) (s w)) =
      expectation labels p (fun s => ∑ a ∈ labels v, ∑ b ∈ labels w,
        f a b*((if s v = a then (1:ℝ) else 0)*(if s w = b then (1:ℝ) else 0))) := by
    apply expectation_congr
    intro s
    simp only [mul_ite,mul_one,mul_zero,ite_mul,one_mul,zero_mul]
    rw [sum_eq_single (s v).val]
    · rw [sum_eq_single (s w).val]
      · simp only [ite_true]
      · intro b hb hne
        simp only [Ne.symm hne,ite_false]
      · exact fun h => (h (s w).property).elim
    · intro a ha hne
      simp only [Ne.symm hne,ite_false,ite_self,sum_const_zero]
    · exact fun h => (h (s v).property).elim
  rw [hexpand,expectation_sum]
  apply sum_congr rfl
  intro a ha
  rw [expectation_sum]
  apply sum_congr rfl
  intro b hb
  rw [expectation_mul]
  have he := expectation_two_factors labels p hn
    (fun _ x => if x = a then (1:ℝ) else 0) (fun _ x => if x = b then (1:ℝ) else 0) v w hvw
  simp only [mul_ite,mul_one,mul_zero,sum_ite_eq',if_pos ha,if_pos hb] at he
  simp only [mul_ite,mul_one,mul_zero]
  rw [he]
  ring


def mean {N : ℕ} (H : SimpleGraph (Fin N)) (labels : Fin N → Finset ℕ)
    (p : Fin N → ℕ → ℝ) (unary : Fin N → ℕ → ℝ)
    (pair : Fin N → Fin N → ℕ → ℕ → ℝ) : ℝ :=
  (∑ v, ∑ a ∈ labels v, p v a*unary v a)+
    ∑ v, ∑ w ∈ H.neighborFinset v, ∑ a ∈ labels v, ∑ b ∈ labels w, p v a*p w b*pair v w a b

lemma expectation_value {N : ℕ} (H : SimpleGraph (Fin N)) (labels : Fin N → Finset ℕ)
    (p : Fin N → ℕ → ℝ) (hn : ∀ i, ∑ a ∈ labels i, p i a = 1)
    (unary : Fin N → ℕ → ℝ) (pair : Fin N → Fin N → ℕ → ℕ → ℝ) :
    expectation labels p (fun s => (∑ v, unary v (s v))+
      ∑ v, ∑ w ∈ H.neighborFinset v, pair v w (s v) (s w)) = mean H labels p unary pair := by
  rw [expectation_add,expectation_sum,expectation_sum]
  apply congrArg₂ (·+·)
  · apply sum_congr rfl
    intro v hv
    exact expectation_unary labels p hn unary v
  · apply sum_congr rfl
    intro v hv
    rw [expectation_sum]
    apply sum_congr rfl
    intro w hw
    exact expectation_pair labels p hn v w ((SimpleGraph.mem_neighborFinset H v w).mp hw).ne (pair v w)

lemma finiteExpectation_eq {N : ℕ} (D : PairwiseInstance N) (f : (Fin N → ℕ) → ℝ) :
    finiteExpectation D f = expectation D.labels D.probability f := by
  unfold finiteExpectation expectation
  apply sum_congr
  · ext s
    simp only [mem_univ]
  · intro s hs
    rfl

lemma finiteExpectation_utility {N : ℕ} (D : PairwiseInstance N)
    (hn : ∀ v, ∑ a ∈ D.labels v, D.probability v a = 1) :
    finiteExpectation D (utility D) = mean D.graph D.labels D.probability D.unaryUtility D.pairUtility := by
  rw [finiteExpectation_eq]
  exact expectation_value D.graph D.labels D.probability hn D.unaryUtility D.pairUtility

lemma finiteExpectation_cost {N : ℕ} (D : PairwiseInstance N)
    (hn : ∀ v, ∑ a ∈ D.labels v, D.probability v a = 1) :
    finiteExpectation D (cost D) = mean D.graph D.labels D.probability D.unaryCost D.pairCost := by
  rw [finiteExpectation_eq]
  exact expectation_value D.graph D.labels D.probability hn D.unaryCost D.pairCost


end Expectation
end PairwiseProof

-- Solutions/Sol_cut_instance_mean.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace DeterministicCuts
variable {N : ℕ} {p : Pairing N}

def expectedCost (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ) (B : BlockAssignment p) : ℝ :=
  (∑ a, expectedUnary G x q B a)+∑ a, ∑ b ∈ (interaction B).neighborFinset a, expectedPair q B a b

lemma sum_indexCopy (f : Copy p → ℝ) : (∑ i : CopyIndex p, f (indexCopy p i)) = ∑ a, f a :=
  (indexCopy p).sum_comp f

lemma comap_neighbor_sum {V U : Type} [Fintype V] [Fintype U] (e : V ≃ U)
    (H : SimpleGraph U) (f : U → ℝ) (v : V) :
    (∑ w ∈ (H.comap e).neighborFinset v, f (e w)) = ∑ u ∈ H.neighborFinset (e v), f u := by
  have h1 : (H.comap e).neighborFinset v = univ.filter (fun w => H.Adj (e v) (e w)) := by ext w; simp
  have h2 : H.neighborFinset (e v) = univ.filter (H.Adj (e v)) := by ext u; simp
  rw [h1,h2,sum_filter,sum_filter]
  exact e.sum_comp (fun u => if H.Adj (e v) u then f u else 0)

lemma instance_utility_constant (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (ids : Fin N → ℕ) (B : BlockAssignment p) (s : CopyIndex p → ℕ) :
    utility (cutInstance G x q ids B) s = 2*expectedCost G x q B := by
  unfold utility
  change (∑ i : CopyIndex p, 2*expectedUnary G x q B (indexCopy p i))+
    (∑ i : CopyIndex p, ∑ j ∈ ((interaction B).comap (indexCopy p)).neighborFinset i,
      2*expectedPair q B (indexCopy p i) (indexCopy p j)) = _
  simp only [←mul_sum]
  rw [sum_indexCopy]
  have hp : (∑ i : CopyIndex p, ∑ j ∈ ((interaction B).comap (indexCopy p)).neighborFinset i,
      expectedPair q B (indexCopy p i) (indexCopy p j)) =
      ∑ a, ∑ b ∈ (interaction B).neighborFinset a, expectedPair q B a b := by
    simp_rw [comap_neighbor_sum]
    exact sum_indexCopy (p:=p) (fun a => ∑ b ∈ (interaction B).neighborFinset a, expectedPair q B a b)
  rw [hp]
  unfold expectedCost
  ring

lemma instance_unary_mean (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (ids : Fin N → ℕ) (hi : Function.Injective ids) (B : BlockAssignment p) (i : CopyIndex p) :
    (∑ label ∈ (cutInstance G x q ids B).labels i,
      (cutInstance G x q ids B).probability i label*(cutInstance G x q ids B).unaryCost i label) =
      expectedUnary G x q B (indexCopy p i) := by
  change (∑ label ∈ encodedLabels ids B (indexCopy p i),
    (if label ∈ encodedLabels ids B (indexCopy p i) then 1/((encodedLabels ids B (indexCopy p i)).card:ℝ) else 0)*
      encodedUnary G x q ids B (indexCopy p i) label) = _
  rw [sum_congr rfl (fun label hl => congrArg (fun z => z*encodedUnary G x q ids B (indexCopy p i) label) (if_pos hl))]
  unfold encodedLabels
  rw [sum_image (fun a _ b _ he => copyID_injective ids hi he)]
  apply sum_congr rfl
  intro c hc
  rw [encodedUnary_on_labels G x q ids hi B _ c hc]
  have hcard := encodedLabels_card ids hi B (indexCopy p i)
  change 1/((encodedLabels ids B (indexCopy p i)).card:ℝ)*_ = _
  rw [hcard]

lemma instance_pair_mean (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (ids : Fin N → ℕ) (hi : Function.Injective ids) (B : BlockAssignment p) (i j : CopyIndex p) :
    (∑ label ∈ (cutInstance G x q ids B).labels i, ∑ other ∈ (cutInstance G x q ids B).labels j,
      (cutInstance G x q ids B).probability i label*(cutInstance G x q ids B).probability j other*
        (cutInstance G x q ids B).pairCost i j label other) =
      expectedPair q B (indexCopy p i) (indexCopy p j) := by
  change (∑ label ∈ encodedLabels ids B (indexCopy p i), ∑ other ∈ encodedLabels ids B (indexCopy p j),
    (if label ∈ encodedLabels ids B (indexCopy p i) then 1/((encodedLabels ids B (indexCopy p i)).card:ℝ) else 0)*
    (if other ∈ encodedLabels ids B (indexCopy p j) then 1/((encodedLabels ids B (indexCopy p j)).card:ℝ) else 0)*
      encodedPair q ids B (indexCopy p i) (indexCopy p j) label other) = _
  have he : ∀ label ∈ encodedLabels ids B (indexCopy p i), ∀ other ∈ encodedLabels ids B (indexCopy p j),
      (if label ∈ encodedLabels ids B (indexCopy p i) then 1/((encodedLabels ids B (indexCopy p i)).card:ℝ) else 0)*
      (if other ∈ encodedLabels ids B (indexCopy p j) then 1/((encodedLabels ids B (indexCopy p j)).card:ℝ) else 0)*
        encodedPair q ids B (indexCopy p i) (indexCopy p j) label other =
      (1/((encodedLabels ids B (indexCopy p i)).card:ℝ))*(1/((encodedLabels ids B (indexCopy p j)).card:ℝ))*
        encodedPair q ids B (indexCopy p i) (indexCopy p j) label other := by
    intro label hl other ho
    rw [if_pos hl,if_pos ho]
  rw [sum_congr rfl (fun label hl => sum_congr rfl (fun other ho => he label hl other ho))]
  unfold encodedLabels
  rw [sum_image (fun a _ b _ he => copyID_injective ids hi he)]
  apply sum_congr rfl
  intro c hc
  rw [sum_image (fun a _ b _ he => copyID_injective ids hi he)]
  apply sum_congr rfl
  intro d hd
  rw [encodedPair_on_labels q ids hi B _ _ c d hc hd]
  change (1/((encodedLabels ids B (indexCopy p i)).card:ℝ))*
    (1/((encodedLabels ids B (indexCopy p j)).card:ℝ))*_ = _
  rw [encodedLabels_card ids hi,encodedLabels_card ids hi]

lemma instance_cost_mean (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (ids : Fin N → ℕ) (hi : Function.Injective ids) (B : BlockAssignment p) :
    PairwiseProof.mean (cutInstance G x q ids B).graph (cutInstance G x q ids B).labels
      (cutInstance G x q ids B).probability (cutInstance G x q ids B).unaryCost
      (cutInstance G x q ids B).pairCost = expectedCost G x q B := by
  unfold PairwiseProof.mean
  simp_rw [instance_unary_mean G x q ids hi B,instance_pair_mean G x q ids hi B]
  rw [sum_indexCopy]
  congr 1
  change (∑ i : CopyIndex p, ∑ j ∈ ((interaction B).comap (indexCopy p)).neighborFinset i,
      expectedPair q B (indexCopy p i) (indexCopy p j)) = _
  simp_rw [comap_neighbor_sum]
  exact sum_indexCopy (p:=p) (fun a => ∑ b ∈ (interaction B).neighborFinset a, expectedPair q B a b)

end DeterministicCuts

-- Solutions/Sol_cut_canonical_input.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace DeterministicCuts

@[ext] lemma objective_ext (a b : ObjectiveInput)
    (hn : a.neighbors = b.neighbors) (hl : a.labels = b.labels)
    (hp : a.probability = b.probability) (hu : a.unaryUtility = b.unaryUtility)
    (hc : a.unaryCost = b.unaryCost) (ht : a.tables = b.tables) (hcol : a.color = b.color) : a = b := by
  cases a
  cases b
  simp_all only [ObjectiveInput.mk.injEq]

lemma comap_neighbor_image {V U X : Type} [Fintype V] [Fintype U] [DecidableEq X]
    (e : V ≃ U) (H : SimpleGraph U) (f : U → X) (v : V) :
    ((H.comap e).neighborFinset v).image (fun w => f (e w)) = (H.neighborFinset (e v)).image f := by
  ext z
  constructor
  · rintro hz
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
    exact mem_image.mpr ⟨e w,(SimpleGraph.mem_neighborFinset H (e v) (e w)).mpr
      ((SimpleGraph.mem_neighborFinset (H.comap e) v w).mp hw),rfl⟩
  · rintro hz
    obtain ⟨u,hu,he⟩ := mem_image.mp hz
    refine mem_image.mpr ⟨e.symm u,?_,?_⟩
    · apply (SimpleGraph.mem_neighborFinset (H.comap e) v (e.symm u)).mpr
      simpa only [SimpleGraph.comap_adj,Equiv.apply_symm_apply] using
        (SimpleGraph.mem_neighborFinset H (e v) u).mp hu
    · simpa only [Equiv.apply_symm_apply] using he

variable {N : ℕ} {p : Pairing N}

def canonicalInput (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (ids : Fin N → ℕ) (B : BlockAssignment p) (col : Copy p → ℕ) (a : Copy p) : ObjectiveInput where
  neighbors := ((interaction B).neighborFinset a).image (copyID ids)
  labels := encodedLabels ids B a
  probability := fun label => if label ∈ encodedLabels ids B a then 1/((encodedLabels ids B a).card:ℝ) else 0
  unaryUtility := fun label => if label ∈ encodedLabels ids B a then 2*expectedUnary G x q B a else 0
  unaryCost := fun label => if label ∈ encodedLabels ids B a then encodedUnary G x q ids B a label else 0
  tables := fun id =>
    (fun label other => ∑ b ∈ (interaction B).neighborFinset a,
      if copyID ids b = id ∧ label ∈ encodedLabels ids B a ∧ other ∈ encodedLabels ids B b
      then 2*expectedPair q B a b else 0,
     fun label other => ∑ b ∈ (interaction B).neighborFinset a,
      if copyID ids b = id ∧ label ∈ encodedLabels ids B a ∧ other ∈ encodedLabels ids B b
      then encodedPair q ids B a b label other else 0,
     fun label other => ∑ b ∈ (interaction B).neighborFinset a,
      if copyID ids b = id ∧ label ∈ encodedLabels ids B a ∧ other ∈ encodedLabels ids B b
      then 2*expectedPair q B b a else 0,
     fun label other => ∑ b ∈ (interaction B).neighborFinset a,
      if copyID ids b = id ∧ label ∈ encodedLabels ids B a ∧ other ∈ encodedLabels ids B b
      then encodedPair q ids B b a other label else 0)
  color := col a

lemma canonical_input_eq (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (ids : Fin N → ℕ) (B : BlockAssignment p) (col : Copy p → ℕ) (i : CopyIndex p) :
    objectiveInput (cutInstance G x q ids B) (fun j => copyID ids (indexCopy p j))
      (fun j => col (indexCopy p j)) i = canonicalInput G x q ids B col (indexCopy p i) := by
  apply objective_ext
  · change (((interaction B).comap (indexCopy p)).neighborFinset i).image
      (fun j => copyID ids (indexCopy p j)) = ((interaction B).neighborFinset (indexCopy p i)).image (copyID ids)
    exact comap_neighbor_image (indexCopy p) (interaction B) (copyID ids) i
  · rfl
  · rfl
  · rfl
  · rfl
  · funext id
    apply Prod.ext
    · funext label other
      exact comap_neighbor_sum (indexCopy p) (interaction B)
        (fun b => if copyID ids b = id ∧ label ∈ encodedLabels ids B (indexCopy p i) ∧
          other ∈ encodedLabels ids B b then 2*expectedPair q B (indexCopy p i) b else 0) i
    · apply Prod.ext
      · funext label other
        exact comap_neighbor_sum (indexCopy p) (interaction B)
          (fun b => if copyID ids b = id ∧ label ∈ encodedLabels ids B (indexCopy p i) ∧
            other ∈ encodedLabels ids B b then encodedPair q ids B (indexCopy p i) b label other else 0) i
      · apply Prod.ext
        · funext label other
          exact comap_neighbor_sum (indexCopy p) (interaction B)
            (fun b => if copyID ids b = id ∧ label ∈ encodedLabels ids B (indexCopy p i) ∧
              other ∈ encodedLabels ids B b then 2*expectedPair q B b (indexCopy p i) else 0) i
        · funext label other
          exact comap_neighbor_sum (indexCopy p) (interaction B)
            (fun b => if copyID ids b = id ∧ label ∈ encodedLabels ids B (indexCopy p i) ∧
              other ∈ encodedLabels ids B b then encodedPair q ids B b (indexCopy p i) other label else 0) i
  · rfl

end DeterministicCuts

-- Solutions/Sol_cut_scalar_tables.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace CutSnapshot

lemma neighbor_lookup {V : Type} [Fintype V] (H : SimpleGraph V) (ids : V → ℕ)
    (hi : Function.Injective ids) (a b : V) (hab : H.Adj a b)
    (P : V → Prop) [DecidablePred P] (f : V → ℝ) :
    (∑ c ∈ H.neighborFinset a, if ids c = ids b ∧ P c then f c else 0) =
      if P b then f b else 0 := by
  rw [sum_eq_single b]
  · simp only [true_and,ite_true]
  · intro c hc hcb
    simp only [show ids c ≠ ids b from fun h => hcb (hi h),false_and,ite_false]
  · exact fun h => (h ((SimpleGraph.mem_neighborFinset H a b).mpr hab)).elim

variable {N : ℕ} {p : Pairing N}

lemma scalarTable_correct (ids : Fin N → ℕ) (hi : Function.Injective ids)
    (B : BlockAssignment p) (R : Finset PhysicalRecord) (a : Copy p)
    (hN : neighbors R (copyKey ids a) = ((DeterministicCuts.interaction B).neighborFinset a).image (copyKey ids))
    (hL : labels R (copyKey ids a) = DeterministicCuts.encodedLabels ids B a)
    (hNL : ∀ b, (DeterministicCuts.interaction B).Adj a b →
      labels R (copyKey ids b) = DeterministicCuts.encodedLabels ids B b)
    (localTable : Key → ℕ → ℕ → ℝ) (globalTable : Copy p → ℕ → ℕ → ℝ)
    (hTable : ∀ b, (DeterministicCuts.interaction B).Adj a b →
      ∀ label ∈ DeterministicCuts.encodedLabels ids B a,
      ∀ other ∈ DeterministicCuts.encodedLabels ids B b,
        localTable (copyKey ids b) label other = globalTable b label other)
    (id label other : ℕ) :
    (if Nat.unpair id ∈ neighbors R (copyKey ids a) ∧ label ∈ labels R (copyKey ids a) ∧
      other ∈ labels R (Nat.unpair id) then localTable (Nat.unpair id) label other else 0) =
    ∑ b ∈ (DeterministicCuts.interaction B).neighborFinset a,
      if DeterministicCuts.copyID ids b = id ∧ label ∈ DeterministicCuts.encodedLabels ids B a ∧
        other ∈ DeterministicCuts.encodedLabels ids B b then globalTable b label other else 0 := by
  by_cases hid : Nat.unpair id ∈ neighbors R (copyKey ids a)
  · have hm : Nat.unpair id ∈ ((DeterministicCuts.interaction B).neighborFinset a).image (copyKey ids) := by rwa [←hN]
    obtain ⟨b,hb,hkey⟩ := mem_image.mp hm
    have hab := (SimpleGraph.mem_neighborFinset (DeterministicCuts.interaction B) a b).mp hb
    have hcode : DeterministicCuts.copyID ids b = id := by
      calc
        _ = encode (copyKey ids b) := rfl
        _ = encode (Nat.unpair id) := congrArg encode hkey
        _ = id := Nat.pair_unpair id
    rw [←hcode,neighbor_lookup (DeterministicCuts.interaction B) (DeterministicCuts.copyID ids)
      (DeterministicCuts.copyID_injective ids hi) a b hab]
    have hdecode : Nat.unpair (DeterministicCuts.copyID ids b) = copyKey ids b := by
      simp only [DeterministicCuts.copyID,Nat.unpair_pair,copyKey]
    rw [hdecode,hL,hNL b hab]
    have hnb : copyKey ids b ∈ neighbors R (copyKey ids a) := by
      rw [hN]
      exact mem_image.mpr ⟨b,hb,rfl⟩
    simp only [hnb,true_and]
    by_cases hl : label ∈ DeterministicCuts.encodedLabels ids B a
    · by_cases ho : other ∈ DeterministicCuts.encodedLabels ids B b
      · simp only [hl,ho,and_self,ite_true]
        exact hTable b hab label hl other ho
      · simp only [ho,and_false,ite_false]
    · simp only [hl,false_and,ite_false]
  · simp only [hid,false_and,ite_false]
    symm
    apply sum_eq_zero
    intro b hb
    apply if_neg
    rintro ⟨he,hlabels⟩
    apply hid
    rw [hN]
    apply mem_image.mpr
    refine ⟨b,hb,?_⟩
    have hd : Nat.unpair (DeterministicCuts.copyID ids b) = copyKey ids b := by
      simp only [DeterministicCuts.copyID,Nat.unpair_pair,copyKey]
    rw [←hd,he]

end CutSnapshot

-- Solutions/Sol_cut_objective_correct.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace CutSnapshot
section Objective
variable {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (hi : Function.Injective ids)
    (x : Sym2 (Fin N) → ℝ) (p : Pairing N) (B : BlockAssignment p) (col : Copy p → ℕ)
    (R : Finset PhysicalRecord) (hauth : authentic G ids x p B col R)
include hi hauth

lemma guardedUnary_correct (q : ℝ) (a : Copy p)
    (hRa : (ids a.1,physicalInput G ids x p B col a.1) ∈ R)
    (hfull : ∀ c ∈ DeterministicCuts.cutLabels B a, (ids c.1,physicalInput G ids x p B col c.1) ∈ R)
    (label : ℕ) :
    (if label ∈ labels R (copyKey ids a) then unaryCost R q (copyKey ids a) label else 0) =
    (if label ∈ DeterministicCuts.encodedLabels ids B a then DeterministicCuts.encodedUnary G x q ids B a label else 0) := by
  rw [labels_eq G ids hi x p B col R hauth a hRa hfull]
  by_cases hl : label ∈ DeterministicCuts.encodedLabels ids B a
  · rw [if_pos hl,if_pos hl]
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hl
    rw [unaryCost_correct G ids hi x p B col R hauth q a c hRa (hfull c hc),
      DeterministicCuts.encodedUnary_on_labels G x q ids hi B a c hc]
  · simp only [if_neg hl]

lemma pairCost_encoded (q : ℝ) (a b : Copy p)
    (hRa : (ids a.1,physicalInput G ids x p B col a.1) ∈ R)
    (hRb : (ids b.1,physicalInput G ids x p B col b.1) ∈ R)
    (label : ℕ) (hl : label ∈ DeterministicCuts.encodedLabels ids B a)
    (other : ℕ) (ho : other ∈ DeterministicCuts.encodedLabels ids B b) :
    pairCost R q (copyKey ids a) (copyKey ids b) label other =
      DeterministicCuts.encodedPair q ids B a b label other := by
  obtain ⟨c,hc,rfl⟩ := mem_image.mp hl
  obtain ⟨d,hd,rfl⟩ := mem_image.mp ho
  rw [pairCost_correct G ids hi x p B col R hauth q a b c d hRa hRb,
    DeterministicCuts.encodedPair_on_labels q ids hi B a b c d hc hd]

lemma objective_correct (q : ℝ) (a : Copy p)
    (hRa : (ids a.1,physicalInput G ids x p B col a.1) ∈ R)
    (hfulla : ∀ c ∈ DeterministicCuts.cutLabels B a, (ids c.1,physicalInput G ids x p B col c.1) ∈ R)
    (hfullNeighbors : ∀ b, (DeterministicCuts.interaction B).Adj a b →
      (ids b.1,physicalInput G ids x p B col b.1) ∈ R ∧
      ∀ d ∈ DeterministicCuts.cutLabels B b, (ids d.1,physicalInput G ids x p B col d.1) ∈ R) :
    objective R q (copyKey ids a) = DeterministicCuts.canonicalInput G x q ids B col a := by
  have hN := neighbors_eq G ids hi x p B col R hauth a hRa hfulla hfullNeighbors
  have hL := labels_eq G ids hi x p B col R hauth a hRa hfulla
  have hNL (b : Copy p) (hab : (DeterministicCuts.interaction B).Adj a b) :
      labels R (copyKey ids b) = DeterministicCuts.encodedLabels ids B b :=
    labels_eq G ids hi x p B col R hauth b (hfullNeighbors b hab).1 (hfullNeighbors b hab).2
  apply DeterministicCuts.objective_ext
  · change (neighbors R (copyKey ids a)).image encode = _
    rw [hN,image_image]
    rfl
  · exact hL
  · funext label
    change (if label ∈ labels R (copyKey ids a) then 1/((labels R (copyKey ids a)).card:ℝ) else 0) = _
    rw [hL]
    rfl
  · funext label
    change (if label ∈ labels R (copyKey ids a) then 2*expectedUnary R q (copyKey ids a) else 0) = _
    rw [hL,expectedUnary_correct G ids hi x p B col R hauth q a hRa hfulla]
    rfl
  · funext label
    exact guardedUnary_correct G ids hi x p B col R hauth q a hRa hfulla label
  · funext id
    apply Prod.ext
    · funext label other
      exact scalarTable_correct ids hi B R a hN hL hNL
        (fun b _ _ => 2*expectedPair R q (copyKey ids a) b)
        (fun b _ _ => 2*DeterministicCuts.expectedPair q B a b)
        (fun b hab _ _ _ _ => congrArg (2*·)
          (expectedPair_correct G ids hi x p B col R hauth q a b hRa
            (hfullNeighbors b hab).1 hfulla (hfullNeighbors b hab).2)) id label other
    · apply Prod.ext
      · funext label other
        exact scalarTable_correct ids hi B R a hN hL hNL
          (fun b => pairCost R q (copyKey ids a) b)
          (fun b => DeterministicCuts.encodedPair q ids B a b)
          (fun b hab label hl other ho => pairCost_encoded G ids hi x p B col R hauth q a b
            hRa (hfullNeighbors b hab).1 label hl other ho) id label other
      · apply Prod.ext
        · funext label other
          exact scalarTable_correct ids hi B R a hN hL hNL
            (fun b _ _ => 2*expectedPair R q b (copyKey ids a))
            (fun b _ _ => 2*DeterministicCuts.expectedPair q B b a)
            (fun b hab _ _ _ _ => congrArg (2*·)
              (expectedPair_correct G ids hi x p B col R hauth q b a
                (hfullNeighbors b hab).1 hRa (hfullNeighbors b hab).2 hfulla)) id label other
        · funext label other
          exact scalarTable_correct ids hi B R a hN hL hNL
            (fun b label other => pairCost R q b (copyKey ids a) other label)
            (fun b label other => DeterministicCuts.encodedPair q ids B b a other label)
            (fun b hab label hl other ho => pairCost_encoded G ids hi x p B col R hauth q b a
              (hfullNeighbors b hab).1 hRa other ho label hl) id label other
  · exact color_correct G ids hi x p B col R hauth a hRa

end Objective
end CutSnapshot

-- Solutions/Sol_cut_snapshot_records.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace CutSnapshot
section Records
variable {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (hi : Function.Injective ids)
    (x : Sym2 (Fin N) → ℝ) (p : Pairing N) (B : BlockAssignment p) (col : Copy p → ℕ)
    (R : Finset PhysicalRecord) (hauth : authentic G ids x p B col R)
include hi hauth

lemma record_good (q : ℝ) (i : DeterministicCuts.CopyIndex p)
    (hRa : (ids (DeterministicCuts.indexCopy p i).1,physicalInput G ids x p B col (DeterministicCuts.indexCopy p i).1) ∈ R)
    (hfulla : ∀ c ∈ DeterministicCuts.cutLabels B (DeterministicCuts.indexCopy p i),
      (ids c.1,physicalInput G ids x p B col c.1) ∈ R)
    (hfullNeighbors : ∀ b, (DeterministicCuts.interaction B).Adj (DeterministicCuts.indexCopy p i) b →
      (ids b.1,physicalInput G ids x p B col b.1) ∈ R ∧
      ∀ d ∈ DeterministicCuts.cutLabels B b, (ids d.1,physicalInput G ids x p B col d.1) ∈ R) :
    ∃ r ∈ records R q,
      r.1 = DeterministicCuts.copyID ids (DeterministicCuts.indexCopy p i) ∧
      r.2.1 = objectiveInput (DeterministicCuts.cutInstance G x q ids B)
        (fun j => DeterministicCuts.copyID ids (DeterministicCuts.indexCopy p j))
        (fun j => col (DeterministicCuts.indexCopy p j)) i ∧
      r.2.2 = ((DeterministicCuts.cutInstance G x q ids B).graph.neighborFinset i).image
        (fun j => DeterministicCuts.copyID ids (DeterministicCuts.indexCopy p j)) := by
  let a := DeterministicCuts.indexCopy p i
  refine ⟨(encode (copyKey ids a),objective R q (copyKey ids a),(neighbors R (copyKey ids a)).image encode),
    mem_image.mpr ⟨copyKey ids a,key_mem G ids x p B col R a hRa,rfl⟩,rfl,?_,?_⟩
  · exact (objective_correct G ids hi x p B col R hauth q a hRa hfulla hfullNeighbors).trans
      (DeterministicCuts.canonical_input_eq G x q ids B col i).symm
  · have hn := neighbors_eq G ids hi x p B col R hauth a hRa hfulla hfullNeighbors
    change (neighbors R (copyKey ids a)).image encode = _
    rw [hn,image_image]
    change ((DeterministicCuts.interaction B).neighborFinset (DeterministicCuts.indexCopy p i)).image
      (DeterministicCuts.copyID ids) =
      (((DeterministicCuts.interaction B).comap (DeterministicCuts.indexCopy p)).neighborFinset i).image
        (fun j => DeterministicCuts.copyID ids (DeterministicCuts.indexCopy p j))
    exact (DeterministicCuts.comap_neighbor_image (DeterministicCuts.indexCopy p)
      (DeterministicCuts.interaction B) (DeterministicCuts.copyID ids) i).symm

end Records
end CutSnapshot

-- Solutions/Sol_cut_protocol.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace CutSnapshot

def accuracy (ell : ℕ) : ℝ := 1/(65*(ell:ℝ)+1)

def physicalRounds (A : Deterministic (ℝ × ℕ) ObjectiveInput ℕ) (k : StageParameters) : ℕ :=
  256*k.ell*(A.program.rounds (accuracy k.ell,k.zeta)+2)

def mark (A : Deterministic (ℝ × ℕ) ObjectiveInput ℕ) (k : StageParameters) (id : ℕ)
    (inp : StageInput) (R : Finset PhysicalRecord) (i : ℕ) : Bool :=
  match inp.leader i with
  | none => false
  | some b => match HostedSnapshot.simulate A (accuracy k.ell,k.zeta) (records R k.q)
      (A.program.rounds (accuracy k.ell,k.zeta)) (encode b) with
    | none => false
    | some st => decide (A.program.out st = Nat.pair id i)

structure CutState where
  parameters : StageParameters
  ownID : ℕ
  original : StageInput
  snapshot : Finset PhysicalRecord

def protocol (A : Deterministic (ℝ × ℕ) ObjectiveInput ℕ) :
    Deterministic StageParameters StageInput (ℕ → Bool) where
  program := {
    State := CutState
    Msg := Finset PhysicalRecord
    rounds := physicalRounds A
    init := fun k id inp _ => ⟨k,id,inp,{(id,inp)}⟩
    send := CutState.snapshot
    step := fun st msgs => {st with snapshot := LocalFlood.merge st.snapshot msgs}
    out := fun st => mark A st.parameters st.ownID st.original st.snapshot }
  tape_independent := by intros; rfl

lemma protocol_run (A : Deterministic (ℝ × ℕ) ObjectiveInput ℕ) {V : Type} [Fintype V]
    (G : SimpleGraph V) (k : StageParameters) (ids : V → ℕ) (inp : V → StageInput) (t : ℕ) : ∀ v,
    (protocol A).program.run G k ids inp (fun _ _ => false) t v =
      ⟨k,ids v,inp v,LocalFlood.flood G ids inp t v⟩ := by
  induction t with
  | zero => intro v; rfl
  | succ t ih =>
    intro v
    rw [SmoothedMIS.LocalAlg.run]
    simp only [ih]
    have hn : univ.filter (G.Adj v) = G.neighborFinset v := by ext u; simp
    change CutState.mk k (ids v) (inp v)
      (LocalFlood.merge (LocalFlood.flood G ids inp t v)
        ((univ.filter (G.Adj v)).val.map (LocalFlood.flood G ids inp t))) = _
    rw [hn]
    rfl

lemma protocol_output (A : Deterministic (ℝ × ℕ) ObjectiveInput ℕ) {V : Type} [Fintype V]
    (G : SimpleGraph V) (k : StageParameters) (ids : V → ℕ) (inp : V → StageInput) (v : V) :
    (protocol A).program.output G k ids inp (fun _ _ => false) v =
      mark A k (ids v) (inp v) (LocalFlood.flood G ids inp (physicalRounds A k) v) := by
  unfold SmoothedMIS.LocalAlg.output
  rw [protocol_run]
  rfl

end CutSnapshot

-- Solutions/Sol_cut_snapshot_radius.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace CutSnapshot

lemma close_trans {V : Type} (G : SimpleGraph V) (r s : ℕ) {a b c : V}
    (hab : Close G r a b) (hbc : Close G s b c) : Close G (r+s) a c := by
  obtain ⟨w,hw⟩ := hab
  obtain ⟨z,hz⟩ := hbc
  exact ⟨w.append z,by simpa only [SimpleGraph.Walk.length_append] using Nat.add_le_add hw hz⟩

lemma close_mono {V : Type} (G : SimpleGraph V) (r s : ℕ) (hrs : r ≤ s) {a b : V}
    (hab : Close G r a b) : Close G s a b := by
  obtain ⟨w,hw⟩ := hab
  exact ⟨w,hw.trans hrs⟩

lemma label_close {N : ℕ} (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (p : Pairing N) (hp : ValidPairing G x q p) (B : BlockAssignment p) (ell : ℕ)
    (hB : ValidBlocks ell B) (a c : Copy p) (hc : c ∈ DeterministicCuts.cutLabels B a) :
    Close G (65*ell) a.1 c.1 := by
  by_cases ha : B a = some a
  · have hcb : c ∈ block B a := by simpa only [DeterministicCuts.cutLabels,if_pos ha] using hc
    exact DeterministicCuts.member_close G x q hp B ell hB a ha c hcb
  · have he : c = a := by simpa only [DeterministicCuts.cutLabels,if_neg ha,mem_singleton] using hc
    subst c
    exact ⟨.nil,by simp⟩

lemma causal_snapshot_complete {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
    (x : Sym2 (Fin N) → ℝ) (q : ℝ) (p : Pairing N) (hp : ValidPairing G x q p)
    (B : BlockAssignment p) (ell : ℕ) (hB : ValidBlocks ell B) (col : Copy p → ℕ)
    (T : ℕ) (a b : Copy p) (hab : B a = some b) (c : Copy p)
    (hbc : Close (DeterministicCuts.interaction B) (T+1) b c) :
    let R := LocalFlood.flood G ids (physicalInput G ids x p B col) (256*ell*(T+2)) a.1;
    (ids c.1,physicalInput G ids x p B col c.1) ∈ R ∧
      ∀ d ∈ DeterministicCuts.cutLabels B c, (ids d.1,physicalInput G ids x p B col d.1) ∈ R := by
  have hleader := (hB.2 a b hab).1
  have haBlock : a ∈ block B b := mem_filter.mpr ⟨mem_univ _,hab⟩
  have hba := DeterministicCuts.member_close G x q hp B ell hB b hleader a haBlock
  have habClose : Close G (65*ell) a.1 b.1 := by
    obtain ⟨w,hw⟩ := hba
    exact ⟨w.reverse,by simpa using hw⟩
  have hphys := DeterministicCuts.interaction_close_physical G x q hp B ell hB (T+1) b c hbc
  have hac := close_trans G _ _ habClose hphys
  have hsmall : 65*ell+130*ell*(T+1) ≤ 256*ell*(T+2) := by nlinarith
  have hlarge : (65*ell+130*ell*(T+1))+65*ell ≤ 256*ell*(T+2) := by nlinarith
  refine ⟨LocalFlood.flood_close G ids _ _ a.1 c.1 (close_mono G _ _ hsmall hac),?_⟩
  intro d hd
  have hcd := label_close G x q p hp B ell hB c d hd
  exact LocalFlood.flood_close G ids _ _ a.1 d.1
    (close_mono G _ _ hlarge (close_trans G _ _ hac hcd))

end CutSnapshot

-- Solutions/Sol_cut_instance_expectation.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace DeterministicCuts

lemma finiteExpectation_constant {n : ℕ} (D : PairwiseInstance n)
    (hn : ∀ v, (∑ a ∈ D.labels v, D.probability v a) = 1) (c : ℝ) :
    finiteExpectation D (fun _ => c) = c := by
  rw [PairwiseProof.finiteExpectation_eq]
  have he := PairwiseProof.expectation_product D.labels D.probability (fun _ _ => (1:ℝ))
  simp only [mul_one,hn,prod_const_one] at he
  have hh := PairwiseProof.expectation_mul D.labels D.probability (fun _ => (1:ℝ)) c
  simpa only [mul_one,he] using hh

variable {N : ℕ} {p : Pairing N}

lemma instance_expectations (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (ids : Fin N → ℕ) (hi : Function.Injective ids) (B : BlockAssignment p)
    (ell : ℕ) (hell : 2 ≤ ell) (hB : ValidBlocks ell B) :
    finiteExpectation (cutInstance G x q ids B) (utility (cutInstance G x q ids B)) =
      2*expectedCost G x q B ∧
    finiteExpectation (cutInstance G x q ids B) (cost (cutInstance G x q ids B)) =
      expectedCost G x q B := by
  have hD := cutInstance_valid G x q ids hi B ell hell hB
  constructor
  · have hfun : utility (cutInstance G x q ids B) = fun _ => 2*expectedCost G x q B :=
      funext (instance_utility_constant G x q ids B)
    rw [hfun]
    exact finiteExpectation_constant _ hD.2.2.1 _
  · rw [PairwiseProof.finiteExpectation_cost _ hD.2.2.1]
    exact instance_cost_mean G x q ids hi B

end DeterministicCuts

-- Solutions/Sol_cut_cost_identity.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace DeterministicCuts
variable {N : ℕ} {p : Pairing N}

def constantCost (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ) : ℝ :=
  2*q^2*∑ v, ((activeDegree G x q v%2:ℕ):ℝ)

def variableCost (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (B : BlockAssignment p) (s : Copy p → Copy p) : ℝ :=
  (∑ a, unaryCost G x q B a (s a))+
    ∑ a, ∑ b ∈ (interaction B).neighborFinset a, pairCost q B a b (s a) (s b)

lemma scaled_vertex_expansion (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (B : BlockAssignment p) (v : Fin N) (s : Copy p → Copy p) :
    2*q^2*(2*(cutCount B s v:ℝ)+(activeDegree G x q v%2:ℕ))^2 =
      2*q^2*((activeDegree G x q v%2:ℕ):ℝ)+
      (∑ a, 2*q^2*(4+4*((activeDegree G x q v%2:ℕ):ℝ))*cutIndicator B v a s)+
      ∑ a, ∑ b, if a ≠ b then 8*q^2*cutIndicator B v a s*cutIndicator B v b s else 0 := by
  rw [vertex_cut_expansion]
  simp only [mul_add,mul_sum]
  congr 1
  · congr 1
    apply sum_congr rfl
    intro a ha
    ring
  · apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    split_ifs <;> ring

lemma cutCost_identity (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (B : BlockAssignment p) (s : Copy p → Copy p) (hs : ValidCuts B s) :
    cutCost G x q B s = constantCost G x q+variableCost G x q B s := by
  have hunary : (∑ a, unaryCost G x q B a (s a)) =
      ∑ v, ∑ a, 2*q^2*(4+4*((activeDegree G x q v%2:ℕ):ℝ))*cutIndicator B v a s := by
    simp_rw [unaryCost_expansion]
    exact sum_comm
  have hpair : (∑ a, ∑ b ∈ (interaction B).neighborFinset a, pairCost q B a b (s a) (s b)) =
      ∑ v, ∑ a, ∑ b, if a ≠ b then 8*q^2*cutIndicator B v a s*cutIndicator B v b s else 0 := by
    rw [graph_pairs_all q B s hs]
    have he (a b : Copy p) : (if a ≠ b then pairCost q B a b (s a) (s b) else 0) =
        ∑ v, if a ≠ b then 8*q^2*cutIndicator B v a s*cutIndicator B v b s else 0 := by
      by_cases hab : a ≠ b
      · simp only [if_pos hab,pairCost_expansion]
      · simp only [if_neg hab,sum_const_zero]
    simp_rw [he]
    calc
      _ = ∑ a, ∑ v, ∑ b, if a ≠ b then 8*q^2*cutIndicator B v a s*cutIndicator B v b s else 0 := by
        apply sum_congr rfl
        intro a ha
        exact sum_comm
      _ = _ := sum_comm
  unfold cutCost constantCost variableCost
  rw [mul_sum]
  simp_rw [scaled_vertex_expansion]
  rw [sum_add_distrib,sum_add_distrib,hunary,hpair,←mul_sum]
  ring

end DeterministicCuts

-- Solutions/Sol_cut_decoding.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace DeterministicCuts
variable {N : ℕ} {p : Pairing N}

def decodeSelection (ids : Fin N → ℕ) (B : BlockAssignment p) (out : CopyIndex p → ℕ) (a : Copy p) : Copy p :=
  if h : ∃ c ∈ cutLabels B a, copyID ids c = out ((indexCopy p).symm a) then h.choose else a

lemma decodeSelection_spec (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (ids : Fin N → ℕ) (B : BlockAssignment p) (out : CopyIndex p → ℕ)
    (hout : ∀ i, out i ∈ (cutInstance G x q ids B).labels i) (a : Copy p) :
    decodeSelection ids B out a ∈ cutLabels B a ∧
      copyID ids (decodeSelection ids B out a) = out ((indexCopy p).symm a) := by
  have he := hout ((indexCopy p).symm a)
  change out ((indexCopy p).symm a) ∈ encodedLabels ids B (indexCopy p ((indexCopy p).symm a)) at he
  rw [Equiv.apply_symm_apply] at he
  have hex : ∃ c ∈ cutLabels B a, copyID ids c = out ((indexCopy p).symm a) := mem_image.mp he
  unfold decodeSelection
  rw [dif_pos hex]
  exact hex.choose_spec

lemma decodeSelection_valid (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (ids : Fin N → ℕ) (B : BlockAssignment p) (out : CopyIndex p → ℕ)
    (hout : ∀ i, out i ∈ (cutInstance G x q ids B).labels i) :
    ValidCuts B (decodeSelection ids B out) := by
  intro a ha
  have hh := (decodeSelection_spec G x q ids B out hout a).1
  simpa only [cutLabels,if_pos ha] using hh

lemma decoded_cost (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (ids : Fin N → ℕ) (hi : Function.Injective ids) (B : BlockAssignment p) (out : CopyIndex p → ℕ)
    (hout : ∀ i, out i ∈ (cutInstance G x q ids B).labels i) :
    cost (cutInstance G x q ids B) out = variableCost G x q B (decodeSelection ids B out) := by
  let s := decodeSelection ids B out
  have hs := decodeSelection_spec G x q ids B out hout
  have hID (i : CopyIndex p) : copyID ids (s (indexCopy p i)) = out i := by
    simpa only [Equiv.symm_apply_apply] using (hs (indexCopy p i)).2
  have hu (i : CopyIndex p) : (cutInstance G x q ids B).unaryCost i (out i) =
      unaryCost G x q B (indexCopy p i) (s (indexCopy p i)) := by
    change encodedUnary G x q ids B (indexCopy p i) (out i) = _
    rw [←hID i]
    exact encodedUnary_on_labels G x q ids hi B _ _ (hs _).1
  have hp (i j : CopyIndex p) : (cutInstance G x q ids B).pairCost i j (out i) (out j) =
      pairCost q B (indexCopy p i) (indexCopy p j) (s (indexCopy p i)) (s (indexCopy p j)) := by
    change encodedPair q ids B (indexCopy p i) (indexCopy p j) (out i) (out j) = _
    rw [←hID i,←hID j]
    exact encodedPair_on_labels q ids hi B _ _ _ _ (hs _).1 (hs _).1
  unfold cost
  simp_rw [hu,hp]
  rw [sum_indexCopy (p:=p) (fun a => unaryCost G x q B a (s a))]
  change _+(∑ i : CopyIndex p, ∑ j ∈ ((interaction B).comap (indexCopy p)).neighborFinset i,
    pairCost q B (indexCopy p i) (indexCopy p j) (s (indexCopy p i)) (s (indexCopy p j))) = _
  have he := fun i : CopyIndex p => comap_neighbor_sum (indexCopy p) (interaction B)
    (fun b => pairCost q B (indexCopy p i) b (s (indexCopy p i)) (s b)) i
  simp_rw [he]
  rw [sum_indexCopy (p:=p) (fun a => ∑ b ∈ (interaction B).neighborFinset a, pairCost q B a b (s a) (s b))]
  rfl

end DeterministicCuts

-- Solutions/Sol_product_expectation.lean

open Classical Finset
noncomputable section
namespace FiniteProductLaw
variable {V L : Type} [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L]

def expectation (p : V → L → ℝ) (f : (V → L) → ℝ) : ℝ := ∑ s, mass p s*f s

lemma expectation_add (p : V → L → ℝ) (f g : (V → L) → ℝ) :
    expectation p (fun s => f s+g s) = expectation p f+expectation p g := by
  simp only [expectation,mul_add,sum_add_distrib]

lemma expectation_sum {J : Type} (p : V → L → ℝ) (S : Finset J) (f : J → (V → L) → ℝ) :
    expectation p (fun s => ∑ j ∈ S, f j s) = ∑ j ∈ S, expectation p (f j) := by
  simp only [expectation,mul_sum]
  exact sum_comm

lemma expectation_const (p : V → L → ℝ) (hn : ∀ v, (∑ a, p v a) = 1) (c : ℝ) :
    expectation p (fun _ => c) = c := by
  unfold expectation
  rw [←sum_mul,normalize p hn,one_mul]

lemma expectation_unary (p : V → L → ℝ) (hn : ∀ v, (∑ a, p v a) = 1) (v : V) (f : L → ℝ) :
    expectation p (fun s => f (s v)) = ∑ a, p v a*f a := by
  have he (s : V → L) : f (s v) = ∑ a, if s v = a then f a else 0 := by simp
  have hex : expectation p (fun s => f (s v)) =
      expectation p (fun s => ∑ a, if s v = a then f a else 0) := by
    unfold expectation
    apply sum_congr rfl
    intro s hs
    dsimp only
    rw [he s]
  rw [hex,expectation_sum]
  apply sum_congr rfl
  intro a ha
  unfold expectation
  have hterm (s : V → L) : mass p s*(if s v = a then f a else 0) =
      (if s v = a then mass p s else 0)*f a := by split_ifs <;> ring
  simp only [hterm,←sum_mul,marginal p hn v a]

lemma expectation_pair (p : V → L → ℝ) (hn : ∀ v, (∑ a, p v a) = 1)
    (v u : V) (hvu : v ≠ u) (f : L → L → ℝ) :
    expectation p (fun s => f (s v) (s u)) = ∑ a, ∑ b, p v a*p u b*f a b := by
  have he (s : V → L) : f (s v) (s u) = ∑ a, ∑ b, if s v = a ∧ s u = b then f a b else 0 := by
    simp only [ite_and]
    rw [sum_eq_single (s v)]
    · simp only [ite_true,sum_ite_eq,mem_univ,ite_true]
    · intro a ha hne
      simp only [if_neg (Ne.symm hne),sum_const_zero]
    · exact fun h => (h (mem_univ _)).elim
  have hex : expectation p (fun s => f (s v) (s u)) =
      expectation p (fun s => ∑ a, ∑ b, if s v = a ∧ s u = b then f a b else 0) := by
    unfold expectation
    apply sum_congr rfl
    intro s hs
    dsimp only
    rw [he s]
  rw [hex,expectation_sum]
  apply sum_congr rfl
  intro a ha
  rw [expectation_sum]
  apply sum_congr rfl
  intro b hb
  unfold expectation
  have hterm (s : V → L) : mass p s*(if s v = a ∧ s u = b then f a b else 0) =
      (if s v = a ∧ s u = b then mass p s else 0)*f a b := by split_ifs <;> ring
  simp only [hterm,←sum_mul,joint p hn v u hvu a b]

end FiniteProductLaw

-- Solutions/Sol_cut_expectation.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace DeterministicCuts
variable {N : ℕ} {p : Pairing N}

lemma constantCost_nonneg (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ) :
    0 ≤ constantCost G x q := by unfold constantCost; positivity

lemma variableCost_nonneg (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (B : BlockAssignment p) (s : Copy p → Copy p) : 0 ≤ variableCost G x q B s := by
  apply add_nonneg
  · exact sum_nonneg (fun a _ => unaryCost_nonneg G x q B a (s a))
  · exact sum_nonneg (fun a _ => sum_nonneg (fun b _ => pairCost_nonneg q B a b (s a) (s b)))

lemma expectedCutCost_identity (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (B : BlockAssignment p) (ell : ℕ) (hell : 2 ≤ ell) (hB : ValidBlocks ell B) :
    FiniteProductLaw.expectation (cutProbability B) (cutCost G x q B) =
      constantCost G x q+FiniteProductLaw.expectation (cutProbability B) (variableCost G x q B) := by
  have hmu := independentCuts B ell hell hB
  have he : FiniteProductLaw.expectation (cutProbability B) (cutCost G x q B) =
      FiniteProductLaw.expectation (cutProbability B) (fun s => constantCost G x q+variableCost G x q B s) := by
    unfold FiniteProductLaw.expectation
    apply sum_congr rfl
    intro s hs
    by_cases hm : FiniteProductLaw.mass (cutProbability B) s = 0
    · simp only [hm,zero_mul]
    · rw [cutCost_identity G x q B s (hmu.2.2.1 s hm)]
  rw [he,FiniteProductLaw.expectation_add,FiniteProductLaw.expectation_const _ (cutProbability_normalize B ell hell hB)]

lemma cut_cost_from_rounding (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ)
    (hx : NonnegativeAssignment G x) (q : ℝ) (hq : 0 < q)
    (hp : ValidPairing G x q p) (B : BlockAssignment p) (ell : ℕ) (hell : 2 ≤ ell)
    (hB : ValidBlocks ell B) (s : Copy p → Copy p) (hs : ValidCuts B s)
    (hround : variableCost G x q B s ≤ (11/10:ℝ)*
      FiniteProductLaw.expectation (cutProbability B) (variableCost G x q B)) :
    cutCost G x q B s ≤ 8*penalty G x/(ell:ℝ)^2+72*q*totalWeight G x := by
  have hmu := independentCuts B ell hell hB
  have hE := lemma_3_4 N G x hx q hq ell hell p hp B hB _ hmu
  have hEnonneg : 0 ≤ FiniteProductLaw.expectation (cutProbability B) (variableCost G x q B) := by
    exact sum_nonneg (fun s _ => mul_nonneg (hmu.1 s) (variableCost_nonneg G x q B s))
  have hF0 := constantCost_nonneg G x q
  change FiniteProductLaw.expectation (cutProbability B) (cutCost G x q B) ≤ _ at hE
  rw [expectedCutCost_identity G x q B ell hell hB] at hE
  rw [cutCost_identity G x q B s hs]
  simp only [div_eq_mul_inv] at hE ⊢
  nlinarith

end DeterministicCuts

-- Solutions/Sol_cut_expected_cost.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace DeterministicCuts
variable {N : ℕ} {p : Pairing N}

lemma uniform_sum (B : BlockAssignment p) (a : Copy p) (f : Copy p → ℝ) :
    (∑ c, cutProbability B a c*f c) =
      ∑ c ∈ cutLabels B a, (1/((cutLabels B a).card:ℝ))*f c := by
  have hf : univ.filter (fun c => c ∈ cutLabels B a) = cutLabels B a := by ext c; simp
  simp only [cutProbability,ite_mul,zero_mul,sum_ite,hf,sum_const_zero,add_zero]

lemma uniform_pair_sum (B : BlockAssignment p) (a b : Copy p) (f : Copy p → Copy p → ℝ) :
    (∑ c, ∑ d, cutProbability B a c*cutProbability B b d*f c d) =
      ∑ c ∈ cutLabels B a, ∑ d ∈ cutLabels B b,
        (1/((cutLabels B a).card:ℝ))*(1/((cutLabels B b).card:ℝ))*f c d := by
  calc
    _ = ∑ c, cutProbability B a c*(∑ d, cutProbability B b d*f c d) := by
      apply sum_congr rfl
      intro c hc
      rw [mul_sum]
      apply sum_congr rfl
      intro d hd
      ring
    _ = ∑ c ∈ cutLabels B a, (1/((cutLabels B a).card:ℝ))*(∑ d, cutProbability B b d*f c d) :=
      uniform_sum B a _
    _ = _ := by
      apply sum_congr rfl
      intro c hc
      rw [uniform_sum,mul_sum]
      apply sum_congr rfl
      intro d hd
      ring

lemma expectedCost_eq_product (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (B : BlockAssignment p) (ell : ℕ) (hell : 2 ≤ ell) (hB : ValidBlocks ell B) :
    expectedCost G x q B =
      FiniteProductLaw.expectation (cutProbability B) (variableCost G x q B) := by
  have hn := cutProbability_normalize B ell hell hB
  unfold expectedCost variableCost
  rw [FiniteProductLaw.expectation_add,FiniteProductLaw.expectation_sum,FiniteProductLaw.expectation_sum]
  congr 1
  · apply sum_congr rfl
    intro a ha
    rw [FiniteProductLaw.expectation_unary _ hn,uniform_sum]
    rfl
  · apply sum_congr rfl
    intro a ha
    rw [FiniteProductLaw.expectation_sum]
    apply sum_congr rfl
    intro b hb
    rw [FiniteProductLaw.expectation_pair _ hn a b ((SimpleGraph.mem_neighborFinset (interaction B) a b).mp hb).1,
      uniform_pair_sum]
    rfl

end DeterministicCuts

-- Solutions/Sol_cut_reference.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace DeterministicCuts

def PairwiseCorrect (A : Deterministic (ℝ × ℕ) ObjectiveInput ℕ) : Prop :=
  ∀ (n : ℕ) (D : PairwiseInstance n) (lambda : ℝ) (zeta : ℕ) (col : Fin n → ℕ),
    ValidObjective D lambda → Proper D.graph zeta col →
    finiteExpectation D (utility D)-finiteExpectation D (cost D) ≥ (1/2)*finiteExpectation D (utility D) →
    ∀ ids : Fin n → ℕ, Function.Injective ids →
      let s := execute A D.graph (lambda,zeta) ids (objectiveInput D ids col)
      (∀ v, s v ∈ D.labels v ∧ 0 < D.probability v (s v)) ∧
      utility D s-cost D s ≥ (9/10)*(finiteExpectation D (utility D)-finiteExpectation D (cost D))

variable {N : ℕ} {p : Pairing N}

def referenceOutput (A : Deterministic (ℝ × ℕ) ObjectiveInput ℕ)
    (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ) (ids : Fin N → ℕ)
    (B : BlockAssignment p) (col : Copy p → ℕ) (ell zeta : ℕ) : CopyIndex p → ℕ :=
  let D := cutInstance G x q ids B
  let colors := fun i => col (indexCopy p i)
  let identities := fun i => copyID ids (indexCopy p i)
  execute A D.graph (1/(65*(ell:ℝ)+1),zeta) identities (objectiveInput D identities colors)

def referenceCuts (A : Deterministic (ℝ × ℕ) ObjectiveInput ℕ)
    (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ) (ids : Fin N → ℕ)
    (B : BlockAssignment p) (col : Copy p → ℕ) (ell zeta : ℕ) : Copy p → Copy p :=
  decodeSelection ids B (referenceOutput A G x q ids B col ell zeta)

lemma reference_good (A : Deterministic (ℝ × ℕ) ObjectiveInput ℕ) (hA : PairwiseCorrect A)
    (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (hx : NonnegativeAssignment G x)
    (q : ℝ) (hq : 0 < q) (ids : Fin N → ℕ) (hi : Function.Injective ids)
    (hp : ValidPairing G x q p) (B : BlockAssignment p) (ell : ℕ) (hell : 2 ≤ ell)
    (hB : ValidBlocks ell B) (col : Copy p → ℕ) (zeta : ℕ) (hcol : ReusableColors G ell zeta col) :
    ValidCuts B (referenceCuts A G x q ids B col ell zeta) ∧
      cutCost G x q B (referenceCuts A G x q ids B col ell zeta) ≤
        8*penalty G x/(ell:ℝ)^2+72*q*totalWeight G x := by
  let D := cutInstance G x q ids B
  let colors := fun i => col (indexCopy p i)
  let identities := fun i => copyID ids (indexCopy p i)
  have hD := cutInstance_valid G x q ids hi B ell hell hB
  have hc0 := interaction_proper G x q hp B ell hB zeta col hcol
  have hc : Proper D.graph zeta colors :=
    ⟨fun i => hc0.1 _,fun i j hij => hc0.2 _ _ hij⟩
  have hid : Function.Injective identities :=
    (copyID_injective ids hi).comp (indexCopy p).injective
  have hE := instance_expectations G x q ids hi B ell hell hB
  have hgap : finiteExpectation D (utility D)-finiteExpectation D (cost D) ≥
      (1/2)*finiteExpectation D (utility D) := by
    rw [hE.1,hE.2]
    ring_nf
    exact le_refl _
  have hout := hA _ D (1/(65*(ell:ℝ)+1)) zeta colors hD hc hgap identities hid
  have hs := fun i => (hout.1 i).1
  have hvalid : ValidCuts B (referenceCuts A G x q ids B col ell zeta) :=
    decodeSelection_valid G x q ids B _ hs
  refine ⟨hvalid,?_⟩
  apply cut_cost_from_rounding G x hx q hq hp B ell hell hB _ hvalid
  have hv := hout.2
  change utility D (referenceOutput A G x q ids B col ell zeta)-
    cost D (referenceOutput A G x q ids B col ell zeta) ≥ _ at hv
  rw [instance_utility_constant G x q ids B,decoded_cost G x q ids hi B (referenceOutput A G x q ids B col ell zeta) hs,hE.1,hE.2] at hv
  rw [←expectedCost_eq_product G x q B ell hell hB]
  change variableCost G x q B (decodeSelection ids B _) ≤ _
  linarith

lemma reference_support (A : Deterministic (ℝ × ℕ) ObjectiveInput ℕ) (hA : PairwiseCorrect A)
    (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ) (ids : Fin N → ℕ)
    (hi : Function.Injective ids) (hp : ValidPairing G x q p) (B : BlockAssignment p)
    (ell : ℕ) (hell : 2 ≤ ell) (hB : ValidBlocks ell B) (col : Copy p → ℕ)
    (zeta : ℕ) (hcol : ReusableColors G ell zeta col) :
    ∀ i, referenceOutput A G x q ids B col ell zeta i ∈ (cutInstance G x q ids B).labels i := by
  let D := cutInstance G x q ids B
  let colors := fun i => col (indexCopy p i)
  let identities := fun i => copyID ids (indexCopy p i)
  have hD := cutInstance_valid G x q ids hi B ell hell hB
  have hc0 := interaction_proper G x q hp B ell hB zeta col hcol
  have hc : Proper D.graph zeta colors := ⟨fun i => hc0.1 _,fun i j hij => hc0.2 _ _ hij⟩
  have hid : Function.Injective identities := (copyID_injective ids hi).comp (indexCopy p).injective
  have hE := instance_expectations G x q ids hi B ell hell hB
  have hgap : finiteExpectation D (utility D)-finiteExpectation D (cost D) ≥
      (1/2)*finiteExpectation D (utility D) := by rw [hE.1,hE.2]; linarith
  have hout := hA _ D (1/(65*(ell:ℝ)+1)) zeta colors hD hc hgap identities hid
  exact fun i => (hout.1 i).1

lemma reference_decodes (A : Deterministic (ℝ × ℕ) ObjectiveInput ℕ) (hA : PairwiseCorrect A)
    (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ) (ids : Fin N → ℕ)
    (hi : Function.Injective ids) (hp : ValidPairing G x q p) (B : BlockAssignment p)
    (ell : ℕ) (hell : 2 ≤ ell) (hB : ValidBlocks ell B) (col : Copy p → ℕ)
    (zeta : ℕ) (hcol : ReusableColors G ell zeta col) (a : Copy p) :
    copyID ids (referenceCuts A G x q ids B col ell zeta a) =
      referenceOutput A G x q ids B col ell zeta ((indexCopy p).symm a) := by
  exact (decodeSelection_spec G x q ids B _
    (reference_support A hA G x q ids hi hp B ell hell hB col zeta hcol) a).2

end DeterministicCuts

-- Solutions/Sol_cut_snapshot_simulation.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace CutSnapshot

lemma comap_close {V U : Type} (H : SimpleGraph U) (f : V → U) (t : ℕ) {a b : V}
    (hc : Close (H.comap f) t a b) : Close H t (f a) (f b) := by
  obtain ⟨w,hw⟩ := hc
  have hm : ∃ path : H.Walk (f a) (f b), path.length = w.length := by
    clear hw
    induction w with
    | nil => exact ⟨.nil,rfl⟩
    | @cons a b c h w ih =>
      obtain ⟨path,hpath⟩ := ih
      have hadj : H.Adj (f a) (f b) := h
      exact ⟨.cons hadj path,by simp only [SimpleGraph.Walk.length_cons,hpath]⟩
  obtain ⟨path,hpath⟩ := hm
  exact ⟨path,hpath.trans_le hw⟩

lemma close_neighbor {V : Type} (H : SimpleGraph V) (t : ℕ) {a b c : V}
    (hab : Close H t a b) (hbc : H.Adj b c) : Close H (t+1) a c := by
  obtain ⟨w,hw⟩ := hab
  exact ⟨w.append (.cons hbc .nil),by simpa only [SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_cons,SimpleGraph.Walk.length_nil,Nat.add_zero] using Nat.succ_le_succ hw⟩

section Simulation
variable {N : ℕ} (A : Deterministic (ℝ × ℕ) ObjectiveInput ℕ)
    (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ) (hi : Function.Injective ids)
    (x : Sym2 (Fin N) → ℝ) (q : ℝ) (p : Pairing N) (B : BlockAssignment p)
    (col : Copy p → ℕ) (ell zeta : ℕ) (R : Finset PhysicalRecord)
    (hauth : authentic G ids x p B col R)
include hi hauth

lemma simulation_of_complete_ball (b : Copy p)
    (hball : ∀ c, Close (DeterministicCuts.interaction B)
      (A.program.rounds (accuracy ell,zeta)+1) b c →
      (ids c.1,physicalInput G ids x p B col c.1) ∈ R ∧
      ∀ d ∈ DeterministicCuts.cutLabels B c, (ids d.1,physicalInput G ids x p B col d.1) ∈ R) :
    (HostedSnapshot.simulate A (accuracy ell,zeta) (records R q)
      (A.program.rounds (accuracy ell,zeta)) (DeterministicCuts.copyID ids b)).map A.program.out =
      some (DeterministicCuts.referenceOutput A G x q ids B col ell zeta ((DeterministicCuts.indexCopy p).symm b)) := by
  let D := DeterministicCuts.cutInstance G x q ids B
  let identities := fun i => DeterministicCuts.copyID ids (DeterministicCuts.indexCopy p i)
  let colors := fun i => col (DeterministicCuts.indexCopy p i)
  let inp := objectiveInput D identities colors
  let T := A.program.rounds (accuracy ell,zeta)
  have hid : Function.Injective identities :=
    (DeterministicCuts.copyID_injective ids hi).comp (DeterministicCuts.indexCopy p).injective
  have hall (j : DeterministicCuts.CopyIndex p)
      (hj : Close D.graph T ((DeterministicCuts.indexCopy p).symm b) j) :
      ∃ r ∈ records R q, r.1 = identities j ∧ r.2.1 = inp j ∧ r.2.2 = (D.graph.neighborFinset j).image identities := by
    have hcopy : Close (DeterministicCuts.interaction B) T b (DeterministicCuts.indexCopy p j) := by
      have hh := comap_close (DeterministicCuts.interaction B) (DeterministicCuts.indexCopy p) T hj
      simpa only [Equiv.apply_symm_apply] using hh
    have hc := hball (DeterministicCuts.indexCopy p j) (close_mono _ _ _ (by omega) hcopy)
    have hn (c : Copy p) (hAdj : (DeterministicCuts.interaction B).Adj (DeterministicCuts.indexCopy p j) c) :=
      hball c (close_neighbor _ T hcopy hAdj)
    exact record_good G ids hi x p B col R hauth q j hc.1 hc.2 hn
  have hs := HostedSnapshot.simulate_correct A D.graph (accuracy ell,zeta) identities hid inp
    (records R q) (records_unique R q) T ((DeterministicCuts.indexCopy p).symm b) hall
  have heid : identities ((DeterministicCuts.indexCopy p).symm b) = DeterministicCuts.copyID ids b := by
    simp only [identities,Equiv.apply_symm_apply]
  rw [heid] at hs
  rw [hs,Option.map_some]
  rfl

end Simulation
end CutSnapshot

-- Solutions/Sol_cut_marks.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace CutSnapshot
variable {N : ℕ} {p : Pairing N}

lemma selected_iff_named (B : BlockAssignment p) (ell : ℕ) (hB : ValidBlocks ell B)
    (s : Copy p → Copy p) (hs : ValidCuts B s) (a : Copy p) :
    (∃ b, B b = some b ∧ s b = a) ↔ ∃ b, B a = some b ∧ s b = a := by
  constructor
  · rintro ⟨b,hb,he⟩
    have hh := (mem_filter.mp (hs b hb)).2
    rw [he] at hh
    exact ⟨b,hh,he⟩
  · rintro ⟨b,hb,he⟩
    exact ⟨b,(hB.2 a b hb).1,he⟩

lemma selected_at_leader (B : BlockAssignment p) (ell : ℕ) (hB : ValidBlocks ell B)
    (s : Copy p → Copy p) (hs : ValidCuts B s) (a b : Copy p) (hab : B a = some b) :
    (∃ c, B c = some c ∧ s c = a) ↔ s b = a := by
  rw [selected_iff_named B ell hB s hs a]
  constructor
  · rintro ⟨c,hc,he⟩
    have hcb : c = b := Option.some.inj (hc.symm.trans hab)
    rwa [hcb] at he
  · intro h
    exact ⟨b,hab,h⟩

lemma selected_none (B : BlockAssignment p) (ell : ℕ) (hB : ValidBlocks ell B)
    (s : Copy p → Copy p) (hs : ValidCuts B s) (a : Copy p) (ha : B a = none) :
    ¬∃ b, B b = some b ∧ s b = a := by
  rw [selected_iff_named B ell hB s hs a]
  rintro ⟨b,hb,he⟩
  rw [ha] at hb
  cases hb

lemma mark_of_none (A : Deterministic (ℝ × ℕ) ObjectiveInput ℕ) (k : StageParameters)
    (id : ℕ) (inp : StageInput) (R : Finset PhysicalRecord) (i : ℕ) (h : inp.leader i = none) :
    mark A k id inp R i = false := by unfold mark; rw [h]

lemma mark_of_some (A : Deterministic (ℝ × ℕ) ObjectiveInput ℕ) (k : StageParameters)
    (id : ℕ) (inp : StageInput) (R : Finset PhysicalRecord) (i : ℕ) (b : Key) (out : ℕ)
    (h : inp.leader i = some b)
    (hout : (HostedSnapshot.simulate A (accuracy k.ell,k.zeta) (records R k.q)
      (A.program.rounds (accuracy k.ell,k.zeta)) (encode b)).map A.program.out = some out) :
    mark A k id inp R i = decide (out = Nat.pair id i) := by
  unfold mark
  rw [h]
  dsimp only
  cases hsim : HostedSnapshot.simulate A (accuracy k.ell,k.zeta) (records R k.q)
      (A.program.rounds (accuracy k.ell,k.zeta)) (encode b) with
  | none => rw [hsim,Option.map_none] at hout; cases hout
  | some st =>
    rw [hsim,Option.map_some] at hout
    have he := Option.some.inj hout
    simp only [hsim,he]

end CutSnapshot

-- Solutions/Sol_cut_reports.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace CutSnapshot

lemma protocol_reports {N : ℕ} (A : Deterministic (ℝ × ℕ) ObjectiveInput ℕ)
    (G : SimpleGraph (Fin N)) (k : StageParameters) (ids : Fin N → ℕ) (hi : Function.Injective ids)
    (x : Sym2 (Fin N) → ℝ) (p : Pairing N) (hp : ValidPairing G x k.q p)
    (B : BlockAssignment p) (hB : ValidBlocks k.ell B) (col : Copy p → ℕ)
    (hvalid : ValidCuts B (DeterministicCuts.referenceCuts A G x k.q ids B col k.ell k.zeta))
    (hdecode : ∀ b, DeterministicCuts.copyID ids (DeterministicCuts.referenceCuts A G x k.q ids B col k.ell k.zeta b) =
      DeterministicCuts.referenceOutput A G x k.q ids B col k.ell k.zeta ((DeterministicCuts.indexCopy p).symm b)) :
    ReportsCuts (execute (protocol A) G k ids (physicalInput G ids x p B col)) B
      (DeterministicCuts.referenceCuts A G x k.q ids B col k.ell k.zeta) := by
  intro a
  let R := LocalFlood.flood G ids (physicalInput G ids x p B col) (physicalRounds A k) a.1
  let s := DeterministicCuts.referenceCuts A G x k.q ids B col k.ell k.zeta
  change (protocol A).program.output G k ids (physicalInput G ids x p B col) (fun _ _ => false) a.1 a.2.val = true ↔ _
  rw [protocol_output]
  change mark A k (ids a.1) (physicalInput G ids x p B col a.1) R a.2.val = true ↔ _
  have hauth : authentic G ids x p B col R :=
    LocalFlood.flood_authentic G ids (physicalInput G ids x p B col) (physicalRounds A k) a.1
  have hleader : (physicalInput G ids x p B col a.1).leader a.2.val = (B a).map (copyKey ids) := by
    simp only [physicalInput,stageInput,dif_pos a.2.isLt,Option.bind_some]
  cases hBa : B a with
  | none =>
    have hl : (physicalInput G ids x p B col a.1).leader a.2.val = none := by rw [hleader,hBa,Option.map_none]
    rw [mark_of_none A k (ids a.1) _ R a.2.val hl]
    simp only [Bool.false_eq_true,false_iff]
    exact selected_none B k.ell hB s hvalid a hBa
  | some b =>
    let T := A.program.rounds (accuracy k.ell,k.zeta)
    have hball (c : Copy p) (hc : Close (DeterministicCuts.interaction B) (T+1) b c) :
        (ids c.1,physicalInput G ids x p B col c.1) ∈ R ∧
        ∀ d ∈ DeterministicCuts.cutLabels B c, (ids d.1,physicalInput G ids x p B col d.1) ∈ R := by
      exact causal_snapshot_complete G ids x k.q p hp B k.ell hB col T a b hBa c hc
    have hsim := simulation_of_complete_ball A G ids hi x k.q p B col k.ell k.zeta R hauth b hball
    have hl : (physicalInput G ids x p B col a.1).leader a.2.val = some (copyKey ids b) := by
      rw [hleader,hBa,Option.map_some]
    have hm := mark_of_some A k (ids a.1) (physicalInput G ids x p B col a.1) R a.2.val (copyKey ids b)
      (DeterministicCuts.referenceOutput A G x k.q ids B col k.ell k.zeta ((DeterministicCuts.indexCopy p).symm b)) hl hsim
    rw [hm,decide_eq_true_eq,←hdecode b]
    change DeterministicCuts.copyID ids (s b) = DeterministicCuts.copyID ids a ↔ _
    have hselected := selected_at_leader B k.ell hB s hvalid a b hBa
    constructor
    · intro he
      exact hselected.mpr (DeterministicCuts.copyID_injective ids hi he)
    · intro he
      exact congrArg (DeterministicCuts.copyID ids) (hselected.mp he)

end CutSnapshot

-- Solutions/Sol_cut_runtime.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace CutSnapshot

lemma cut_log_bound (ell : ℕ) (hell : 2 ≤ ell) :
    1 ≤ logTwo (ell:ℝ) ∧ 0 ≤ logTwo (65*(ell:ℝ)+1) ∧
      logTwo (65*(ell:ℝ)+1) ≤ 8*logTwo (ell:ℝ) := by
  have hel : (2:ℝ) ≤ ell := by exact_mod_cast hell
  have hp : (0:ℝ) < ell := by linarith
  have hL : 1 ≤ logTwo (ell:ℝ) := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ) < 2) hp).mpr
    simpa only [Real.rpow_one] using hel
  have hm : (0:ℝ) < 65*(ell:ℝ)+1 := by positivity
  have h0 : 0 ≤ logTwo (65*(ell:ℝ)+1) := Real.logb_nonneg (by norm_num) (by linarith)
  have hh : logTwo (65*(ell:ℝ)+1) ≤ logTwo (128*(ell:ℝ)) :=
    Real.logb_le_logb_of_le (by norm_num) hm (by linarith)
  have h128 : logTwo 128 = 7 := by
    change Real.logb 2 (128:ℝ) = 7
    rw [show (128:ℝ) = 2^7 by norm_num,Real.logb_pow]
    norm_num
  have he : logTwo (128*(ell:ℝ)) = 7+logTwo (ell:ℝ) := by
    unfold logTwo
    rw [Real.logb_mul (by norm_num) hp.ne']
    change logTwo 128+logTwo (ell:ℝ) = _
    rw [h128]
    rfl
  refine ⟨hL,h0,?_⟩
  rw [he] at hh
  linarith

lemma protocol_runtime (A : Deterministic (ℝ × ℕ) ObjectiveInput ℕ) (C : ℝ) (hC : 0 < C)
    (hTime : ∀ lambda zeta, 0 < lambda → lambda ≤ 1/2 → A.program.rounds (lambda,zeta) ≤
      budget C ((logTwo (1/lambda))^2+logTwo (1/lambda)*(logStar zeta:ℝ)))
    (k : StageParameters) (hell : 2 ≤ k.ell) :
    (protocol A).program.rounds k ≤ budget (1000000*(C+1))
      ((k.ell:ℝ)*((logTwo k.ell)^2+logTwo k.ell*(logStar k.zeta:ℝ)+1)) := by
  let L := logTwo (k.ell:ℝ)
  let J := logTwo (65*(k.ell:ℝ)+1)
  let S : ℝ := logStar k.zeta
  have hh := cut_log_bound k.ell hell
  have hL : 1 ≤ L := hh.1
  have hJ : 0 ≤ J := hh.2.1
  have hJL : J ≤ 8*L := hh.2.2
  have hL0 : 0 ≤ L := by linarith
  have hS : 0 ≤ S := Nat.cast_nonneg _
  have hden : (0:ℝ) < 65*(k.ell:ℝ)+1 := by positivity
  have hlambda : 0 < accuracy k.ell := one_div_pos.mpr hden
  have hhalf : accuracy k.ell ≤ 1/2 := by
    unfold accuracy
    apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2)
    have hkr : (2:ℝ) ≤ k.ell := by exact_mod_cast hell
    linarith
  have hTime' := hTime (accuracy k.ell) k.zeta hlambda hhalf
  have hf : logTwo (1/accuracy k.ell) = J := by simp only [accuracy,one_div_one_div,J]
  rw [hf] at hTime'
  have hF0 : 0 ≤ C*(J^2+J*S) := mul_nonneg hC.le (by positivity)
  have hceil : (budget C (J^2+J*S):ℝ) ≤ C*(J^2+J*S)+1 := (Nat.ceil_lt_add_one hF0).le
  have hTr : (A.program.rounds (accuracy k.ell,k.zeta):ℝ) ≤ C*(J^2+J*S)+1 :=
    (show (A.program.rounds (accuracy k.ell,k.zeta):ℝ) ≤ (budget C (J^2+J*S):ℝ) by exact_mod_cast hTime').trans hceil
  have hJsq : J^2 ≤ 64*L^2 := by nlinarith
  have hJS : J*S ≤ 8*(L*S) := by nlinarith [mul_le_mul_of_nonneg_right hJL hS]
  have hscaled := mul_le_mul_of_nonneg_left (add_le_add hJsq hJS) hC.le
  have hbound : 256*((A.program.rounds (accuracy k.ell,k.zeta):ℝ)+2) ≤
      1000000*(C+1)*(L^2+L*S+1) := by
    have h1 := mul_nonneg hC.le (sq_nonneg L)
    have h2 := mul_nonneg hC.le (mul_nonneg hL0 hS)
    nlinarith [sq_nonneg L,mul_nonneg hL0 hS]
  have hreal : ((protocol A).program.rounds k:ℝ) ≤
      1000000*(C+1)*((k.ell:ℝ)*(L^2+L*S+1)) := by
    change ((256*k.ell*(A.program.rounds (accuracy k.ell,k.zeta)+2):ℕ):ℝ) ≤ _
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg k.ell)]
  exact_mod_cast hreal.trans (Nat.le_ceil (1000000*(C+1)*((k.ell:ℝ)*(L^2+L*S+1))))

end CutSnapshot

-- Solutions/Sol_deterministic_cuts.lean
open FasterDistributedMatching.ApproximateMatching

/- Lemma 3.5, printed p.11 / PDF p.13 (implementation continues p.14).
The ell factor multiplies the entire bracket. Both 8 and 72 are literal source constants. -/
theorem solution :
    ∃ (A : Deterministic StageParameters StageInput (ℕ → Bool)) (C : ℝ), 0 < C ∧
      (∀ k, 2 ≤ k.ell → A.program.rounds k ≤ budget C
        (k.ell * ((logTwo k.ell) ^ 2 + logTwo k.ell * (logStar k.zeta : ℝ) + 1))) ∧
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (k : StageParameters),
        2 ≤ k.ell → 0 < k.q → boundedGraph G k.n k.degree →
        ∀ (x : Sym2 (Fin N) → ℝ), NonnegativeAssignment G x →
          ∀ (p : Pairing N), ValidPairing G x k.q p →
            ∀ (B : BlockAssignment p), ValidBlocks k.ell B →
              ∀ col : Copy p → ℕ, ReusableColors G k.ell k.zeta col →
                ∀ ids : Fin N → ℕ, Function.Injective ids →
                  ∃ s : Copy p → Copy p, ValidCuts B s ∧
                    ReportsCuts (execute A G k ids (stageInput G ids x p (some B) (some col)
                      (fun _ => false) (fun _ => none))) B s ∧
                    cutCost G x k.q B s ≤
                      8 * penalty G x / (k.ell : ℝ) ^ 2 + 72 * k.q * totalWeight G x  := by
  obtain ⟨A,C,hC,hTime,hA⟩ := lemma_2_2
  refine ⟨CutSnapshot.protocol A,1000000*(C+1),by positivity,?_,?_⟩
  · intro k hell
    exact CutSnapshot.protocol_runtime A C hC hTime k hell
  · intro N G k hell hq hbounds x hx p hp B hB col hcol ids hi
    let s := DeterministicCuts.referenceCuts A G x k.q ids B col k.ell k.zeta
    have hg := DeterministicCuts.reference_good A hA G x hx k.q hq ids hi hp B k.ell hell hB col k.zeta hcol
    refine ⟨s,hg.1,?_,hg.2⟩
    exact CutSnapshot.protocol_reports A G k ids hi x p hp B hB col hg.1
      (DeterministicCuts.reference_decodes A hA G x k.q ids hi hp B k.ell hell hB col k.zeta hcol)


