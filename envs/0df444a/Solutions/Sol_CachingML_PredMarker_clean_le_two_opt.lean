-- Prove2me | solution 1 for CachingML.PredMarker.clean_le_two_opt
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-24T03:32:13.938793+00:00
-- url     : https://prove2.me/submissions/3c5590db-5093-4370-88f5-c5b7b19125a8

import Init
import Definitions.Def_CachingML_PredMarker_opt
import Definitions.Def_CachingML_PredMarker_cleanCount

namespace CacheCharging
variable {α : Type*} [DecidableEq α]

inductive Run (k : ℕ) : Finset α → List α → Finset α → ℕ → Prop
  | nil (C : Finset α) (hC : C.card ≤ k) : Run k C [] C 0
  | hit {C E : Finset α} {z : α} {τ : List α} {n : ℕ}
      (hz : z ∈ C) (tail : Run k C τ E n) : Run k C (z::τ) E n
  | miss {C D E : Finset α} {z : α} {τ : List α} {n : ℕ}
      (hC : C.card ≤ k) (hz : z ∉ C) (hload : z ∈ D)
      (hD : D ⊆ insert z C) (tail : Run k D τ E n) : Run k C (z::τ) E (1+n)

namespace Run
variable {k : ℕ} {C E : Finset α} {σ : List α} {n : ℕ}

theorem start_capacity (h : Run k C σ E n) : C.card ≤ k := by
  induction h with
  | nil C hC => exact hC
  | hit hz tail ih => exact ih
  | miss hC hz hload hD tail ih => exact hC

theorem end_capacity (h : Run k C σ E n) : E.card ≤ k := by
  induction h with
  | nil C hC => exact hC
  | hit hz tail ih => exact ih
  | miss hC hz hload hD tail ih => exact ih

theorem distinct_misses (h : Run k C σ E n) : (σ.toFinset \ C).card ≤ n := by
  induction h with
  | nil C hC => simp
  | @hit C E z τ n hz tail ih =>
    simpa [List.toFinset_cons, Finset.insert_sdiff_of_mem _ hz] using ih
  | @miss C D E z τ n hC hz hload hD tail ih =>
    have hs : (z::τ).toFinset \ C ⊆ insert z (τ.toFinset \ D) := by
      intro x hx
      simp only [List.toFinset_cons, Finset.mem_sdiff, Finset.mem_insert] at hx ⊢
      rcases hx with ⟨hx,hxC⟩
      rcases hx with rfl | hxT
      · exact Or.inl rfl
      · by_cases hxz : x = z
        · exact Or.inl hxz
        · refine Or.inr ⟨hxT, ?_⟩
          intro hxD
          have := hD hxD
          simp only [Finset.mem_insert] at this
          exact this.elim hxz hxC
    have hc := Finset.card_le_card hs
    have hi := Finset.card_insert_le z (τ.toFinset \ D)
    omega

theorem append {D : Finset α} {τ : List α} {m : ℕ}
    (h₁ : Run k C σ D n) (h₂ : Run k D τ E m) : Run k C (σ++τ) E (n+m) := by
  induction h₁ with
  | nil C hC => simpa using h₂
  | hit hz tail ih => exact .hit hz (ih h₂)
  | miss hC hz hload hD tail ih =>
    simpa [Nat.add_assoc] using Run.miss hC hz hload hD (ih h₂)

theorem split {τ : List α} (h : Run k C (σ++τ) E n) :
    ∃ D a b, Run k C σ D a ∧ Run k D τ E b ∧ n = a+b := by
  induction σ generalizing C n with
  | nil => exact ⟨C,0,n,.nil C h.start_capacity,h,by simp⟩
  | cons z σ ih =>
    cases h with
    | hit hz tail =>
      obtain ⟨D,a,b,h₁,h₂,hn⟩ := ih tail
      exact ⟨D,a,b,.hit hz h₁,h₂,hn⟩
    | miss hC hz hload hD tail =>
      obtain ⟨D,a,b,h₁,h₂,hn⟩ := ih tail
      exact ⟨D,1+a,b,.miss hC hz hload hD h₁,h₂,by omega⟩

theorem two_phase {τ : List α} (h : Run k C (σ++τ) E n)
    (hσ : σ.toFinset.card = k) : (τ.toFinset \ σ.toFinset).card ≤ n := by
  have ha := h.distinct_misses
  have hb := Finset.card_le_card_sdiff_add_card (s := (σ++τ).toFinset) (t := C)
  have hc := h.start_capacity
  have hd := Finset.card_sdiff_add_card τ.toFinset σ.toFinset
  rw [List.toFinset_append] at ha hb
  rw [Finset.union_comm τ.toFinset σ.toFinset, hσ] at hd
  omega

theorem first_phase (h : Run k ∅ σ E n) : σ.toFinset.card ≤ n := by
  simpa using h.distinct_misses

end Run

open CachingML.PredMarker

theorem optimal_run (k : ℕ) (hk : 1 ≤ k) (C : Finset α) (hC : C.card ≤ k) (σ : List α) :
    ∃ E, Run k C σ E (optFrom k C σ) := by
  induction σ generalizing C with
  | nil => exact ⟨C,.nil C hC⟩
  | cons z τ ih =>
    by_cases hz : z ∈ C
    · obtain ⟨E,hE⟩ := ih C hC
      exact ⟨E,by simpa [optFrom,hz] using Run.hit hz hE⟩
    · by_cases hlt : C.card < k
      · have hD : (insert z C).card ≤ k := by
          rw [Finset.card_insert_of_notMem hz]
          omega
        obtain ⟨E,hE⟩ := ih (insert z C) hD
        refine ⟨E, ?_⟩
        simpa [optFrom,hz,hlt] using
          (Run.miss hC hz (Finset.mem_insert_self z C) (Finset.Subset.refl _) hE)
      · have hne : C.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨e,he,heq⟩ := Finset.exists_mem_eq_inf' hne (fun e => optFrom k (insert z (C.erase e)) τ)
        have hz' : z ∉ C.erase e := fun h => hz (Finset.mem_of_mem_erase h)
        have hD : (insert z (C.erase e)).card ≤ k := by
          rw [Finset.card_insert_of_notMem hz', Finset.card_erase_of_mem he]
          omega
        obtain ⟨E,hE⟩ := ih (insert z (C.erase e)) hD
        refine ⟨E, ?_⟩
        rw [optFrom, if_neg hz, if_neg hlt, dif_pos hne, heq]
        exact Run.miss hC hz (Finset.mem_insert_self _ _) (Finset.insert_subset_insert _ (Finset.erase_subset _ _)) hE

end CacheCharging

namespace CacheCharging
variable {α : Type*} [DecidableEq α]

def FullPhases (k : ℕ) : List (List α) → Prop
  | [] => True
  | [_] => True
  | p::q::ps => p.toFinset.card = k ∧ FullPhases k (q::ps)

def blockClean (prev : Finset α) : List (List α) → ℕ
  | [] => 0
  | p::ps => (p.toFinset \ prev).card + blockClean p.toFinset ps

theorem FullPhases.cons {k : ℕ} {p : List α} {ps : List (List α)}
    (hp : p.toFinset.card = k) (hps : FullPhases k ps) : FullPhases k (p::ps) := by
  cases ps <;> simp_all [FullPhases]

theorem blocks_from_previous (k : ℕ) (ps : List (List α))
    (hps : FullPhases k ps) (prev : List α) (hp : prev.toFinset.card = k)
    (C D E : Finset α) (a b : ℕ) (hr : Run k C prev D a)
    (hs : Run k D ps.flatten E b) : blockClean prev.toFinset ps ≤ a+2*b := by
  induction ps generalizing prev C D E a b with
  | nil => simp [blockClean]
  | cons p ps ih =>
    change Run k D (p++ps.flatten) E b at hs
    obtain ⟨F,c,d,hpRun,htail,hb⟩ := hs.split
    have hpair := (hr.append hpRun).two_phase hp
    cases ps with
    | nil =>
      simp only [blockClean, add_zero]
      omega
    | cons q qs =>
      have hfull : p.toFinset.card = k ∧ FullPhases k (q::qs) := hps
      have ht := ih hfull.2 p hfull.1 D F E c d hpRun htail
      change (p.toFinset \ prev.toFinset).card + blockClean p.toFinset (q::qs) ≤ _
      omega

theorem blocks_bound (k : ℕ) (ps : List (List α)) (hps : FullPhases k ps)
    (E : Finset α) (n : ℕ) (hr : Run k ∅ ps.flatten E n) : blockClean ∅ ps ≤ 2*n := by
  cases ps with
  | nil => simp [blockClean]
  | cons p ps =>
    change Run k ∅ (p++ps.flatten) E n at hr
    obtain ⟨F,a,b,hp,ht,hn⟩ := hr.split
    have hc := hp.first_phase
    cases ps with
    | nil =>
      simp only [blockClean, Finset.sdiff_empty, add_zero]
      omega
    | cons q qs =>
      have hfull : p.toFinset.card = k ∧ FullPhases k (q::qs) := hps
      have hb := blocks_from_previous k (q::qs) hfull.2 p hfull.1 ∅ F E a b hp ht
      simp only [blockClean, Finset.sdiff_empty]
      change p.toFinset.card + blockClean p.toFinset (q::qs) ≤ _
      omega

end CacheCharging

namespace CacheCharging
open CachingML.PredMarker
variable {α : Type*} [DecidableEq α]

theorem decompose (k : ℕ) (hk : 1 ≤ k) (prev : Finset α) (p σ : List α)
    (hp : p.toFinset.card ≤ k) :
    ∃ ps : List (List α), ps.flatten = p++σ ∧ FullPhases k ps ∧
      blockClean prev ps = (p.toFinset \ prev).card + cleanCountAux k prev p.toFinset σ := by
  induction σ generalizing prev p with
  | nil => exact ⟨[p],by simp,by trivial,by simp [blockClean,cleanCountAux]⟩
  | cons z τ ih =>
    have hset : (p++[z]).toFinset = insert z p.toFinset := by simp
    by_cases hz : z ∈ p.toFinset
    · have hcard : (p++[z]).toFinset.card ≤ k := by simpa [hset,Finset.insert_eq_of_mem hz] using hp
      obtain ⟨ps,hflat,hfull,hclean⟩ := ih prev (p++[z]) hcard
      refine ⟨ps,by simpa [List.append_assoc] using hflat,hfull,?_⟩
      simpa [hset,Finset.insert_eq_of_mem hz,cleanCountAux,hz] using hclean
    · by_cases hlt : p.toFinset.card < k
      · have hcard : (p++[z]).toFinset.card ≤ k := by
          rw [hset,Finset.card_insert_of_notMem hz]
          omega
        obtain ⟨ps,hflat,hfull,hclean⟩ := ih prev (p++[z]) hcard
        refine ⟨ps,by simpa [List.append_assoc] using hflat,hfull,?_⟩
        by_cases hzprev : z ∈ prev
        · simpa [hset,cleanCountAux,hz,hlt,hzprev,Finset.insert_sdiff_of_mem _ hzprev] using hclean
        · have hs : insert z p.toFinset \ prev = insert z (p.toFinset \ prev) := by
            ext x
            simp only [Finset.mem_sdiff,Finset.mem_insert]
            aesop
          have hnot : z ∉ p.toFinset \ prev := fun h => hz (Finset.mem_sdiff.mp h).1
          simpa [hset,cleanCountAux,hz,hlt,hzprev,hs,Finset.card_insert_of_notMem hnot,Nat.add_assoc] using hclean
      · have hfullp : p.toFinset.card = k := by omega
        obtain ⟨ps,hflat,hfull,hclean⟩ := ih p.toFinset [z] (by simpa using hk)
        refine ⟨p::ps,by simpa [hflat,List.append_assoc],FullPhases.cons hfullp hfull,?_⟩
        simp only [blockClean]
        rw [hclean]
        have hsg : ({z} \ p.toFinset : Finset α) = {z} := by
          ext x
          simp only [Finset.mem_sdiff,Finset.mem_singleton]
          aesop
        simp [cleanCountAux,hz,hlt,hsg,Nat.add_assoc]

theorem clean_bound (k : ℕ) (hk : 1 ≤ k) (σ : List α) :
    cleanCount k σ ≤ 2 * opt k σ := by
  obtain ⟨ps,hflat,hfull,hclean⟩ := decompose k hk ∅ [] σ (by simp)
  obtain ⟨E,hr⟩ := optimal_run k hk (∅ : Finset α) (by simp) σ
  simp only [List.nil_append] at hflat
  have hb := blocks_bound k ps hfull E (opt k σ) (by simpa [hflat,opt] using hr)
  simpa [hclean,cleanCount] using hb

end CacheCharging

theorem solution {α : Type*} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k) (σ : List α) :
    CachingML.PredMarker.cleanCount k σ ≤ 2 * CachingML.PredMarker.opt k σ :=
  CacheCharging.clean_bound k hk σ
