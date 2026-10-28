-- Prove2me | solution 1 for CachingML.PredMarker.predictiveMarker_competitive
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-26T08:30:54.276974+00:00
-- url     : https://prove2.me/submissions/865923e4-d7d5-4f65-9d14-72d342ebd328

-- SPDX-License-Identifier: Apache-2.0

import Definitions.Def_CachingML_PredMarker_cleanCount
import Definitions.Def_CachingML_PredMarker_opt
import Definitions.Def_CachingML_PredMarker_predError
import Definitions.Def_CachingML_PredMarker_predictiveMarker
import Definitions.Def_CachingML_PredMarker_spread
import Mathlib


section

open scoped ENNReal

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

def savePrediction (s : PMState α) (i : ℕ) (z : α) (hz : ℝ) : PMState α :=
  { s with pred := Function.update s.pred z hz, predIdx := Function.update s.predIdx z i}

def hitOrFill (s : PMState α) (z : α) : PMState α :=
  { s with
    cache := insert z s.cache
    marked := insert z s.marked
    misses := if z ∈ s.cache then s.misses else s.misses + 1}

def phaseStart (k : ℕ) (s : PMState α) : PMState α :=
  if s.marked.card = k then
    { s with phase := s.phase + 1, clean := 0, stale := s.cache, marked := ∅}
  else s

def cleanState (s : PMState α) : PMState α :=
  { s with
    clean := s.clean + 1
    chainLen := Function.update s.chainLen s.phase
      (Function.update (s.chainLen s.phase) (s.clean + 1) 1)}

def staleState (s : PMState α) (z : α) : PMState α :=
  { s with
    chainLen := Function.update s.chainLen s.phase
      (Function.update (s.chainLen s.phase) (s.chainOf z) (s.chainLen s.phase (s.chainOf z) + 1))}

noncomputable def randomEviction (s : PMState α) (z : α) (c : ℕ) : PMF (PMState α) :=
  if hne : (s.cache \ s.marked).Nonempty then
    (PMF.uniformOfFinset (s.cache \ s.marked) hne).map (fun e =>
      evictInto { s with randomChains := insert (s.phase, c) s.randomChains} z c e)
  else PMF.pure (evictInto s z c z)

theorem step_factored (k : ℕ) (tb : PMState α → α) (s : PMState α)
    (i : ℕ) (z : α) (hz : ℝ) :
    step k tb s i z hz =
      let t := savePrediction s i z hz
      if z ∈ t.cache ∨ t.cache.card < k then PMF.pure (hitOrFill t z)
      else
        let u := phaseStart k t
        if z ∉ u.stale then
          let v := cleanState u
          PMF.pure (evictInto v z (u.clean + 1) (tb v))
        else
          let v := staleState u z
          if (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ) then
            PMF.pure (evictInto v z (u.chainOf z) (tb v))
          else randomEviction v z (u.chainOf z) := by
  rfl

theorem randomEviction_support {s : PMState α} {z : α} {c : ℕ}
    (hne : (s.cache \ s.marked).Nonempty) {t : PMState α}
    (ht : t ∈ (randomEviction s z c).support) :
    ∃ e ∈ s.cache \ s.marked,
      t = evictInto { s with randomChains := insert (s.phase, c) s.randomChains} z c e := by
  simp only [randomEviction, dif_pos hne, PMF.mem_support_map_iff] at ht
  obtain ⟨e, he, rfl⟩ := ht
  exact ⟨e, by simpa using he, rfl⟩

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

structure CacheInvariant (k : ℕ) (s : PMState α) : Prop where
  marked_subset : s.marked ⊆ s.cache
  card_le : s.cache.card ≤ k

omit [DecidableEq α] in
theorem init_cacheInvariant (k : ℕ) : CacheInvariant k (initState α) := by
  constructor <;> simp [initState]

theorem save_cacheInvariant {k : ℕ} {s : PMState α} (hs : CacheInvariant k s)
    (i : ℕ) (z : α) (hz : ℝ) : CacheInvariant k (savePrediction s i z hz) := ⟨hs.marked_subset, hs.card_le⟩

theorem hitOrFill_cacheInvariant {k : ℕ} {s : PMState α} (hs : CacheInvariant k s)
    {z : α} (h : z ∈ s.cache ∨ s.cache.card < k) : CacheInvariant k (hitOrFill s z) := by
  constructor
  · exact Finset.insert_subset_insert z hs.marked_subset
  · change (insert z s.cache).card ≤ k
    rcases h with h | h
    · simpa [Finset.insert_eq_of_mem h] using hs.card_le
    · exact (Finset.card_insert_le z s.cache).trans (by omega)

omit [DecidableEq α] in
omit [DecidableEq α] in
theorem phaseStart_cacheInvariant {k : ℕ} {s : PMState α} (hs : CacheInvariant k s) :
    CacheInvariant k (phaseStart k s) := by
  unfold phaseStart
  split_ifs
  · exact ⟨Finset.empty_subset _, hs.card_le⟩
  · exact hs

omit [DecidableEq α] in
theorem phaseStart_cache (k : ℕ) (s : PMState α) : (phaseStart k s).cache = s.cache := by
  unfold phaseStart
  split_ifs <;> rfl

theorem phaseStart_candidates_nonempty {k : ℕ} (hk : 1 ≤ k) {s : PMState α}
    (hs : CacheInvariant k s) (hfull : s.cache.card = k) :
    ((phaseStart k s).cache \ (phaseStart k s).marked).Nonempty := by
  unfold phaseStart
  split_ifs with hm
  · simpa using (Finset.card_pos.mpr (show s.cache.Nonempty from
      Finset.card_pos.mp (by omega)))
  · apply Finset.card_pos.mp
    rw [Finset.card_sdiff_of_subset hs.marked_subset, hfull]
    have := Finset.card_le_card hs.marked_subset
    omega

theorem evictInto_cacheInvariant {k : ℕ} {s : PMState α} (hs : CacheInvariant k s)
    (z : α) (c : ℕ) {e : α} (he : e ∈ s.cache \ s.marked) :
    CacheInvariant k (evictInto s z c e) := by
  obtain ⟨hec, hem⟩ := Finset.mem_sdiff.mp he
  constructor
  · change insert z s.marked ⊆ insert z (s.cache.erase e)
    apply Finset.insert_subset_insert
    intro x hx
    exact Finset.mem_erase.mpr ⟨ne_of_mem_of_not_mem hx hem, hs.marked_subset hx⟩
  · change (insert z (s.cache.erase e)).card ≤ k
    calc
      _ ≤ (s.cache.erase e).card + 1 := Finset.card_insert_le _ _
      _ = s.cache.card := Finset.card_erase_add_one hec
      _ ≤ k := hs.card_le

theorem miss_cacheInvariant {k : ℕ} (tb : PMState α → α) (htb : IsMaxTieBreak tb)
    (u : PMState α) (hu : CacheInvariant k u)
    (hne : (u.cache \ u.marked).Nonempty) (z : α) {v : PMState α}
    (hv : v ∈ (if z ∉ u.stale then
      PMF.pure (evictInto (cleanState u) z (u.clean + 1) (tb (cleanState u)))
      else if (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ) then
        PMF.pure (evictInto (staleState u z) z (u.chainOf z) (tb (staleState u z)))
      else randomEviction (staleState u z) z (u.chainOf z)).support) :
    CacheInvariant k v := by
  by_cases hc : z ∉ u.stale
  · rw [if_pos hc] at hv
    have he := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    exact evictInto_cacheInvariant (s := cleanState u) ⟨hu.marked_subset, hu.card_le⟩ z _
      (htb (cleanState u) hne).1
  · rw [if_neg hc] at hv
    by_cases hr : (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ)
    · rw [if_pos hr] at hv
      have he := (PMF.mem_support_pure_iff _ _).mp hv
      subst v
      exact evictInto_cacheInvariant (s := staleState u z) ⟨hu.marked_subset, hu.card_le⟩ z _
        (htb (staleState u z) hne).1
    · rw [if_neg hr] at hv
      obtain ⟨e, he, rfl⟩ := randomEviction_support (s := staleState u z) hne hv
      exact evictInto_cacheInvariant
        (s := { staleState u z with randomChains := insert ((staleState u z).phase, u.chainOf z) (staleState u z).randomChains })
        ⟨hu.marked_subset, hu.card_le⟩ z _ he

theorem step_cacheInvariant {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) {s : PMState α} (hs : CacheInvariant k s)
    (i : ℕ) (z : α) (hz : ℝ) {v : PMState α}
    (hv : v ∈ (step k tb s i z hz).support) : CacheInvariant k v := by
  rw [step_factored] at hv
  dsimp only at hv
  let t := savePrediction s i z hz
  have ht : CacheInvariant k t := save_cacheInvariant hs i z hz
  by_cases hh : z ∈ t.cache ∨ t.cache.card < k
  · simp only [show z ∈ (savePrediction s i z hz).cache ∨
      (savePrediction s i z hz).cache.card < k from hh, if_pos] at hv
    have he := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    exact hitOrFill_cacheInvariant ht hh
  · simp only [show ¬ (z ∈ (savePrediction s i z hz).cache ∨
      (savePrediction s i z hz).cache.card < k) from hh, if_false] at hv
    have hf : t.cache.card = k := by have := ht.card_le; simp only [not_or] at hh; omega
    exact miss_cacheInvariant tb htb (phaseStart k t) (phaseStart_cacheInvariant ht)
      (phaseStart_candidates_nonempty hk ht hf) z hv

end CachingML.PredMarker.PMFresh
end


section

open scoped ENNReal

namespace CachingML.PredMarker.PMFresh

variable {α β γ : Type*}

theorem finite_support_bind (p : PMF α) (f : α → PMF β)
    (hp : p.support.Finite) (hf : ∀ a ∈ p.support, (f a).support.Finite) :
    (p.bind f).support.Finite := by
  rw [PMF.support_bind]
  exact hp.biUnion hf

theorem finite_support_map (p : PMF α) (f : α → β) (hp : p.support.Finite) :
    (p.map f).support.Finite := by
  rw [PMF.support_map]
  exact hp.image f

theorem fold_support_invariant (f : α → β → PMF α) (P : α → Prop)
    (hf : ∀ s, P s → ∀ b t, t ∈ (f s b).support → P t)
    (l : List β) (p : PMF α) (hp : ∀ s ∈ p.support, P s) :
    ∀ t ∈ (l.foldl (fun q b => q.bind (fun s => f s b)) p).support, P t := by
  induction l generalizing p with
  | nil => exact hp
  | cons b l ih =>
    apply ih
    intro t ht
    obtain ⟨s, hs, ht⟩ := (PMF.mem_support_bind_iff _ _ _).mp ht
    exact hf s (hp s hs) b t ht

theorem fold_finite_support (f : α → β → PMF α)
    (hf : ∀ s b, (f s b).support.Finite) (l : List β)
    (p : PMF α) (hp : p.support.Finite) :
    (l.foldl (fun q b => q.bind (fun s => f s b)) p).support.Finite := by
  induction l generalizing p with
  | nil => exact hp
  | cons b l ih =>
    apply ih
    exact finite_support_bind p _ hp (fun s _ => hf s b)

theorem randomEviction_finite_support [DecidableEq α] (s : PMState α) (z : α) (c : ℕ) :
    (randomEviction s z c).support.Finite := by
  unfold randomEviction
  split_ifs
  · apply finite_support_map
    simp
  · simp

theorem step_finite_support [DecidableEq α] (k : ℕ) (tb : PMState α → α)
    (s : PMState α) (i : ℕ) (z : α) (hz : ℝ) :
    (step k tb s i z hz).support.Finite := by
  rw [step_factored]
  dsimp only
  split_ifs <;> first | simp | exact randomEviction_finite_support _ _ _

theorem run_finite_support [DecidableEq α] (k : ℕ) (tb : PMState α → α)
    (σ : List α) (h : Fin σ.length → ℝ) : (run k tb σ h).support.Finite := by
  unfold run
  apply fold_finite_support
  · exact fun s i => step_finite_support k tb s i.val (σ.get i) (h i)
  · simp

noncomputable def pmExpectation (p : PMF α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' a, p a * f a

theorem pmExpectation_mono (p : PMF α) {f g : α → ℝ≥0∞}
    (h : ∀ a ∈ p.support, f a ≤ g a) : pmExpectation p f ≤ pmExpectation p g := by
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : a ∈ p.support
  · exact mul_le_mul le_rfl (h a ha) zero_le zero_le
  · simp only [PMF.mem_support_iff, not_not] at ha
    simp [ha]

theorem pmExpectation_const (p : PMF α) (c : ℝ≥0∞) : pmExpectation p (fun _ => c) = c := by
  simp [pmExpectation, ENNReal.tsum_mul_right]

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

structure PhaseState (α : Type*) where
  previous : Finset α
  current : Finset α
  number : ℕ

def phaseInit (α : Type*) : PhaseState α := ⟨∅, ∅, 1⟩

def phaseStep {α : Type*} [DecidableEq α] (k : ℕ) (s : PhaseState α) (z : α) : PhaseState α :=
  if z ∈ s.current then s
  else if s.current.card < k then { s with current := insert z s.current }
  else ⟨s.current, {z}, s.number + 1⟩

def phaseCharge {α : Type*} [DecidableEq α] (k : ℕ) (s : PhaseState α) (z : α) : ℕ :=
  if z ∈ s.current then 0
  else if s.current.card < k then (if z ∈ s.previous then 0 else 1)
  else 1

def phaseRun {α : Type*} [DecidableEq α] (k : ℕ) (σ : List α) : PhaseState α :=
  σ.foldl (phaseStep k) (phaseInit α)

def phaseFuture {α : Type*} [DecidableEq α] (k : ℕ) : Finset α → List α → Finset α
  | C, [] => C
  | C, z :: τ => if z ∈ C ∨ C.card < k then phaseFuture k (insert z C) τ else C

lemma subset_phaseFuture {α : Type*} [DecidableEq α] (k : ℕ) (C : Finset α) (τ : List α) :
    C ⊆ phaseFuture k C τ := by
  induction τ generalizing C with
  | nil => exact le_rfl
  | cons z τ ih =>
    simp only [phaseFuture]
    split
    · exact (Finset.subset_insert _ _).trans (ih _)
    · exact le_rfl

lemma phaseFuture_card_le {α : Type*} [DecidableEq α] (k : ℕ) (C : Finset α)
    (hC : C.card ≤ k) (τ : List α) : (phaseFuture k C τ).card ≤ k := by
  induction τ generalizing C with
  | nil => exact hC
  | cons z τ ih =>
    simp only [phaseFuture]
    split_ifs with h
    · apply ih
      rcases h with hz | hcard
      · simpa [Finset.insert_eq_of_mem hz] using hC
      · exact (Finset.card_insert_le _ _).trans (by omega)
    · exact hC

lemma phaseFuture_cons_of_mem {α : Type*} [DecidableEq α] (k : ℕ)
    (C : Finset α) (z : α) (τ : List α) (hz : z ∈ C) :
    phaseFuture k C (z :: τ) = phaseFuture k C τ := by
  simp [phaseFuture, hz, Finset.insert_eq_of_mem hz]

lemma phaseFuture_cons_of_card_lt {α : Type*} [DecidableEq α] (k : ℕ)
    (C : Finset α) (z : α) (τ : List α) (hC : C.card < k) :
    phaseFuture k C (z :: τ) = phaseFuture k (insert z C) τ := by
  simp [phaseFuture, hC]

lemma mem_phaseFuture_cons {α : Type*} [DecidableEq α] (k : ℕ)
    (C : Finset α) (z : α) (τ : List α) (h : z ∈ C ∨ C.card < k) :
    z ∈ phaseFuture k C (z :: τ) := by
  simp only [phaseFuture, if_pos h]
  exact subset_phaseFuture k _ _ (Finset.mem_insert_self _ _)

lemma cleanCountAux_step {α : Type*} [DecidableEq α] (k : ℕ)
    (s : PhaseState α) (z : α) (τ : List α) :
    cleanCountAux k s.previous s.current (z :: τ) = phaseCharge k s z +
      cleanCountAux k (phaseStep k s z).previous (phaseStep k s z).current τ := by
  simp only [cleanCountAux, phaseCharge, phaseStep]
  split_ifs <;> simp

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

def nativePhase (s : PMState α) : PhaseState α := ⟨s.stale, s.marked, s.phase⟩

def loadedPhase (s : PMState α) (z : α) : PhaseState α :=
  ⟨s.stale, insert z s.marked, s.phase⟩

omit [DecidableEq α] in
theorem marked_eq_cache_of_full {k : ℕ} {s : PMState α}
    (hs : CacheInvariant k s) (hm : s.marked.card = k) : s.marked = s.cache :=
  Finset.eq_of_subset_of_card_le hs.marked_subset (by have := hs.card_le; omega)

theorem loadedPhase_of_hitOrFill {k : ℕ} {s : PMState α} (hs : CacheInvariant k s)
    {z : α} (h : z ∈ s.cache ∨ s.cache.card < k) :
    loadedPhase s z = phaseStep k (nativePhase s) z := by
  by_cases hz : z ∈ s.marked
  · simp [loadedPhase, phaseStep, nativePhase, hz, Finset.insert_eq_of_mem hz]
  · have hcard : s.marked.card < k := by
      have hle := (Finset.card_le_card hs.marked_subset).trans hs.card_le
      have hne : s.marked.card ≠ k := by
        intro heq
        have he := marked_eq_cache_of_full hs heq
        rcases h with h | h
        · exact hz (he.symm ▸ h)
        · have := Finset.card_le_card hs.marked_subset
          omega
      omega
    simp [loadedPhase, phaseStep, nativePhase, hz, hcard]

theorem loadedPhase_of_miss {k : ℕ} {s : PMState α} (hs : CacheInvariant k s)
    {z : α} (hz : z ∉ s.cache) :
    loadedPhase (phaseStart k s) z = phaseStep k (nativePhase s) z := by
  have hzm : z ∉ s.marked := fun h => hz (hs.marked_subset h)
  by_cases hm : s.marked.card = k
  · have he := marked_eq_cache_of_full hs hm
    simp only [loadedPhase, phaseStart, phaseStep, nativePhase, hm, if_pos, hzm, if_false, lt_self_iff_false, Finset.insert_empty]
    rw [he]
  · have hlt : s.marked.card < k := by
      have := (Finset.card_le_card hs.marked_subset).trans hs.card_le
      omega
    simp [loadedPhase, phaseStart, phaseStep, nativePhase, hm, hzm, hlt]

theorem miss_nativePhase {k : ℕ} (u : PMState α) (z : α) (tb : PMState α → α)
    (hne : (u.cache \ u.marked).Nonempty) {v : PMState α}
    (hv : v ∈ (if z ∉ u.stale then
      PMF.pure (evictInto (cleanState u) z (u.clean + 1) (tb (cleanState u)))
      else if (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ) then
        PMF.pure (evictInto (staleState u z) z (u.chainOf z) (tb (staleState u z)))
      else randomEviction (staleState u z) z (u.chainOf z)).support) :
    nativePhase v = loadedPhase u z := by
  by_cases hc : z ∉ u.stale
  · rw [if_pos hc] at hv
    have he := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    rfl
  · rw [if_neg hc] at hv
    by_cases hr : (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ)
    · rw [if_pos hr] at hv
      have he := (PMF.mem_support_pure_iff _ _).mp hv
      subst v
      rfl
    · rw [if_neg hr] at hv
      obtain ⟨e, he, rfl⟩ := randomEviction_support (s := staleState u z) hne hv
      rfl

theorem step_nativePhase {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    {s : PMState α} (hs : CacheInvariant k s) (i : ℕ) (z : α) (hz : ℝ)
    {v : PMState α} (hv : v ∈ (step k tb s i z hz).support) :
    nativePhase v = phaseStep k (nativePhase s) z := by
  rw [step_factored] at hv
  dsimp only at hv
  let t := savePrediction s i z hz
  have ht : CacheInvariant k t := save_cacheInvariant hs i z hz
  by_cases hh : z ∈ t.cache ∨ t.cache.card < k
  · simp only [show z ∈ (savePrediction s i z hz).cache ∨
      (savePrediction s i z hz).cache.card < k from hh, if_pos] at hv
    have he := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    exact loadedPhase_of_hitOrFill ht hh
  · simp only [show ¬ (z ∈ (savePrediction s i z hz).cache ∨
      (savePrediction s i z hz).cache.card < k) from hh, if_false] at hv
    have hf : t.cache.card = k := by have := ht.card_le; simp only [not_or] at hh; omega
    exact (miss_nativePhase (phaseStart k t) z tb
      (phaseStart_candidates_nonempty hk ht hf) hv).trans
      (loadedPhase_of_miss ht (not_or.mp hh).1)

theorem run_cacheInvariant {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {s : PMState α} (hs : s ∈ (run k tb σ h).support) : CacheInvariant k s := by
  unfold run at hs
  have hstep : ∀ t : PMState α, CacheInvariant k t → ∀ i : Fin σ.length,
      ∀ v ∈ (step k tb t i.val (σ.get i) (h i)).support, CacheInvariant k v := by
    intro t ht i v hv
    exact step_cacheInvariant hk tb htb ht i.val (σ.get i) (h i) hv
  have hinit : ∀ t ∈ (PMF.pure (initState α)).support, CacheInvariant k t := by
    intro t ht
    have he := (PMF.mem_support_pure_iff _ _).mp ht
    subst t
    exact init_cacheInvariant k
  exact fold_support_invariant (fun (t : PMState α) (i : Fin σ.length) => step k tb t i.val (σ.get i) (h i))
    (CacheInvariant k) hstep (List.finRange σ.length) (PMF.pure (initState α)) hinit s hs

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

structure PhaseCacheInvariant (k : ℕ) (s : PMState α) : Prop where
  unmarked_stale : s.cache \ s.marked ⊆ s.stale
  stale_full : s.stale.Nonempty → s.cache.card = k

theorem init_phaseCacheInvariant (k : ℕ) : PhaseCacheInvariant k (initState α) := by
  constructor <;> simp [initState]

theorem hitOrFill_phaseCacheInvariant {k : ℕ} {s : PMState α}
    (hs : PhaseCacheInvariant k s) (z : α) (h : z ∈ s.cache ∨ s.cache.card < k) :
    PhaseCacheInvariant k (hitOrFill s z) := by
  constructor
  · intro x hx
    obtain ⟨hx, hm⟩ := Finset.mem_sdiff.mp hx
    have hxz : x ≠ z := by intro he; subst x; exact hm (Finset.mem_insert_self _ _)
    have hxc : x ∈ s.cache := (Finset.mem_insert.mp hx).resolve_left hxz
    exact hs.unmarked_stale (Finset.mem_sdiff.mpr ⟨hxc, fun hxm => hm (Finset.mem_insert_of_mem hxm)⟩)
  · intro hne
    have hf := hs.stale_full hne
    rcases h with h | h
    · simpa only [hitOrFill, Finset.insert_eq_of_mem h] using hf
    · omega

theorem phaseStart_phaseCacheInvariant {k : ℕ} {s : PMState α}
    (hc : CacheInvariant k s) (hs : PhaseCacheInvariant k s) :
    PhaseCacheInvariant k (phaseStart k s) := by
  unfold phaseStart
  split_ifs with hm
  · constructor
    · simp
    · intro _
      have := Finset.card_le_card hc.marked_subset
      have := hc.card_le
      change s.cache.card = k
      omega
  · exact hs

theorem evictInto_phaseCacheInvariant {k : ℕ} {s : PMState α}
    (hs : PhaseCacheInvariant k s) (hf : s.cache.card = k)
    {z : α} (hz : z ∉ s.cache) (c : ℕ) {e : α} (he : e ∈ s.cache \ s.marked) :
    PhaseCacheInvariant k (evictInto s z c e) := by
  constructor
  · intro x hx
    obtain ⟨hx, hm⟩ := Finset.mem_sdiff.mp hx
    have hxz : x ≠ z := by intro heq; subst x; exact hm (Finset.mem_insert_self _ _)
    have hxc : x ∈ s.cache := Finset.mem_of_mem_erase ((Finset.mem_insert.mp hx).resolve_left hxz)
    exact hs.unmarked_stale (Finset.mem_sdiff.mpr ⟨hxc, fun hxm => hm (Finset.mem_insert_of_mem hxm)⟩)
  · intro _
    change (insert z (s.cache.erase e)).card = k
    rw [Finset.card_insert_of_notMem (fun h => hz (Finset.mem_of_mem_erase h)),
      Finset.card_erase_add_one (Finset.mem_sdiff.mp he).1, hf]

theorem miss_phaseCacheInvariant {k : ℕ} (u : PMState α) (z : α) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (hu : PhaseCacheInvariant k u)
    (hf : u.cache.card = k) (hz : z ∉ u.cache)
    (hne : (u.cache \ u.marked).Nonempty) {v : PMState α}
    (hv : v ∈ (if z ∉ u.stale then
      PMF.pure (evictInto (cleanState u) z (u.clean + 1) (tb (cleanState u)))
      else if (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ) then
        PMF.pure (evictInto (staleState u z) z (u.chainOf z) (tb (staleState u z)))
      else randomEviction (staleState u z) z (u.chainOf z)).support) :
    PhaseCacheInvariant k v := by
  by_cases hc : z ∉ u.stale
  · rw [if_pos hc] at hv
    have he := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    exact evictInto_phaseCacheInvariant (s := cleanState u) ⟨hu.unmarked_stale, hu.stale_full⟩ hf hz _
      (htb (cleanState u) hne).1
  · rw [if_neg hc] at hv
    by_cases hr : (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ)
    · rw [if_pos hr] at hv
      have he := (PMF.mem_support_pure_iff _ _).mp hv
      subst v
      exact evictInto_phaseCacheInvariant (s := staleState u z) ⟨hu.unmarked_stale, hu.stale_full⟩ hf hz _
        (htb (staleState u z) hne).1
    · rw [if_neg hr] at hv
      obtain ⟨e, he, rfl⟩ := randomEviction_support (s := staleState u z) hne hv
      exact evictInto_phaseCacheInvariant
        (s := { staleState u z with randomChains := insert ((staleState u z).phase, u.chainOf z) (staleState u z).randomChains })
        ⟨hu.unmarked_stale, hu.stale_full⟩ hf hz _ he

theorem step_phaseCacheInvariant {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) {s : PMState α} (hs : CacheInvariant k s)
    (hp : PhaseCacheInvariant k s) (i : ℕ) (z : α) (hz : ℝ) {v : PMState α}
    (hv : v ∈ (step k tb s i z hz).support) : PhaseCacheInvariant k v := by
  rw [step_factored] at hv
  dsimp only at hv
  let t := savePrediction s i z hz
  have ht : CacheInvariant k t := save_cacheInvariant hs i z hz
  have hpt : PhaseCacheInvariant k t := ⟨hp.unmarked_stale, hp.stale_full⟩
  by_cases hh : z ∈ t.cache ∨ t.cache.card < k
  · simp only [show z ∈ (savePrediction s i z hz).cache ∨
      (savePrediction s i z hz).cache.card < k from hh, if_pos] at hv
    have he := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    exact hitOrFill_phaseCacheInvariant hpt z hh
  · simp only [show ¬ (z ∈ (savePrediction s i z hz).cache ∨
      (savePrediction s i z hz).cache.card < k) from hh, if_false] at hv
    have hf : t.cache.card = k := by have := ht.card_le; simp only [not_or] at hh; omega
    exact miss_phaseCacheInvariant (phaseStart k t) z tb htb (phaseStart_phaseCacheInvariant ht hpt)
      (by rw [phaseStart_cache]; exact hf) (by rw [phaseStart_cache]; exact (not_or.mp hh).1)
      (phaseStart_candidates_nonempty hk ht hf) hv

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

structure RepresentativeBijection {α : Type*} (D : Finset α) (f : α → ℕ) (c : ℕ) : Prop where
  bounds : ∀ x ∈ D, 1 ≤ f x ∧ f x ≤ c
  injective : Set.InjOn f (↑D : Set α)
  surjective : ∀ i, 1 ≤ i → i ≤ c → ∃ x ∈ D, f x = i

lemma RepresentativeBijection.empty {α : Type*} (f : α → ℕ) :
    RepresentativeBijection (∅ : Finset α) f 0 := by
  constructor
  · simp
  · intro x hx; simp at hx
  · intro i hi hic; omega

lemma RepresentativeBijection.add_fresh {α : Type*} [DecidableEq α]
    {D : Finset α} {f : α → ℕ} {c : ℕ} (h : RepresentativeBijection D f c)
    (e : α) (he : e ∉ D) :
    RepresentativeBijection (insert e D) (Function.update f e (c + 1)) (c + 1) := by
  constructor
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simp
    · have hxe : x ≠ e := ne_of_mem_of_not_mem hx he
      simp only [Function.update_of_ne hxe]
      have hb := h.bounds x hx
      omega
  · intro x hx y hy hxy
    by_cases hxe : x = e
    · subst x
      by_cases hye : y = e
      · exact hye.symm
      · have hyD : y ∈ D := (Finset.mem_insert.mp hy).resolve_left hye
        have hb := (h.bounds y hyD).2
        simp only [Function.update_self, Function.update_of_ne hye] at hxy
        omega
    · by_cases hye : y = e
      · subst y
        have hxD : x ∈ D := (Finset.mem_insert.mp hx).resolve_left hxe
        have hb := (h.bounds x hxD).2
        simp only [Function.update_self, Function.update_of_ne hxe] at hxy
        omega
      · apply h.injective ((Finset.mem_insert.mp hx).resolve_left hxe)
          ((Finset.mem_insert.mp hy).resolve_left hye)
        simpa [Function.update_of_ne hxe, Function.update_of_ne hye] using hxy
  · intro i hi hic
    by_cases hie : i = c + 1
    · exact ⟨e, Finset.mem_insert_self _ _, by simpa using hie.symm⟩
    · obtain ⟨x, hx, hfx⟩ := h.surjective i hi (by omega)
      exact ⟨x, Finset.mem_insert_of_mem hx, by
        simpa [Function.update_of_ne (ne_of_mem_of_not_mem hx he)] using hfx⟩

lemma RepresentativeBijection.replace {α : Type*} [DecidableEq α]
    {D : Finset α} {f : α → ℕ} {c : ℕ} (h : RepresentativeBijection D f c)
    (z e : α) (hz : z ∈ D) (he : e ∉ D) :
    RepresentativeBijection (insert e (D.erase z)) (Function.update f e (f z)) c := by
  constructor
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simpa using h.bounds z hz
    · have hxD := Finset.mem_of_mem_erase hx
      simpa [Function.update_of_ne (ne_of_mem_of_not_mem hxD he)] using h.bounds x hxD
  · intro x hx y hy hxy
    by_cases hxe : x = e
    · subst x
      by_cases hye : y = e
      · exact hye.symm
      · have hyE : y ∈ D.erase z := (Finset.mem_insert.mp hy).resolve_left hye
        have hyD := Finset.mem_of_mem_erase hyE
        have hzy : f z = f y := by simpa [Function.update_of_ne hye] using hxy
        have heq := h.injective hz hyD hzy
        exact False.elim ((Finset.mem_erase.mp hyE).1 heq.symm)
    · by_cases hye : y = e
      · subst y
        have hxE : x ∈ D.erase z := (Finset.mem_insert.mp hx).resolve_left hxe
        have hxD := Finset.mem_of_mem_erase hxE
        have hxz : f x = f z := by simpa [Function.update_of_ne hxe] using hxy
        have heq := h.injective hxD hz hxz
        exact False.elim ((Finset.mem_erase.mp hxE).1 heq)
      · apply h.injective
          (Finset.mem_of_mem_erase ((Finset.mem_insert.mp hx).resolve_left hxe))
          (Finset.mem_of_mem_erase ((Finset.mem_insert.mp hy).resolve_left hye))
        simpa [Function.update_of_ne hxe, Function.update_of_ne hye] using hxy
  · intro i hi hic
    obtain ⟨x, hx, hfx⟩ := h.surjective i hi hic
    by_cases hxz : x = z
    · subst x
      exact ⟨e, Finset.mem_insert_self _ _, by simpa using hfx⟩
    · exact ⟨x, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxz, hx⟩), by
        simpa [Function.update_of_ne (ne_of_mem_of_not_mem hx he)] using hfx⟩

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

def NativeRepresentatives (s : PMState α) : Prop :=
  RepresentativeBijection (s.stale \ s.cache) s.chainOf s.clean

theorem missing_clean_update (S C : Finset α) {z e : α}
    (hz : z ∉ S) (heS : e ∈ S) (heC : e ∈ C) :
    S \ insert z (C.erase e) = insert e (S \ C) := by
  ext x
  by_cases hxe : x = e <;> by_cases hxz : x = z <;> simp_all

theorem missing_stale_update (S C : Finset α) {z e : α}
    (hzS : z ∈ S) (hzC : z ∉ C) (heS : e ∈ S) (heC : e ∈ C) :
    S \ insert z (C.erase e) = insert e ((S \ C).erase z) := by
  ext x
  by_cases hxe : x = e <;> by_cases hxz : x = z <;> simp_all

theorem init_nativeRepresentatives : NativeRepresentatives (initState α) := by
  simpa [NativeRepresentatives, initState] using
    (RepresentativeBijection.empty (fun _ : α => 0))

theorem phaseStart_nativeRepresentatives (k : ℕ) {s : PMState α}
    (hs : NativeRepresentatives s) : NativeRepresentatives (phaseStart k s) := by
  unfold phaseStart
  split_ifs
  · simpa [NativeRepresentatives] using RepresentativeBijection.empty s.chainOf
  · exact hs

theorem hitOrFill_nativeRepresentatives {k : ℕ} {s : PMState α}
    (hp : PhaseCacheInvariant k s) (hs : NativeRepresentatives s) (z : α)
    (h : z ∈ s.cache ∨ s.cache.card < k) : NativeRepresentatives (hitOrFill s z) := by
  rcases h with h | h
  · simpa only [NativeRepresentatives, hitOrFill, Finset.insert_eq_of_mem h] using hs
  · have he : s.stale = ∅ := by
      by_contra he
      have hf := hp.stale_full (Finset.nonempty_iff_ne_empty.mpr he)
      omega
    simpa only [NativeRepresentatives, hitOrFill, he, Finset.empty_sdiff] using hs

theorem clean_eviction_nativeRepresentatives {k : ℕ} {s : PMState α}
    (hp : PhaseCacheInvariant k s) (hs : NativeRepresentatives s)
    {z e : α} (hz : z ∉ s.stale) (he : e ∈ s.cache \ s.marked) :
    NativeRepresentatives (evictInto (cleanState s) z (s.clean + 1) e) := by
  have heS := hp.unmarked_stale he
  have heC := (Finset.mem_sdiff.mp he).1
  change RepresentativeBijection (s.stale \ insert z (s.cache.erase e))
    (Function.update s.chainOf e (s.clean + 1)) (s.clean + 1)
  rw [missing_clean_update s.stale s.cache hz heS heC]
  exact hs.add_fresh e (by intro h; exact (Finset.mem_sdiff.mp h).2 heC)

theorem stale_eviction_nativeRepresentatives {k : ℕ} {s : PMState α}
    (hp : PhaseCacheInvariant k s) (hs : NativeRepresentatives s)
    {z e : α} (hzS : z ∈ s.stale) (hzC : z ∉ s.cache) (he : e ∈ s.cache \ s.marked) :
    NativeRepresentatives (evictInto (staleState s z) z (s.chainOf z) e) := by
  have heS := hp.unmarked_stale he
  have heC := (Finset.mem_sdiff.mp he).1
  change RepresentativeBijection (s.stale \ insert z (s.cache.erase e))
    (Function.update s.chainOf e (s.chainOf z)) s.clean
  rw [missing_stale_update s.stale s.cache hzS hzC heS heC]
  exact hs.replace z e (Finset.mem_sdiff.mpr ⟨hzS, hzC⟩)
    (by intro h; exact (Finset.mem_sdiff.mp h).2 heC)

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

theorem miss_nativeRepresentatives {k : ℕ} (u : PMState α) (z : α) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (hp : PhaseCacheInvariant k u) (hu : NativeRepresentatives u)
    (hz : z ∉ u.cache) (hne : (u.cache \ u.marked).Nonempty) {v : PMState α}
    (hv : v ∈ (if z ∉ u.stale then
      PMF.pure (evictInto (cleanState u) z (u.clean + 1) (tb (cleanState u)))
      else if (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ) then
        PMF.pure (evictInto (staleState u z) z (u.chainOf z) (tb (staleState u z)))
      else randomEviction (staleState u z) z (u.chainOf z)).support) :
    NativeRepresentatives v := by
  by_cases hc : z ∉ u.stale
  · rw [if_pos hc] at hv
    have he := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    exact clean_eviction_nativeRepresentatives hp hu hc (htb (cleanState u) hne).1
  · rw [if_neg hc] at hv
    have hzS : z ∈ u.stale := not_not.mp hc
    by_cases hr : (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ)
    · rw [if_pos hr] at hv
      have he := (PMF.mem_support_pure_iff _ _).mp hv
      subst v
      exact stale_eviction_nativeRepresentatives hp hu hzS hz (htb (staleState u z) hne).1
    · rw [if_neg hr] at hv
      obtain ⟨e, he, rfl⟩ := randomEviction_support (s := staleState u z) hne hv
      exact stale_eviction_nativeRepresentatives hp hu hzS hz he

theorem step_nativeRepresentatives {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) {s : PMState α} (hs : CacheInvariant k s)
    (hp : PhaseCacheInvariant k s) (hr : NativeRepresentatives s)
    (i : ℕ) (z : α) (hz : ℝ) {v : PMState α}
    (hv : v ∈ (step k tb s i z hz).support) : NativeRepresentatives v := by
  rw [step_factored] at hv
  dsimp only at hv
  let t := savePrediction s i z hz
  have ht : CacheInvariant k t := save_cacheInvariant hs i z hz
  have hpt : PhaseCacheInvariant k t := ⟨hp.unmarked_stale, hp.stale_full⟩
  have hrt : NativeRepresentatives t := hr
  by_cases hh : z ∈ t.cache ∨ t.cache.card < k
  · simp only [show z ∈ (savePrediction s i z hz).cache ∨
      (savePrediction s i z hz).cache.card < k from hh, if_pos] at hv
    have he := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    exact hitOrFill_nativeRepresentatives hpt hrt z hh
  · simp only [show ¬ (z ∈ (savePrediction s i z hz).cache ∨
      (savePrediction s i z hz).cache.card < k) from hh, if_false] at hv
    have hf : t.cache.card = k := by have := ht.card_le; simp only [not_or] at hh; omega
    exact miss_nativeRepresentatives (phaseStart k t) z tb htb
      (phaseStart_phaseCacheInvariant ht hpt) (phaseStart_nativeRepresentatives k hrt)
      (by rw [phaseStart_cache]; exact (not_or.mp hh).1)
      (phaseStart_candidates_nonempty hk ht hf) hv

theorem run_phaseCache_representatives {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {s : PMState α} (hs : s ∈ (run k tb σ h).support) :
    CacheInvariant k s ∧ PhaseCacheInvariant k s ∧ NativeRepresentatives s := by
  let P := fun t : PMState α => CacheInvariant k t ∧ PhaseCacheInvariant k t ∧ NativeRepresentatives t
  have hstep : ∀ t : PMState α, P t → ∀ i : Fin σ.length,
      ∀ v ∈ (step k tb t i.val (σ.get i) (h i)).support, P v := by
    intro t ht i v hv
    exact ⟨step_cacheInvariant hk tb htb ht.1 i.val _ _ hv,
      step_phaseCacheInvariant hk tb htb ht.1 ht.2.1 i.val _ _ hv,
      step_nativeRepresentatives hk tb htb ht.1 ht.2.1 ht.2.2 i.val _ _ hv⟩
  have hinit : ∀ t ∈ (PMF.pure (initState α)).support, P t := by
    intro t ht
    have he := (PMF.mem_support_pure_iff _ _).mp ht
    subst t
    exact ⟨init_cacheInvariant k, init_phaseCacheInvariant k, init_nativeRepresentatives⟩
  unfold run at hs
  exact fold_support_invariant (fun (t : PMState α) (i : Fin σ.length) =>
      step k tb t i.val (σ.get i) (h i)) P hstep
    (List.finRange σ.length) (PMF.pure (initState α)) hinit s hs

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem phaseStart_readonly (k : ℕ) (s : PMState α) :
    (phaseStart k s).pred = s.pred ∧ (phaseStart k s).predIdx = s.predIdx ∧
    (phaseStart k s).misses = s.misses ∧ (phaseStart k s).cache = s.cache := by
  unfold phaseStart
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem evictInto_observations (s : PMState α) (z : α) (c : ℕ) (e : α) :
    (evictInto s z c e).pred = s.pred ∧ (evictInto s z c e).predIdx = s.predIdx ∧
    (evictInto s z c e).misses = s.misses + 1 ∧
    (evictInto s z c e).cache ⊆ insert z s.cache := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact Finset.insert_subset_insert z (Finset.erase_subset _ _)

theorem miss_observations {k : ℕ} (u : PMState α) (z : α) (tb : PMState α → α)
    (hne : (u.cache \ u.marked).Nonempty) {v : PMState α}
    (hv : v ∈ (if z ∉ u.stale then
      PMF.pure (evictInto (cleanState u) z (u.clean + 1) (tb (cleanState u)))
      else if (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ) then
        PMF.pure (evictInto (staleState u z) z (u.chainOf z) (tb (staleState u z)))
      else randomEviction (staleState u z) z (u.chainOf z)).support) :
    v.pred = u.pred ∧ v.predIdx = u.predIdx ∧ v.misses = u.misses + 1 ∧
    v.cache ⊆ insert z u.cache := by
  by_cases hc : z ∉ u.stale
  · rw [if_pos hc] at hv
    have he := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    exact evictInto_observations _ _ _ _
  · rw [if_neg hc] at hv
    by_cases hr : (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ)
    · rw [if_pos hr] at hv
      have he := (PMF.mem_support_pure_iff _ _).mp hv
      subst v
      exact evictInto_observations _ _ _ _
    · rw [if_neg hr] at hv
      obtain ⟨e, he, rfl⟩ := randomEviction_support (s := staleState u z) hne hv
      exact evictInto_observations _ _ _ _

theorem step_observations {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    {s : PMState α} (hs : CacheInvariant k s) (i : ℕ) (z : α) (hz : ℝ)
    {v : PMState α} (hv : v ∈ (step k tb s i z hz).support) :
    v.pred = Function.update s.pred z hz ∧ v.predIdx = Function.update s.predIdx z i ∧
    v.misses = s.misses + (if z ∈ s.cache then 0 else 1) ∧
    v.cache ⊆ insert z s.cache := by
  rw [step_factored] at hv
  dsimp only at hv
  let t := savePrediction s i z hz
  have ht : CacheInvariant k t := save_cacheInvariant hs i z hz
  by_cases hh : z ∈ t.cache ∨ t.cache.card < k
  · simp only [show z ∈ (savePrediction s i z hz).cache ∨
      (savePrediction s i z hz).cache.card < k from hh, if_pos] at hv
    have he := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    refine ⟨rfl, rfl, ?_, le_rfl⟩
    change (if z ∈ s.cache then s.misses else s.misses + 1) = _
    split_ifs <;> omega
  · simp only [show ¬ (z ∈ (savePrediction s i z hz).cache ∨
      (savePrediction s i z hz).cache.card < k) from hh, if_false] at hv
    have hf : t.cache.card = k := by have := ht.card_le; simp only [not_or] at hh; omega
    obtain ⟨hp, hi, hm, hc⟩ := miss_observations (phaseStart k t) z tb
      (phaseStart_candidates_nonempty hk ht hf) hv
    obtain ⟨hp0, hi0, hm0, hc0⟩ := phaseStart_readonly k t
    refine ⟨hp.trans hp0, hi.trans hi0, ?_, ?_⟩
    · rw [hm, hm0]
      exact congrArg (s.misses + ·) (if_neg (not_or.mp hh).1).symm
    · rw [hc0] at hc
      exact hc

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

def indexFamily (s : PMState α) (p : ℕ × ℕ) : List ℕ := s.chainIdx p.1 p.2

theorem evictInto_indexFamily (s : PMState α) (z : α) (c : ℕ) (e : α) :
    indexFamily (evictInto s z c e) = Function.update (indexFamily s) (s.phase, c)
      (indexFamily s (s.phase, c) ++ [s.predIdx e]) := by
  funext p
  rcases p with ⟨r, d⟩
  by_cases hr : r = s.phase <;> by_cases hd : d = c <;>
    simp [indexFamily, evictInto, hr, hd]

theorem miss_eviction_data {k : ℕ} (u : PMState α) (z : α) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (hne : (u.cache \ u.marked).Nonempty) {v : PMState α}
    (hv : v ∈ (if z ∉ u.stale then
      PMF.pure (evictInto (cleanState u) z (u.clean + 1) (tb (cleanState u)))
      else if (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ) then
        PMF.pure (evictInto (staleState u z) z (u.chainOf z) (tb (staleState u z)))
      else randomEviction (staleState u z) z (u.chainOf z)).support) :
    ∃ e ∈ u.cache \ u.marked, ∃ c : ℕ,
      v.cache = insert z (u.cache.erase e) ∧
      indexFamily v = Function.update (indexFamily u) (u.phase, c)
        (indexFamily u (u.phase, c) ++ [u.predIdx e]) := by
  by_cases hc : z ∉ u.stale
  · rw [if_pos hc] at hv
    have he := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    refine ⟨tb (cleanState u), (htb (cleanState u) hne).1, u.clean + 1, rfl, ?_⟩
    exact evictInto_indexFamily _ _ _ _
  · rw [if_neg hc] at hv
    by_cases hr : (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ)
    · rw [if_pos hr] at hv
      have he := (PMF.mem_support_pure_iff _ _).mp hv
      subst v
      refine ⟨tb (staleState u z), (htb (staleState u z) hne).1, u.chainOf z, rfl, ?_⟩
      exact evictInto_indexFamily _ _ _ _
    · rw [if_neg hr] at hv
      obtain ⟨e, he, rfl⟩ := randomEviction_support (s := staleState u z) hne hv
      exact ⟨e, he, u.chainOf z, rfl, evictInto_indexFamily _ _ _ _⟩

omit [DecidableEq α] in
theorem phaseStart_indexFamily (k : ℕ) (s : PMState α) :
    indexFamily (phaseStart k s) = indexFamily s := by
  unfold phaseStart
  split_ifs <;> rfl

theorem step_ledger_cases {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) {s : PMState α} (hs : CacheInvariant k s)
    (i : ℕ) (z : α) (hz : ℝ) {v : PMState α}
    (hv : v ∈ (step k tb s i z hz).support) :
    (indexFamily v = indexFamily s ∧ v.cache = insert z s.cache) ∨
    (z ∉ s.cache ∧ ∃ e ∈ s.cache, ∃ p : ℕ × ℕ,
      v.cache = insert z (s.cache.erase e) ∧
      indexFamily v = Function.update (indexFamily s) p (indexFamily s p ++ [s.predIdx e])) := by
  rw [step_factored] at hv
  dsimp only at hv
  let t := savePrediction s i z hz
  have ht : CacheInvariant k t := save_cacheInvariant hs i z hz
  by_cases hh : z ∈ t.cache ∨ t.cache.card < k
  · simp only [show z ∈ (savePrediction s i z hz).cache ∨
      (savePrediction s i z hz).cache.card < k from hh, if_pos] at hv
    have he := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    exact Or.inl ⟨rfl, rfl⟩
  · simp only [show ¬ (z ∈ (savePrediction s i z hz).cache ∨
      (savePrediction s i z hz).cache.card < k) from hh, if_false] at hv
    have hf : t.cache.card = k := by have := ht.card_le; simp only [not_or] at hh; omega
    obtain ⟨e, he, c, hc, hi⟩ := miss_eviction_data (phaseStart k t) z tb htb
      (phaseStart_candidates_nonempty hk ht hf) hv
    have hec : e ∈ s.cache := by
      have := (Finset.mem_sdiff.mp he).1
      rw [phaseStart_cache] at this
      exact this
    have hze : z ∉ s.cache := (not_or.mp hh).1
    have hez : e ≠ z := ne_of_mem_of_not_mem hec hze
    refine Or.inr ⟨hze, e, hec, ((phaseStart k t).phase, c), ?_, ?_⟩
    · rw [phaseStart_cache] at hc
      exact hc
    · rw [phaseStart_indexFamily] at hi
      have hidx := (phaseStart_readonly k t).2.1
      rw [hidx] at hi
      have hfam : indexFamily t = indexFamily s := rfl
      have hpred : t.predIdx e = s.predIdx e := by
        change Function.update s.predIdx z i e = s.predIdx e
        exact Function.update_of_ne hez i s.predIdx
      rw [hfam, hpred] at hi
      exact hi

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

def lengthFamily (s : PMState α) (p : ℕ × ℕ) : ℕ := s.chainLen p.1 p.2

structure ChainBookkeeping (s : PMState α) : Prop where
  lengths : ∀ p, lengthFamily s p = (indexFamily s p).length
  future_empty : ∀ r c, s.phase < r → indexFamily s (r, c) = []
  current_empty : ∀ c, s.clean < c ∨ c = 0 → indexFamily s (s.phase, c) = []

omit [DecidableEq α] in
theorem init_chainBookkeeping : ChainBookkeeping (initState α) := by
  constructor <;> intros <;> rfl

theorem clean_lengthFamily (s : PMState α) (z e : α) :
    lengthFamily (evictInto (cleanState s) z (s.clean + 1) e) =
      Function.update (lengthFamily s) (s.phase, s.clean + 1) 1 := by
  funext p
  rcases p with ⟨r, c⟩
  by_cases hr : r = s.phase <;> by_cases hc : c = s.clean + 1 <;>
    simp [lengthFamily, evictInto, cleanState, hr, hc]

theorem stale_lengthFamily (s : PMState α) (z e : α) :
    lengthFamily (evictInto (staleState s z) z (s.chainOf z) e) =
      Function.update (lengthFamily s) (s.phase, s.chainOf z)
        (lengthFamily s (s.phase, s.chainOf z) + 1) := by
  funext p
  rcases p with ⟨r, c⟩
  by_cases hr : r = s.phase <;> by_cases hc : c = s.chainOf z <;>
    simp [lengthFamily, evictInto, staleState, hr, hc]

theorem clean_eviction_chainBookkeeping {s : PMState α} (hs : ChainBookkeeping s) (z e : α) :
    ChainBookkeeping (evictInto (cleanState s) z (s.clean + 1) e) := by
  have hi := evictInto_indexFamily (cleanState s) z (s.clean + 1) e
  change indexFamily (evictInto (cleanState s) z (s.clean + 1) e) =
    Function.update (indexFamily s) (s.phase, s.clean + 1)
      (indexFamily s (s.phase, s.clean + 1) ++ [s.predIdx e]) at hi
  have hempty := hs.current_empty (s.clean + 1) (Or.inl (Nat.lt_succ_self _))
  constructor
  · intro p
    rw [clean_lengthFamily, hi]
    by_cases hp : p = (s.phase, s.clean + 1)
    · subst p
      simp [hempty]
    · rw [Function.update_of_ne hp, Function.update_of_ne hp]
      exact hs.lengths p
  · intro r c hr
    change s.phase < r at hr
    rw [hi, Function.update_of_ne (show (r, c) ≠ (s.phase, s.clean + 1) from by
      intro he; have := congrArg Prod.fst he; dsimp at this; omega)]
    exact hs.future_empty r c hr
  · intro c hc
    change s.clean + 1 < c ∨ c = 0 at hc
    change indexFamily (evictInto (cleanState s) z (s.clean + 1) e) (s.phase, c) = []
    have hne : (s.phase, c) ≠ (s.phase, s.clean + 1) := by
      intro he; have := congrArg Prod.snd he; dsimp at this; omega
    rw [hi, Function.update_of_ne hne]
    exact hs.current_empty c (by omega)

theorem stale_eviction_chainBookkeeping {s : PMState α} (hs : ChainBookkeeping s)
    (z e : α) (hc : 1 ≤ s.chainOf z ∧ s.chainOf z ≤ s.clean) :
    ChainBookkeeping (evictInto (staleState s z) z (s.chainOf z) e) := by
  have hi := evictInto_indexFamily (staleState s z) z (s.chainOf z) e
  change indexFamily (evictInto (staleState s z) z (s.chainOf z) e) =
    Function.update (indexFamily s) (s.phase, s.chainOf z)
      (indexFamily s (s.phase, s.chainOf z) ++ [s.predIdx e]) at hi
  constructor
  · intro p
    rw [stale_lengthFamily, hi]
    by_cases hp : p = (s.phase, s.chainOf z)
    · subst p
      simp [hs.lengths]
    · rw [Function.update_of_ne hp, Function.update_of_ne hp]
      exact hs.lengths p
  · intro r c hr
    change s.phase < r at hr
    rw [hi, Function.update_of_ne (show (r, c) ≠ (s.phase, s.chainOf z) from by
      intro he; have := congrArg Prod.fst he; dsimp at this; omega)]
    exact hs.future_empty r c hr
  · intro c hce
    change s.clean < c ∨ c = 0 at hce
    change indexFamily (evictInto (staleState s z) z (s.chainOf z) e) (s.phase, c) = []
    have hne : (s.phase, c) ≠ (s.phase, s.chainOf z) := by
      intro he; have := congrArg Prod.snd he; dsimp at this; omega
    rw [hi, Function.update_of_ne hne]
    exact hs.current_empty c hce

omit [DecidableEq α] in
theorem phaseStart_chainBookkeeping (k : ℕ) {s : PMState α} (hs : ChainBookkeeping s) :
    ChainBookkeeping (phaseStart k s) := by
  unfold phaseStart
  split_ifs
  · constructor
    · exact hs.lengths
    · intro r c hr
      exact hs.future_empty r c (by change s.phase + 1 < r at hr; omega)
    · intro c _
      exact hs.future_empty (s.phase + 1) c (Nat.lt_succ_self _)
  · exact hs

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

noncomputable def indexedStep (k : ℕ) (tb : PMState α → α) (σ : List α)
    (h : Fin σ.length → ℝ) (i : ℕ) (s : PMState α) : PMF (PMState α) :=
  if hi : i < σ.length then step k tb s i (σ.get ⟨i, hi⟩) (h ⟨i, hi⟩) else PMF.pure s

noncomputable def prefixRun (k : ℕ) (tb : PMState α → α) (σ : List α)
    (h : Fin σ.length → ℝ) : ℕ → PMF (PMState α)
  | 0 => PMF.pure (initState α)
  | n + 1 => (prefixRun k tb σ h n).bind (indexedStep k tb σ h n)

theorem prefixRun_succ {k : ℕ} (tb : PMState α → α) (σ : List α)
    (h : Fin σ.length → ℝ) {n : ℕ} (hn : n < σ.length) :
    prefixRun k tb σ h (n + 1) = (prefixRun k tb σ h n).bind
      (fun s => step k tb s n (σ.get ⟨n, hn⟩) (h ⟨n, hn⟩)) := by
  rw [prefixRun]
  congr 1
  funext s
  exact dif_pos hn

theorem prefixRun_fold (k : ℕ) (tb : PMState α → α) (σ : List α)
    (h : Fin σ.length → ℝ) (n : ℕ) :
    prefixRun k tb σ h n = (List.range n).foldl
      (fun p i => p.bind (indexedStep k tb σ h i)) (PMF.pure (initState α)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [prefixRun, List.range_succ, List.foldl_append, ih]

omit [DecidableEq α] in
theorem finRange_val (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intros
    simp

theorem run_eq_prefixRun (k : ℕ) (tb : PMState α → α) (σ : List α)
    (h : Fin σ.length → ℝ) : run k tb σ h = prefixRun k tb σ h σ.length := by
  rw [prefixRun_fold, ← finRange_val σ.length, List.foldl_map]
  unfold run
  congr 1
  funext p i
  congr 1
  funext s
  simp [indexedStep, i.isLt]

theorem prefixRun_cacheInvariant {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ) (n : ℕ)
    {s : PMState α} (hs : s ∈ (prefixRun k tb σ h n).support) : CacheInvariant k s := by
  induction n generalizing s with
  | zero =>
    have he := (PMF.mem_support_pure_iff _ _).mp hs
    subst s
    exact init_cacheInvariant k
  | succ n ih =>
    obtain ⟨t, ht, hs⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
    unfold indexedStep at hs
    split_ifs at hs with hn
    · exact step_cacheInvariant hk tb htb (ih ht) n _ _ hs
    · have he := (PMF.mem_support_pure_iff _ _).mp hs
      subst s
      exact ih ht

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

structure OperationalInvariant (k : ℕ) (s : PMState α) : Prop where
  cache : CacheInvariant k s
  phaseCache : PhaseCacheInvariant k s
  representatives : NativeRepresentatives s
  bookkeeping : ChainBookkeeping s

theorem miss_chainBookkeeping {k : ℕ} (u : PMState α) (z : α) (tb : PMState α → α)
    (hrp : NativeRepresentatives u) (hu : ChainBookkeeping u)
    (hz : z ∉ u.cache) (hne : (u.cache \ u.marked).Nonempty) {v : PMState α}
    (hv : v ∈ (if z ∉ u.stale then
      PMF.pure (evictInto (cleanState u) z (u.clean + 1) (tb (cleanState u)))
      else if (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ) then
        PMF.pure (evictInto (staleState u z) z (u.chainOf z) (tb (staleState u z)))
      else randomEviction (staleState u z) z (u.chainOf z)).support) :
    ChainBookkeeping v := by
  by_cases hc : z ∉ u.stale
  · rw [if_pos hc] at hv
    have he := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    exact clean_eviction_chainBookkeeping hu z _
  · rw [if_neg hc] at hv
    have hzc := hrp.bounds z (Finset.mem_sdiff.mpr ⟨not_not.mp hc, hz⟩)
    by_cases hr : (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ)
    · rw [if_pos hr] at hv
      have he := (PMF.mem_support_pure_iff _ _).mp hv
      subst v
      exact stale_eviction_chainBookkeeping hu z _ hzc
    · rw [if_neg hr] at hv
      obtain ⟨e, he, rfl⟩ := randomEviction_support (s := staleState u z) hne hv
      have hb := stale_eviction_chainBookkeeping hu z e hzc
      exact ⟨hb.lengths, hb.future_empty, hb.current_empty⟩

theorem step_chainBookkeeping {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    {s : PMState α} (hs : CacheInvariant k s) (hr : NativeRepresentatives s)
    (hb : ChainBookkeeping s) (i : ℕ) (z : α) (hz : ℝ) {v : PMState α}
    (hv : v ∈ (step k tb s i z hz).support) : ChainBookkeeping v := by
  rw [step_factored] at hv
  dsimp only at hv
  let t := savePrediction s i z hz
  have ht : CacheInvariant k t := save_cacheInvariant hs i z hz
  have hrt : NativeRepresentatives t := hr
  have hbt : ChainBookkeeping t := ⟨hb.lengths, hb.future_empty, hb.current_empty⟩
  by_cases hh : z ∈ t.cache ∨ t.cache.card < k
  · simp only [show z ∈ (savePrediction s i z hz).cache ∨
      (savePrediction s i z hz).cache.card < k from hh, if_pos] at hv
    have he := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    exact ⟨hb.lengths, hb.future_empty, hb.current_empty⟩
  · simp only [show ¬ (z ∈ (savePrediction s i z hz).cache ∨
      (savePrediction s i z hz).cache.card < k) from hh, if_false] at hv
    have hf : t.cache.card = k := by have := ht.card_le; simp only [not_or] at hh; omega
    exact miss_chainBookkeeping (phaseStart k t) z tb
      (phaseStart_nativeRepresentatives k hrt) (phaseStart_chainBookkeeping k hbt)
      (by rw [phaseStart_cache]; exact (not_or.mp hh).1)
      (phaseStart_candidates_nonempty hk ht hf) hv

theorem init_operationalInvariant (k : ℕ) : OperationalInvariant k (initState α) :=
  ⟨init_cacheInvariant k, init_phaseCacheInvariant k, init_nativeRepresentatives, init_chainBookkeeping⟩

theorem step_operationalInvariant {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) {s : PMState α} (hs : OperationalInvariant k s)
    (i : ℕ) (z : α) (hz : ℝ) {v : PMState α}
    (hv : v ∈ (step k tb s i z hz).support) : OperationalInvariant k v :=
  ⟨step_cacheInvariant hk tb htb hs.cache i z hz hv,
    step_phaseCacheInvariant hk tb htb hs.cache hs.phaseCache i z hz hv,
    step_nativeRepresentatives hk tb htb hs.cache hs.phaseCache hs.representatives i z hz hv,
    step_chainBookkeeping hk tb hs.cache hs.representatives hs.bookkeeping i z hz hv⟩

theorem prefixRun_operationalInvariant {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ) (n : ℕ)
    {s : PMState α} (hs : s ∈ (prefixRun k tb σ h n).support) : OperationalInvariant k s := by
  induction n generalizing s with
  | zero =>
    have he := (PMF.mem_support_pure_iff _ _).mp hs
    subst s
    exact init_operationalInvariant k
  | succ n ih =>
    obtain ⟨t, ht, hs⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
    unfold indexedStep at hs
    split_ifs at hs with hn
    · exact step_operationalInvariant hk tb htb (ih ht) n _ _ hs
    · have he := (PMF.mem_support_pure_iff _ _).mp hs
      subst s
      exact ih ht

theorem run_operationalInvariant {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {s : PMState α} (hs : s ∈ (run k tb σ h).support) : OperationalInvariant k s := by
  rw [run_eq_prefixRun] at hs
  exact prefixRun_operationalInvariant hk tb htb σ h σ.length hs

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh
variable {α : Type*} [DecidableEq α]

lemma phaseStep_same_phase (k : ℕ) (s : PhaseState α) (z : α)
    (hp : (phaseStep k s z).number = s.number) :
    (phaseStep k s z).previous = s.previous ∧
    s.current ⊆ (phaseStep k s z).current ∧ z ∈ (phaseStep k s z).current := by
  unfold phaseStep at hp ⊢
  split_ifs with hz hm
  · exact ⟨rfl, le_rfl, hz⟩
  · exact ⟨rfl, Finset.subset_insert _ _, Finset.mem_insert_self _ _⟩
  · rw [if_neg hz, if_neg hm] at hp
    change s.number + 1 = s.number at hp
    omega

lemma step_same_phase_fields {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    {s : PMState α} (hs : CacheInvariant k s) (i : ℕ) (z : α) (hz : ℝ)
    {v : PMState α} (hv : v ∈ (step k tb s i z hz).support)
    (hp : v.phase = s.phase) :
    v.stale = s.stale ∧ s.marked ⊆ v.marked ∧ z ∈ v.marked := by
  have hπ := step_nativePhase hk tb hs i z hz hv
  have hn := congrArg PhaseState.number hπ
  change v.phase = (phaseStep k (nativePhase s) z).number at hn
  have hh := phaseStep_same_phase k (nativePhase s) z (hn.symm.trans hp)
  have hprev := congrArg PhaseState.previous hπ
  have hcur := congrArg PhaseState.current hπ
  change v.stale = _ at hprev
  change v.marked = _ at hcur
  exact ⟨hprev.trans hh.1, by rw [hcur]; exact hh.2.1, by rw [hcur]; exact hh.2.2⟩

lemma step_unmarked_subset {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    {s : PMState α} (hs : CacheInvariant k s) (i : ℕ) (z : α) (hz : ℝ)
    {v : PMState α} (hv : v ∈ (step k tb s i z hz).support)
    (hp : v.phase = s.phase) : v.cache \ v.marked ⊆ s.cache \ s.marked := by
  have hcache := (step_observations hk tb hs i z hz hv).2.2.2
  have hm := step_same_phase_fields hk tb hs i z hz hv hp
  intro x hx
  obtain ⟨hxC, hxM⟩ := Finset.mem_sdiff.mp hx
  have hxz : x ≠ z := by intro he; subst x; exact hxM hm.2.2
  exact Finset.mem_sdiff.mpr ⟨(Finset.mem_insert.mp (hcache hxC)).resolve_left hxz,
    fun hx => hxM (hm.2.1 hx)⟩

lemma step_missing_other {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    {s : PMState α} (hs : CacheInvariant k s) (i : ℕ) (z : α) (hz : ℝ)
    {v : PMState α} (hv : v ∈ (step k tb s i z hz).support)
    (hp : v.phase = s.phase) {x : α} (hx : x ∈ s.stale \ s.cache) (hxz : x ≠ z) :
    x ∈ v.stale \ v.cache := by
  have hcache := (step_observations hk tb hs i z hz hv).2.2.2
  have hm := step_same_phase_fields hk tb hs i z hz hv hp
  refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
  · rw [hm.1]; exact (Finset.mem_sdiff.mp hx).1
  · intro hxc
    exact (Finset.mem_sdiff.mp hx).2 ((Finset.mem_insert.mp (hcache hxc)).resolve_left hxz)
end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh
variable {α : Type*} [DecidableEq α]

lemma phaseFuture_step_same (k : ℕ) (s : PhaseState α) (z : α) (τ : List α)
    (hp : (phaseStep k s z).number = s.number) :
    phaseFuture k (phaseStep k s z).current τ = phaseFuture k s.current (z :: τ) := by
  by_cases hz : z ∈ s.current
  · simp [phaseStep, hz, phaseFuture, Finset.insert_eq_of_mem hz]
  · by_cases hm : s.current.card < k
    · simp [phaseStep, hz, hm, phaseFuture]
    · simp [phaseStep, hz, hm] at hp

lemma step_phaseFuture_same {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    {s : PMState α} (hs : CacheInvariant k s) (i : ℕ) (z : α) (hz : ℝ)
    {v : PMState α} (hv : v ∈ (step k tb s i z hz).support)
    (hp : v.phase = s.phase) (τ : List α) :
    phaseFuture k v.marked τ = phaseFuture k s.marked (z :: τ) := by
  have hπ := step_nativePhase hk tb hs i z hz hv
  have hn := congrArg PhaseState.number hπ
  have hm := congrArg PhaseState.current hπ
  change v.phase = (phaseStep k (nativePhase s) z).number at hn
  change v.marked = (phaseStep k (nativePhase s) z).current at hm
  rw [hm]
  exact phaseFuture_step_same k (nativePhase s) z τ (hn.symm.trans hp)

lemma finite_future_sink (C M F : Finset α) {k : ℕ}
    (hC : C.card = k) (hF : F.card ≤ k) (hMF : M ⊆ F)
    {z : α} (hzF : z ∈ F) (hzC : z ∉ C) :
    ∃ e ∈ C \ M, e ∉ F := by
  have hnot : ¬ C ⊆ F := by
    intro hCF
    have hi : insert z C ⊆ F := Finset.insert_subset hzF hCF
    have hcard := Finset.card_le_card hi
    rw [Finset.card_insert_of_notMem hzC, hC] at hcard
    omega
  obtain ⟨e, heC, heF⟩ := Finset.not_subset.mp hnot
  exact ⟨e, Finset.mem_sdiff.mpr ⟨heC, fun heM => heF (hMF heM)⟩, heF⟩

lemma finite_future_candidates_card (C M F : Finset α) {k : ℕ}
    (hC : C.card = k) (hF : F.card ≤ k) (hMF : M ⊆ F)
    {z : α} (hzF : z ∈ F) (hzC : z ∉ C) :
    ((C \ M) ∩ F).card + 1 ≤ (C \ M).card := by
  obtain ⟨e, heU, heF⟩ := finite_future_sink C M F hC hF hMF hzF hzC
  have hstrict : (C \ M) ∩ F ⊂ C \ M := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.inter_subset_left, ?_⟩
    intro heq
    have heA : e ∈ (C \ M) ∩ F := heq.symm ▸ heU
    exact heF (Finset.mem_inter.mp heA).2
  exact Finset.card_lt_card hstrict
end CachingML.PredMarker.PMFresh
end


section

open scoped BigOperators

namespace CachingML.PredMarker.PMFresh

lemma harmonic_real_succ (n : ℕ) :
    (harmonic (n + 1) : ℝ) = (harmonic n : ℝ) + 1 / ((n : ℝ) + 1) := by
  simp [harmonic_succ, Nat.cast_add, Nat.cast_one, one_div]

lemma harmonic_real_nonneg (n : ℕ) : 0 ≤ (harmonic n : ℝ) := by
  cases n with
  | zero => simp
  | succ n => exact le_of_lt (by exact_mod_cast harmonic_pos (Nat.succ_ne_zero n))

lemma harmonic_real_monotone : Monotone (fun n : ℕ => (harmonic n : ℝ)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [harmonic_real_succ]
  have h : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
  linarith

lemma harmonic_real_one_le {k : ℕ} (hk : 1 ≤ k) : 1 ≤ (harmonic k : ℝ) := by
  simpa [harmonic_succ, harmonic_zero] using harmonic_real_monotone hk

lemma sum_harmonic_successors (a : ℕ) :
    (∑ j ∈ Finset.range a, (harmonic (j + 1) : ℝ)) =
      ((a : ℝ) + 1) * (harmonic a : ℝ) - a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_range_succ, ih, harmonic_real_succ]
    push_cast
    have ha : (a : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

lemma harmonic_suffix_recursion (a b : ℕ) (hb : 1 ≤ b) :
    1 + (∑ j ∈ Finset.range a, (harmonic (j + 1) : ℝ)) / ((a : ℝ) + b) ≤
      (harmonic (a + 1) : ℝ) := by
  have hsum : 0 ≤ ∑ j ∈ Finset.range a, (harmonic (j + 1) : ℝ) :=
    Finset.sum_nonneg (fun j _ => harmonic_real_nonneg _)
  have ha : (0 : ℝ) < a + 1 := by positivity
  have hab : (a : ℝ) + 1 ≤ a + b := by exact_mod_cast Nat.add_le_add_left hb a
  have hdiv := div_le_div_of_nonneg_left hsum ha hab
  calc
    1 + (∑ j ∈ Finset.range a, (harmonic (j + 1) : ℝ)) / ((a : ℝ) + b)
        ≤ 1 + (∑ j ∈ Finset.range a, (harmonic (j + 1) : ℝ)) / ((a : ℝ) + 1) := add_le_add le_rfl hdiv
    _ = (harmonic (a + 1) : ℝ) := by
      rw [sum_harmonic_successors, harmonic_real_succ]
      field_simp
      ring

lemma harmonic_suffix_recursion_le_cache (a b k : ℕ) (hb : 1 ≤ b) (hak : a + 1 ≤ k) :
    1 + (∑ j ∈ Finset.range a, (harmonic (j + 1) : ℝ)) / ((a : ℝ) + b) ≤
      (harmonic k : ℝ) :=
  (harmonic_suffix_recursion a b hb).trans (harmonic_real_monotone hak)

lemma harmonic_rank_sum (a : ℕ) :
    (∑ j ∈ Finset.range a, (harmonic (a - j) : ℝ)) =
      ∑ j ∈ Finset.range a, (harmonic (j + 1) : ℝ) := by
  have h := Finset.sum_range_reflect (fun j => (harmonic (j + 1) : ℝ)) a
  convert h using 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 2
  have := Finset.mem_range.mp hj
  omega

end CachingML.PredMarker.PMFresh
end


section

open scoped BigOperators ENNReal

namespace CachingML.PredMarker.PMFresh

lemma pmExpectation_uniform {α : Type*} (s : Finset α) (hs : s.Nonempty)
    (f : α → ℝ≥0∞) : pmExpectation (PMF.uniformOfFinset s hs) f =
      (s.card : ℝ≥0∞)⁻¹ * ∑ a ∈ s, f a := by
  classical
  unfold pmExpectation
  rw [tsum_eq_sum (s := s)]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [PMF.uniformOfFinset_apply_of_mem hs ha]
  · intro a ha
    rw [PMF.uniformOfFinset_apply_of_notMem hs ha, zero_mul]

lemma pmExpectation_uniform_ofReal {α : Type*} (s : Finset α) (hs : s.Nonempty)
    (f : α → ℝ) (hf : ∀ a ∈ s, 0 ≤ f a) :
    pmExpectation (PMF.uniformOfFinset s hs) (fun a => ENNReal.ofReal (f a)) =
      ENNReal.ofReal ((∑ a ∈ s, f a) / s.card) := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  rw [pmExpectation_uniform, ENNReal.ofReal_div_of_pos hc,
    ENNReal.ofReal_sum_of_nonneg hf]
  simp [div_eq_mul_inv, mul_comm]

lemma uniform_harmonic_budget {α : Type*} (s : Finset α) (hs : s.Nonempty)
    (f : α → ℝ) (hf : ∀ a ∈ s, 0 ≤ f a) (a : ℕ)
    (hcard : a + 1 ≤ s.card)
    (hbudget : (∑ x ∈ s, f x) ≤ ∑ j ∈ Finset.range a, (harmonic (j + 1) : ℝ)) :
    1 + pmExpectation (PMF.uniformOfFinset s hs) (fun x => ENNReal.ofReal (f x)) ≤
      ENNReal.ofReal (harmonic (a + 1) : ℝ) := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  have hsum : 0 ≤ ∑ x ∈ s, f x := Finset.sum_nonneg hf
  have hb : 1 ≤ s.card - a := by omega
  have heq : (a : ℝ) + (s.card - a : ℕ) = s.card := by exact_mod_cast (Nat.add_sub_of_le (by omega : a ≤ s.card))
  have hrec := harmonic_suffix_recursion a (s.card - a) hb
  rw [heq] at hrec
  have hreal : 1 + (∑ x ∈ s, f x) / s.card ≤ (harmonic (a + 1) : ℝ) :=
    (add_le_add le_rfl (div_le_div_of_nonneg_right hbudget hc.le)).trans hrec
  rw [pmExpectation_uniform_ofReal s hs f hf]
  have hnon : 0 ≤ (∑ x ∈ s, f x) / s.card := div_nonneg hsum hc.le
  have h := ENNReal.ofReal_le_ofReal hreal
  simpa [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) hnon] using h

end CachingML.PredMarker.PMFresh
end


section

open scoped BigOperators ENNReal

namespace CachingML.PredMarker.PMFresh

lemma uniform_harmonic_ennreal_budget {α : Type*} (s : Finset α) (hs : s.Nonempty)
    (f : α → ℝ≥0∞) (a : ℕ) (hcard : a + 1 ≤ s.card)
    (hbudget : (∑ x ∈ s, f x) ≤
      ENNReal.ofReal (∑ j ∈ Finset.range a, (harmonic (j + 1) : ℝ))) :
    1 + pmExpectation (PMF.uniformOfFinset s hs) f ≤
      ENNReal.ofReal (harmonic (a + 1) : ℝ) := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  let B : ℝ := ∑ j ∈ Finset.range a, (harmonic (j + 1) : ℝ)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ => harmonic_real_nonneg _)
  have hrec := harmonic_suffix_recursion a (s.card - a) (by omega)
  have heq : (a : ℝ) + (s.card - a : ℕ) = s.card := by exact_mod_cast (Nat.add_sub_of_le (by omega : a ≤ s.card))
  rw [heq] at hrec
  have hdiv : (s.card : ℝ≥0∞)⁻¹ * ENNReal.ofReal B = ENNReal.ofReal (B / s.card) := by
    rw [ENNReal.ofReal_div_of_pos hc]
    simp [div_eq_mul_inv, mul_comm]
  calc
    1 + pmExpectation (PMF.uniformOfFinset s hs) f =
        1 + (s.card : ℝ≥0∞)⁻¹ * ∑ x ∈ s, f x := by rw [pmExpectation_uniform]
    _ ≤ 1 + (s.card : ℝ≥0∞)⁻¹ * ENNReal.ofReal B :=
      add_le_add le_rfl (mul_le_mul le_rfl hbudget zero_le zero_le)
    _ = ENNReal.ofReal (1 + B / s.card) := by
      rw [hdiv, ENNReal.ofReal_add (by norm_num) (div_nonneg hB hc.le)]
      simp
    _ ≤ ENNReal.ofReal (harmonic (a + 1) : ℝ) := ENNReal.ofReal_le_ofReal hrec

lemma sum_ranked_candidates_le {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ≥0∞) {a : ℕ} (e : Fin a → α)
    (he : Function.Injective e) (hes : ∀ i, e i ∈ s)
    (hsink : ∀ x ∈ s, x ∉ Set.range e → f x = 0)
    (hfuture : ∀ i, f (e i) ≤ ENNReal.ofReal (harmonic (a - i.val) : ℝ)) :
    (∑ x ∈ s, f x) ≤ ENNReal.ofReal (∑ j ∈ Finset.range a, (harmonic (j + 1) : ℝ)) := by
  have hsub : Finset.univ.image e ⊆ s := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hes i
  have heq : (∑ x ∈ s, f x) = ∑ i : Fin a, f (e i) := by
    rw [← Finset.sum_image (fun i _ j _ hij => he hij)]
    symm
    apply Finset.sum_subset hsub
    intro x hxs hx
    apply hsink x hxs
    rintro ⟨i, rfl⟩
    exact hx (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  rw [heq]
  calc
    (∑ i : Fin a, f (e i)) ≤ ∑ i : Fin a, ENNReal.ofReal (harmonic (a - i.val) : ℝ) :=
      Finset.sum_le_sum (fun i _ => hfuture i)
    _ = ENNReal.ofReal (∑ i : Fin a, (harmonic (a - i.val) : ℝ)) :=
      (ENNReal.ofReal_sum_of_nonneg (fun i _ => harmonic_real_nonneg _)).symm
    _ = _ := by rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (harmonic (a - j) : ℝ)) a, harmonic_rank_sum]

lemma ranked_uniform_harmonic_budget {α : Type*} [DecidableEq α]
    (s : Finset α) (hs : s.Nonempty) (f : α → ℝ≥0∞) {a : ℕ}
    (hcard : a + 1 ≤ s.card) (e : Fin a → α) (he : Function.Injective e)
    (hes : ∀ i, e i ∈ s) (hsink : ∀ x ∈ s, x ∉ Set.range e → f x = 0)
    (hfuture : ∀ i, f (e i) ≤ ENNReal.ofReal (harmonic (a - i.val) : ℝ)) :
    1 + pmExpectation (PMF.uniformOfFinset s hs) f ≤
      ENNReal.ofReal (harmonic (a + 1) : ℝ) :=
  uniform_harmonic_ennreal_budget s hs f a hcard
    (sum_ranked_candidates_le s f e he hes hsink hfuture)

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

lemma sorted_finite_enumeration {α : Type*} [DecidableEq α] (A : Finset α)
    (time : α → ℕ) (ht : Set.InjOn time (↑A : Set α)) :
    ∃ e : Fin A.card → α, Function.Injective e ∧ (∀ i, e i ∈ A) ∧
      (∀ x ∈ A, ∃ i, e i = x) ∧ StrictMono (fun i => time (e i)) := by
  classical
  let B := A.image time
  have hcard : B.card = A.card := Finset.card_image_iff.mpr ht
  let ord : Fin A.card ≃o B := B.orderIsoOfFin hcard
  have hw : ∀ i : Fin A.card, ∃ x ∈ A, time x = (ord i).val := by
    intro i
    exact Finset.mem_image.mp (ord i).property
  choose e he het using hw
  have hmono : StrictMono (fun i => time (e i)) := by
    intro i j hij
    change time (e i) < time (e j)
    rw [het, het]
    exact ord.strictMono hij
  refine ⟨e, ?_, he, ?_, hmono⟩
  · intro i j hij
    exact hmono.injective (congrArg time hij)
  · intro x hx
    let y : B := ⟨time x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
    obtain ⟨i, hi⟩ := ord.surjective y
    refine ⟨i, ht (he i) hx ?_⟩
    rw [het, hi]

lemma later_candidates_card {α : Type*} [DecidableEq α] (A : Finset α) (time : α → ℕ)
    (e : Fin A.card → α) (he : Function.Injective e) (hem : ∀ i, e i ∈ A)
    (hes : ∀ x ∈ A, ∃ i, e i = x) (hmono : StrictMono (fun i => time (e i)))
    (i : Fin A.card) :
    (A.filter (fun x => time (e i) < time x)).card = A.card - 1 - i.val := by
  have hset : A.filter (fun x => time (e i) < time x) = (Finset.Ioi i).image e := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxA, htime⟩ := Finset.mem_filter.mp hx
      obtain ⟨j, rfl⟩ := hes x hxA
      exact Finset.mem_image.mpr ⟨j, Finset.mem_Ioi.mpr (hmono.lt_iff_lt.mp htime), rfl⟩
    · intro hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_filter.mpr ⟨hem j, hmono (Finset.mem_Ioi.mp hj)⟩
  rw [hset, Finset.card_image_of_injective _ he, Fin.card_Ioi]

lemma later_subset_card_bound {α : Type*} [DecidableEq α] (A R : Finset α) (time : α → ℕ)
    (e : Fin A.card → α) (he : Function.Injective e) (hem : ∀ i, e i ∈ A)
    (hes : ∀ x ∈ A, ∃ i, e i = x) (hmono : StrictMono (fun i => time (e i)))
    (i : Fin A.card) (hR : R ⊆ A.filter (fun x => time (e i) < time x)) :
    R.card + 1 ≤ A.card - i.val := by
  have hcard := Finset.card_le_card hR
  rw [later_candidates_card A time e he hem hes hmono i] at hcard
  have hi := i.isLt
  omega

end CachingML.PredMarker.PMFresh
end


section

open scoped ENNReal

namespace CachingML.PredMarker.PMFresh

noncomputable def arrivalPotential {α : Type*} [DecidableEq α]
    (A : Finset α) (time : α → ℕ) (x : α) : ℝ≥0∞ :=
  if x ∈ A then ENNReal.ofReal (harmonic (1 + (A.filter (fun y => time x < time y)).card) : ℝ)
  else 0

lemma arrivalPotential_mono {α : Type*} [DecidableEq α] {A B : Finset α}
    (hAB : A ⊆ B) (time : α → ℕ) (x : α) :
    arrivalPotential A time x ≤ arrivalPotential B time x := by
  unfold arrivalPotential
  by_cases hx : x ∈ A
  · rw [if_pos hx, if_pos (hAB hx)]
    apply ENNReal.ofReal_le_ofReal
    apply harmonic_real_monotone
    exact Nat.add_le_add_left (Finset.card_le_card (Finset.filter_subset_filter _ hAB)) 1
  · rw [if_neg hx]
    exact zero_le

lemma uniform_arrivalPotential {α : Type*} [DecidableEq α]
    (U A : Finset α) (hU : U.Nonempty) (hAU : A ⊆ U)
    (hcard : A.card + 1 ≤ U.card) (time : α → ℕ)
    (ht : Set.InjOn time (↑A : Set α)) :
    1 + pmExpectation (PMF.uniformOfFinset U hU) (arrivalPotential A time) ≤
      ENNReal.ofReal (harmonic (A.card + 1) : ℝ) := by
  obtain ⟨e, he, hem, hes, hmono⟩ := sorted_finite_enumeration A time ht
  apply ranked_uniform_harmonic_budget U hU (arrivalPotential A time) hcard e he
    (fun i => hAU (hem i))
  · intro x _ hx
    have hxA : x ∉ A := by
      intro hm
      obtain ⟨i, hi⟩ := hes x hm
      exact hx ⟨i, hi⟩
    simp [arrivalPotential, hxA]
  · intro i
    unfold arrivalPotential
    rw [if_pos (hem i)]
    apply ENNReal.ofReal_le_ofReal
    apply harmonic_real_monotone
    have hbound := later_subset_card_bound A
      (A.filter (fun x => time (e i) < time x)) time e he hem hes hmono i (Finset.Subset.refl _)
    omega

lemma uniform_arrivalPotential_domination {α : Type*} [DecidableEq α]
    (U A : Finset α) (hU : U.Nonempty) (hAU : A ⊆ U)
    (hcard : A.card + 1 ≤ U.card) (time : α → ℕ)
    (ht : Set.InjOn time (↑A : Set α)) (F : α → ℝ≥0∞)
    (hF : ∀ x ∈ U, F x ≤ arrivalPotential A time x) :
    1 + pmExpectation (PMF.uniformOfFinset U hU) F ≤
      ENNReal.ofReal (harmonic (A.card + 1) : ℝ) := by
  apply (add_le_add le_rfl (pmExpectation_mono _ (fun x hx => hF x (by simpa using hx)))).trans
  exact uniform_arrivalPotential U A hU hAU hcard time ht

end CachingML.PredMarker.PMFresh
end


section

open scoped ENNReal

namespace CachingML.PredMarker.PMFresh

noncomputable def missingRepresentativePotential {α : Type*} [DecidableEq α]
    (F A : Finset α) (time : α → ℕ) (x : α) : ℝ≥0∞ :=
  if x ∈ F then ENNReal.ofReal (harmonic (1 + (A.filter (fun y => time x < time y)).card) : ℝ)
  else 0

lemma missingRepresentativePotential_shrink {α : Type*} [DecidableEq α]
    {F G A B : Finset α} (hFG : F ⊆ G) (hAB : A ⊆ B) (time : α → ℕ) (x : α) :
    missingRepresentativePotential F A time x ≤ missingRepresentativePotential G B time x := by
  unfold missingRepresentativePotential
  by_cases hx : x ∈ F
  · rw [if_pos hx, if_pos (hFG hx)]
    apply ENNReal.ofReal_le_ofReal
    apply harmonic_real_monotone
    exact Nat.add_le_add_left (Finset.card_le_card (Finset.filter_subset_filter _ hAB)) 1
  · rw [if_neg hx]
    exact zero_le

lemma missingRepresentativePotential_victim_eq {α : Type*} [DecidableEq α]
    (F U : Finset α) (time : α → ℕ) {x : α} (hx : x ∈ U) :
    missingRepresentativePotential F (U ∩ F) time x = arrivalPotential (U ∩ F) time x := by
  unfold missingRepresentativePotential arrivalPotential
  by_cases hF : x ∈ F <;> simp [hF, hx]

lemma missingRepresentativePotential_current_bound {α : Type*} [DecidableEq α]
    (F A : Finset α) (time : α → ℕ) (x : α) :
    missingRepresentativePotential F A time x ≤ ENNReal.ofReal (harmonic (1 + A.card) : ℝ) := by
  unfold missingRepresentativePotential
  split_ifs
  · apply ENNReal.ofReal_le_ofReal
    apply harmonic_real_monotone
    exact Nat.add_le_add_left (Finset.card_filter_le _ _) 1
  · exact zero_le

lemma uniform_missingRepresentativePotential {α : Type*} [DecidableEq α]
    (F U : Finset α) (hU : U.Nonempty) (time : α → ℕ)
    (hcard : (U ∩ F).card + 1 ≤ U.card)
    (ht : Set.InjOn time (↑(U ∩ F) : Set α))
    (after : α → Finset α) (hafter : ∀ x ∈ U, after x ⊆ U ∩ F) :
    1 + pmExpectation (PMF.uniformOfFinset U hU)
      (fun x => missingRepresentativePotential F (after x) time x) ≤
      ENNReal.ofReal (harmonic ((U ∩ F).card + 1) : ℝ) := by
  apply uniform_arrivalPotential_domination U (U ∩ F) hU Finset.inter_subset_left hcard time ht
  intro x hx
  calc
    missingRepresentativePotential F (after x) time x ≤
        missingRepresentativePotential F (U ∩ F) time x :=
      missingRepresentativePotential_shrink (Finset.Subset.refl _) (hafter x hx) time x
    _ = arrivalPotential (U ∩ F) time x := missingRepresentativePotential_victim_eq F U time hx

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh
variable {α : Type*} [DecidableEq α]

lemma phaseFuture_subset_union (k : ℕ) (M : Finset α) (τ : List α) :
    phaseFuture k M τ ⊆ M ∪ τ.toFinset := by
  induction τ generalizing M with
  | nil => simp [phaseFuture]
  | cons z τ ih =>
    rw [phaseFuture]
    split_ifs
    · have hi := ih (insert z M)
      intro x hx
      have hh := hi hx
      simpa [Finset.insert_union, Finset.union_insert] using hh
    · exact Finset.subset_union_left

lemma phaseFuture_unmarked_mem (k : ℕ) (M : Finset α) (τ : List α)
    {x : α} (hx : x ∈ phaseFuture k M τ) (hxM : x ∉ M) : x ∈ τ := by
  have hh := phaseFuture_subset_union k M τ hx
  exact List.mem_toFinset.mp ((Finset.mem_union.mp hh).resolve_left hxM)

lemma arrivalIndex_injective (τ : List α) : Set.InjOn τ.idxOf (↑τ.toFinset : Set α) := by
  intro x hx y hy hxy
  have hx' : x ∈ τ := List.mem_toFinset.mp hx
  have hy' : y ∈ τ := List.mem_toFinset.mp hy
  have hxl : τ.idxOf x < τ.length := List.idxOf_lt_length_iff.mpr hx'
  have hyl : τ.idxOf y < τ.length := List.idxOf_lt_length_iff.mpr hy'
  have he : τ[τ.idxOf x] = x := List.getElem_idxOf hxl
  have hf : τ[τ.idxOf y] = y := List.getElem_idxOf hyl
  change τ.idxOf x = τ.idxOf y at hxy
  have hfin : (⟨τ.idxOf x, hxl⟩ : Fin τ.length) = ⟨τ.idxOf y, hyl⟩ := Fin.ext hxy
  have hget := congrArg τ.get hfin
  exact he.symm.trans (hget.trans hf)

lemma arrivalIndex_cons_ne (τ : List α) {x z : α} (hx : x ≠ z) :
    (z :: τ).idxOf x = τ.idxOf x + 1 := by
  simp [Ne.symm hx]

lemma arrivalIndex_cons_compare (τ : List α) {x y z : α} (hx : x ≠ z) (hy : y ≠ z) :
    ((z :: τ).idxOf x < (z :: τ).idxOf y) ↔ τ.idxOf x < τ.idxOf y := by
  rw [arrivalIndex_cons_ne τ hx, arrivalIndex_cons_ne τ hy]
  omega

lemma missingPotential_cons_eq (F A : Finset α) (τ : List α) {x z : α}
    (hx : x ≠ z) (hzA : z ∉ A) :
    missingRepresentativePotential F A (z :: τ).idxOf x =
      missingRepresentativePotential F A τ.idxOf x := by
  have heq : A.filter (fun y => (z :: τ).idxOf x < (z :: τ).idxOf y) =
      A.filter (fun y => τ.idxOf x < τ.idxOf y) := by
    apply Finset.ext
    intro y
    by_cases hy : y ∈ A
    · have hyz : y ≠ z := ne_of_mem_of_not_mem hy hzA
      simp only [Finset.mem_filter, hy, true_and, arrivalIndex_cons_compare τ hx hyz]
    · simp [hy]
  unfold missingRepresentativePotential
  rw [heq]
end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh
variable {α : Type*} [DecidableEq α]

lemma step_chainOf_missing_other {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) {s : PMState α} (hs : CacheInvariant k s)
    (i : ℕ) (z : α) (hz : ℝ) {v : PMState α}
    (hv : v ∈ (step k tb s i z hz).support) {x : α}
    (hx : x ∉ s.cache) : v.chainOf x = s.chainOf x := by
  let t := savePrediction s i z hz
  let u := phaseStart k t
  rw [step_factored] at hv
  change v ∈ (if z ∈ t.cache ∨ t.cache.card < k then PMF.pure (hitOrFill t z)
    else if z ∉ u.stale then PMF.pure (evictInto (cleanState u) z (u.clean + 1) (tb (cleanState u)))
    else if (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ) then
      PMF.pure (evictInto (staleState u z) z (u.chainOf z) (tb (staleState u z)))
    else randomEviction (staleState u z) z (u.chainOf z)).support at hv
  have huc : u.cache = s.cache := by change (phaseStart k t).cache = _; rw [phaseStart_cache]; rfl
  have huo : u.chainOf = s.chainOf := by dsimp [u, phaseStart]; split_ifs <;> rfl
  by_cases hh : z ∈ t.cache ∨ t.cache.card < k
  · rw [if_pos hh] at hv
    have he := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    rfl
  · rw [if_neg hh] at hv
    have ht : CacheInvariant k t := save_cacheInvariant hs i z hz
    have hf : t.cache.card = k := by have := ht.card_le; simp only [not_or] at hh; omega
    have hne : (u.cache \ u.marked).Nonempty := phaseStart_candidates_nonempty hk ht hf
    have hxe (e : α) (he : e ∈ u.cache) : x ≠ e := by
      intro heq
      subst e
      exact hx (huc ▸ he)
    by_cases hc : z ∉ u.stale
    · rw [if_pos hc] at hv
      have he := (PMF.mem_support_pure_iff _ _).mp hv
      subst v
      change Function.update u.chainOf (tb (cleanState u)) (u.clean + 1) x = _
      rw [Function.update_of_ne (hxe _ (Finset.mem_sdiff.mp (htb (cleanState u) hne).1).1), huo]
    · rw [if_neg hc] at hv
      by_cases hr : (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ)
      · rw [if_pos hr] at hv
        have he := (PMF.mem_support_pure_iff _ _).mp hv
        subst v
        change Function.update u.chainOf (tb (staleState u z)) (u.chainOf z) x = _
        rw [Function.update_of_ne (hxe _ (Finset.mem_sdiff.mp (htb (staleState u z) hne).1).1), huo]
      · rw [if_neg hr] at hv
        obtain ⟨e, he, rfl⟩ := randomEviction_support (s := staleState u z) hne hv
        change Function.update u.chainOf e (u.chainOf z) x = _
        rw [Function.update_of_ne (hxe _ (Finset.mem_sdiff.mp he).1), huo]

lemma step_representative_persists {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) {s : PMState α} (hs : CacheInvariant k s)
    (i : ℕ) (z : α) (hz : ℝ) {v : PMState α}
    (hv : v ∈ (step k tb s i z hz).support) (hp : v.phase = s.phase)
    {x : α} (hx : x ∈ s.stale \ s.cache) (hxz : x ≠ z) :
    x ∈ v.stale \ v.cache ∧ v.chainOf x = s.chainOf x :=
  ⟨step_missing_other hk tb hs i z hz hv hp hx hxz,
    step_chainOf_missing_other hk tb htb hs i z hz hv (Finset.mem_sdiff.mp hx).2⟩
end CachingML.PredMarker.PMFresh
end


section

open scoped ENNReal
namespace CachingML.PredMarker.PMFresh
variable {α : Type*} [DecidableEq α]

noncomputable def nativeArrivalPotential (k : ℕ) (s : PMState α) (τ : List α) (x : α) : ℝ≥0∞ :=
  let F := phaseFuture k s.marked τ
  missingRepresentativePotential F ((s.cache \ s.marked) ∩ F) τ.idxOf x

lemma nativeArrivalPotential_other_step {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    {s : PMState α} (hs : CacheInvariant k s) (i : ℕ) (z : α) (hz : ℝ)
    {v : PMState α} (hv : v ∈ (step k tb s i z hz).support)
    (hp : v.phase = s.phase) (τ : List α) {x : α} (hx : x ≠ z) :
    nativeArrivalPotential k v τ x ≤ nativeArrivalPotential k s (z :: τ) x := by
  have hF := step_phaseFuture_same hk tb hs i z hz hv hp τ
  have hU := step_unmarked_subset hk tb hs i z hz hv hp
  have hzM := (step_same_phase_fields hk tb hs i z hz hv hp).2.2
  unfold nativeArrivalPotential
  dsimp only
  rw [hF]
  rw [← missingPotential_cons_eq _ _ τ hx (by
    intro hzA
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hzA).1).2 hzM)]
  exact missingRepresentativePotential_shrink (Finset.Subset.refl _)
    (Finset.inter_subset_inter_right hU) _ _

lemma nativeArrivalPotential_nil (k : ℕ) (s : PMState α) {x : α}
    (hx : x ∈ s.stale \ s.cache) (hs : CacheInvariant k s) :
    nativeArrivalPotential k s [] x = 0 := by
  have hxM : x ∉ s.marked := fun hm => (Finset.mem_sdiff.mp hx).2 (hs.marked_subset hm)
  simp [nativeArrivalPotential, phaseFuture, missingRepresentativePotential, hxM]

lemma evict_unmarked_subset (s : PMState α) (z e : α) (c : ℕ) :
    (evictInto s z c e).cache \ (evictInto s z c e).marked ⊆ s.cache \ s.marked := by
  intro x hx
  change x ∈ insert z (s.cache.erase e) \ insert z s.marked at hx
  obtain ⟨hxC, hxM⟩ := Finset.mem_sdiff.mp hx
  have hxz : x ≠ z := fun he => hxM (he ▸ Finset.mem_insert_self z s.marked)
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase ((Finset.mem_insert.mp hxC).resolve_left hxz),
    fun hm => hxM (Finset.mem_insert_of_mem hm)⟩

lemma evict_nativeArrivalPotential_le (k : ℕ) (s : PMState α) (τ : List α)
    {z e : α} (hzM : s.marked.card < k) (hez : e ≠ z) (c : ℕ) :
    nativeArrivalPotential k (evictInto s z c e) τ e ≤
      missingRepresentativePotential (phaseFuture k s.marked (z :: τ))
        ((s.cache \ s.marked) ∩ phaseFuture k s.marked (z :: τ)) (z :: τ).idxOf e := by
  have hF : phaseFuture k (insert z s.marked) τ = phaseFuture k s.marked (z :: τ) := by
    simp [phaseFuture, hzM]
  unfold nativeArrivalPotential
  dsimp only [evictInto]
  rw [hF]
  rw [← missingPotential_cons_eq _ _ τ hez (by simp)]
  exact missingRepresentativePotential_shrink (Finset.Subset.refl _)
    (Finset.inter_subset_inter_right (evict_unmarked_subset s z e c)) _ _
end CachingML.PredMarker.PMFresh
end


section

open scoped ENNReal
namespace CachingML.PredMarker.PMFresh
variable {α : Type*} [DecidableEq α]

lemma current_nativeArrivalPotential (k : ℕ) (s : PMState α) (τ : List α)
    {z : α} (hzC : z ∉ s.cache) (hm : s.marked.card < k) :
    nativeArrivalPotential k s (z :: τ) z = ENNReal.ofReal
      (harmonic (1 + ((s.cache \ s.marked) ∩ phaseFuture k s.marked (z :: τ)).card) : ℝ) := by
  have hzF : z ∈ phaseFuture k s.marked (z :: τ) := mem_phaseFuture_cons k _ _ _ (Or.inr hm)
  unfold nativeArrivalPotential missingRepresentativePotential
  dsimp only
  rw [if_pos hzF]
  have hfilter : ((s.cache \ s.marked) ∩ phaseFuture k s.marked (z :: τ)).filter
      (fun y => (z :: τ).idxOf z < (z :: τ).idxOf y) =
      (s.cache \ s.marked) ∩ phaseFuture k s.marked (z :: τ) := by
    apply Finset.filter_eq_self.mpr
    intro y hy
    have hyz : y ≠ z := ne_of_mem_of_not_mem (Finset.mem_sdiff.mp (Finset.mem_inter.mp hy).1).1 hzC
    rw [List.idxOf_cons_self, arrivalIndex_cons_ne τ hyz]
    omega
  rw [hfilter]

lemma uniform_nativeArrivalPotential (k : ℕ) (s : PMState α) (τ : List α)
    {z : α} (hzC : z ∉ s.cache) (hC : s.cache.card = k)
    (hm : s.marked.card < k) (_hM : s.marked ⊆ s.cache)
    (hne : (s.cache \ s.marked).Nonempty) (c : ℕ) :
    1 + pmExpectation (PMF.uniformOfFinset (s.cache \ s.marked) hne)
      (fun e => nativeArrivalPotential k (evictInto s z c e) τ e) ≤
        nativeArrivalPotential k s (z :: τ) z := by
  let F := phaseFuture k s.marked (z :: τ)
  let U := s.cache \ s.marked
  have hF : F.card ≤ k := phaseFuture_card_le k s.marked (by omega) _
  have hzF : z ∈ F := mem_phaseFuture_cons k _ _ _ (Or.inr hm)
  have hcard : (U ∩ F).card + 1 ≤ U.card :=
    finite_future_candidates_card s.cache s.marked F hC hF (subset_phaseFuture k _ _) hzF hzC
  have htime : Set.InjOn (z :: τ).idxOf (↑(U ∩ F) : Set α) := by
    apply (arrivalIndex_injective (z :: τ)).mono
    intro x hx
    have hh := Finset.mem_inter.mp hx
    exact List.mem_toFinset.mpr (phaseFuture_unmarked_mem k s.marked (z :: τ) hh.2
      (Finset.mem_sdiff.mp hh.1).2)
  rw [current_nativeArrivalPotential k s τ hzC hm]
  have hb := uniform_arrivalPotential_domination U (U ∩ F) hne Finset.inter_subset_left
    hcard (z :: τ).idxOf htime
    (fun e => nativeArrivalPotential k (evictInto s z c e) τ e) (by
      intro e he
      have hez : e ≠ z := ne_of_mem_of_not_mem (Finset.mem_sdiff.mp he).1 hzC
      exact (evict_nativeArrivalPotential_le k s τ hm hez c).trans_eq
        (missingRepresentativePotential_victim_eq F U (z :: τ).idxOf he))
  simpa only [Nat.add_comm] using hb
end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh
variable {α : Type*} [DecidableEq α]

lemma phaseStep_number_mono (k : ℕ) (s : PhaseState α) (z : α) :
    s.number ≤ (phaseStep k s z).number := by
  unfold phaseStep
  split_ifs <;> simp

lemma step_phase_mono {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    {s : PMState α} (hs : CacheInvariant k s) (i : ℕ) (z : α) (hz : ℝ)
    {v : PMState α} (hv : v ∈ (step k tb s i z hz).support) : s.phase ≤ v.phase := by
  have hh := congrArg PhaseState.number (step_nativePhase hk tb hs i z hz hv)
  change v.phase = (phaseStep k (nativePhase s) z).number at hh
  rw [hh]
  exact phaseStep_number_mono k (nativePhase s) z

omit [DecidableEq α] in
lemma phaseStart_phase_ge (k : ℕ) (s : PMState α) : s.phase ≤ (phaseStart k s).phase := by
  unfold phaseStart
  split_ifs <;> simp

lemma step_old_phase_length {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    {s : PMState α} (hs : CacheInvariant k s) (i : ℕ) (z : α) (hz : ℝ)
    {v : PMState α} (hv : v ∈ (step k tb s i z hz).support)
    {r c : ℕ} (hr : r < s.phase) : v.chainLen r c = s.chainLen r c := by
  rw [step_factored] at hv
  dsimp only at hv
  let t := savePrediction s i z hz
  let u := phaseStart k t
  have huph : s.phase ≤ u.phase := phaseStart_phase_ge k t
  have hru : r ≠ u.phase := by omega
  have hul : u.chainLen = s.chainLen := by dsimp [u, phaseStart]; split_ifs <;> rfl
  by_cases hh : z ∈ t.cache ∨ t.cache.card < k
  · simp only [show z ∈ (savePrediction s i z hz).cache ∨
      (savePrediction s i z hz).cache.card < k from hh, if_pos] at hv
    have he := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    rfl
  · simp only [show ¬(z ∈ (savePrediction s i z hz).cache ∨
      (savePrediction s i z hz).cache.card < k) from hh, if_false] at hv
    have ht : CacheInvariant k t := save_cacheInvariant hs i z hz
    have hf : t.cache.card = k := by have := ht.card_le; simp only [not_or] at hh; omega
    have hne : (u.cache \ u.marked).Nonempty := phaseStart_candidates_nonempty hk ht hf
    by_cases hc : z ∉ u.stale
    · rw [if_pos hc] at hv
      have he := (PMF.mem_support_pure_iff _ _).mp hv
      subst v
      change Function.update u.chainLen u.phase _ r c = _
      rw [Function.update_of_ne hru, hul]
    · rw [if_neg hc] at hv
      by_cases hR : (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ)
      · rw [if_pos hR] at hv
        have he := (PMF.mem_support_pure_iff _ _).mp hv
        subst v
        change Function.update u.chainLen u.phase _ r c = _
        rw [Function.update_of_ne hru, hul]
      · rw [if_neg hR] at hv
        obtain ⟨e, _, rfl⟩ := randomEviction_support (s := staleState u z) hne hv
        change Function.update u.chainLen u.phase _ r c = _
        rw [Function.update_of_ne hru, hul]
end CachingML.PredMarker.PMFresh
end


section

open scoped BigOperators

namespace CachingML.PredMarker.PMFresh

structure IndexFamilyValid {ι : Type*} (n : ℕ) (I : ι → List ℕ) : Prop where
  nodup : ∀ p, (I p).Nodup
  separate : ∀ p q, p ≠ q → ∀ j, j ∈ I p → j ∉ I q
  bounded : ∀ p j, j ∈ I p → j < n

lemma IndexFamilyValid.empty {ι : Type*} (n : ℕ) :
    IndexFamilyValid n (fun _ : ι => []) := by
  constructor <;> simp

lemma IndexFamilyValid.mono {ι : Type*} {n m : ℕ} {I : ι → List ℕ}
    (h : IndexFamilyValid n I) (hnm : n ≤ m) : IndexFamilyValid m I :=
  ⟨h.nodup, h.separate, fun p j hj => (h.bounded p j hj).trans_le hnm⟩

lemma mem_update_append {ι : Type*} [DecidableEq ι] (I : ι → List ℕ) (p q : ι) (j v : ℕ) :
    v ∈ Function.update I p (I p ++ [j]) q ↔ v ∈ I q ∨ (q = p ∧ v = j) := by
  by_cases h : q = p
  · subst q; simp
  · simp [h]

lemma IndexFamilyValid.append {ι : Type*} [DecidableEq ι] {n : ℕ} {I : ι → List ℕ}
    (h : IndexFamilyValid n I) (p : ι) (j : ℕ) (hj : j < n)
    (hfresh : ∀ q, j ∉ I q) : IndexFamilyValid n (Function.update I p (I p ++ [j])) := by
  constructor
  · intro q
    by_cases hq : q = p
    · subst q
      simp only [Function.update_self]
      rw [List.nodup_append]
      refine ⟨h.nodup p, by simp, ?_⟩
      intro x hx y hy
      have hyj : y = j := by simpa using hy
      subst y
      exact ne_of_mem_of_not_mem hx (hfresh p)
    · simpa [Function.update_of_ne hq] using h.nodup q
  · intro q r hqr v hvq hvr
    rw [mem_update_append] at hvq hvr
    rcases hvq with hvq | ⟨hqp, hvj⟩
    · rcases hvr with hvr | ⟨hrp, hvj⟩
      · exact h.separate q r hqr v hvq hvr
      · subst v; exact hfresh q hvq
    · subst v
      rcases hvr with hvr | ⟨hrp, _⟩
      · exact hfresh r hvr
      · exact hqr (hqp.trans hrp.symm)
  · intro q v hv
    rw [mem_update_append] at hv
    rcases hv with hv | ⟨_, rfl⟩
    · exact h.bounded q v hv
    · exact hj

lemma IndexFamilyValid.aggregate_loss_le {ι : Type*} [DecidableEq ι]
    {n : ℕ} {I : ι → List ℕ} (h : IndexFamilyValid n I)
    (keys : Finset ι) (loss : ℕ → ℝ) (hloss : ∀ j, 0 ≤ loss j) :
    (∑ p ∈ keys, ((I p).map loss).sum) ≤ ∑ j ∈ Finset.range n, loss j := by
  have hd : Set.PairwiseDisjoint (↑keys : Set ι) (fun p => (I p).toFinset) := by
    intro p _ q _ hpq
    apply Finset.disjoint_left.mpr
    intro j hjp hjq
    exact h.separate p q hpq j (List.mem_toFinset.mp hjp) (List.mem_toFinset.mp hjq)
  have hsub : keys.biUnion (fun p => (I p).toFinset) ⊆ Finset.range n := by
    intro j hj
    obtain ⟨p, _, hj⟩ := Finset.mem_biUnion.mp hj
    exact Finset.mem_range.mpr (h.bounded p j (List.mem_toFinset.mp hj))
  calc
    (∑ p ∈ keys, ((I p).map loss).sum) = ∑ p ∈ keys, ∑ j ∈ (I p).toFinset, loss j := by
      apply Finset.sum_congr rfl
      intro p _
      exact (List.sum_toFinset loss (h.nodup p)).symm
    _ = ∑ j ∈ keys.biUnion (fun p => (I p).toFinset), loss j := (Finset.sum_biUnion hd).symm
    _ ≤ ∑ j ∈ Finset.range n, loss j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hloss j)

end CachingML.PredMarker.PMFresh
end


section

open scoped BigOperators

namespace CachingML.PredMarker.PMFresh

lemma lossAt_nonneg {α : Type*} [DecidableEq α] (ℓ : ℝ → ℝ → ℝ)
    (hℓ : ∀ a b, 0 ≤ ℓ a b) (σ : List α) (h : Fin σ.length → ℝ) (j : ℕ) :
    0 ≤ lossAt ℓ σ h j := by
  unfold lossAt
  split_ifs
  · exact hℓ _ _
  · exact le_rfl

lemma sum_lossAt_eq_predError {α : Type*} [DecidableEq α]
    (ℓ : ℝ → ℝ → ℝ) (σ : List α) (h : Fin σ.length → ℝ) :
    (∑ j ∈ Finset.range σ.length, lossAt ℓ σ h j) = predError ℓ σ h := by
  rw [← Fin.sum_univ_eq_sum_range]
  unfold predError
  apply Finset.sum_congr rfl
  intro i _
  simp [lossAt, i.isLt]

lemma indexFamily_loss_le_predError {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (ℓ : ℝ → ℝ → ℝ) (hℓ : ∀ a b, 0 ≤ ℓ a b)
    (σ : List α) (h : Fin σ.length → ℝ) (I : ι → List ℕ)
    (hI : IndexFamilyValid σ.length I) (keys : Finset ι) :
    (∑ p ∈ keys, ((I p).map (lossAt ℓ σ h)).sum) ≤ predError ℓ σ h := by
  rw [← sum_lossAt_eq_predError]
  exact hI.aggregate_loss_le keys _ (lossAt_nonneg ℓ hℓ σ h)

end CachingML.PredMarker.PMFresh
end


section

open scoped ENNReal

namespace CachingML.PredMarker.PMFresh

variable {α β : Type*}

noncomputable def kernelRun (f : α → β → PMF α) (s : α) : List β → PMF α
  | [] => PMF.pure s
  | b :: l => (f s b).bind (fun t => kernelRun f t l)

noncomputable def historyRun (f : α → β → PMF α) (s : α) :
    List β → PMF (α × List (α × β × α))
  | [] => PMF.pure (s, [])
  | b :: l => (f s b).bind (fun t =>
      (historyRun f t l).map (fun p => (p.1, (s, b, t) :: p.2)))

theorem kernelRun_fold (f : α → β → PMF α) (l : List β) (p : PMF α) :
    l.foldl (fun q b => q.bind (fun s => f s b)) p =
      p.bind (fun s => kernelRun f s l) := by
  induction l generalizing p with
  | nil => simp [kernelRun]
  | cons b l ih =>
    simp only [List.foldl_cons, ih, kernelRun, PMF.bind_bind]

theorem historyRun_endpoint (f : α → β → PMF α) (l : List β) (s : α) :
    (historyRun f s l).map Prod.fst = kernelRun f s l := by
  induction l generalizing s with
  | nil => simp [historyRun, kernelRun, PMF.pure_map]
  | cons b l ih =>
    simp only [historyRun, PMF.map_bind, PMF.map_comp, Function.comp_def, kernelRun]
    congr 1
    funext t
    exact ih t

theorem kernelRun_support_invariant (f : α → β → PMF α) (P : α → Prop)
    (hf : ∀ s, P s → ∀ b t, t ∈ (f s b).support → P t)
    (l : List β) (s : α) (hs : P s) :
    ∀ t ∈ (kernelRun f s l).support, P t := by
  induction l generalizing s with
  | nil =>
    intro t ht
    have he : t = s := (PMF.mem_support_pure_iff _ _).mp ht
    exact he.symm ▸ hs
  | cons b l ih =>
    intro t ht
    obtain ⟨u, hu, ht⟩ := (PMF.mem_support_bind_iff _ _ _).mp ht
    exact ih u (hf s hs b u hu) t ht

theorem historyRun_finite_support (f : α → β → PMF α)
    (hf : ∀ s b, (f s b).support.Finite) (l : List β) (s : α) :
    (historyRun f s l).support.Finite := by
  induction l generalizing s with
  | nil => simp [historyRun]
  | cons b l ih =>
    apply finite_support_bind _ _ (hf s b)
    intro t _
    exact finite_support_map _ _ (ih t)

def ValidHistory (f : α → β → PMF α) : α → List β → α → List (α × β × α) → Prop
  | s, [], u, L => u = s ∧ L = []
  | s, b :: l, u, L => ∃ t, t ∈ (f s b).support ∧
      ∃ R, L = (s, b, t) :: R ∧ ValidHistory f t l u R

theorem historyRun_valid (f : α → β → PMF α) (l : List β) (s : α)
    {p : α × List (α × β × α)} (hp : p ∈ (historyRun f s l).support) :
    ValidHistory f s l p.1 p.2 := by
  induction l generalizing s p with
  | nil =>
    have he : p = (s, []) := (PMF.mem_support_pure_iff _ _).mp hp
    subst p
    exact ⟨rfl, rfl⟩
  | cons b l ih =>
    obtain ⟨t, ht, hp⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
    obtain ⟨q, hq, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
    exact ⟨t, ht, q.2, rfl, ih t hq⟩

theorem pmExpectation_bind (p : PMF α) (f : α → PMF β) (g : β → ℝ≥0∞) :
    pmExpectation (p.bind f) g = pmExpectation p (fun a => pmExpectation (f a) g) := by
  unfold pmExpectation
  simp only [PMF.bind_apply]
  simp_rw [ENNReal.tsum_mul_right.symm]
  rw [ENNReal.tsum_comm]
  simp_rw [mul_assoc]
  simp only [ENNReal.tsum_mul_left]

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

lemma step_index_prefix {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) {s : PMState α} (hs : CacheInvariant k s)
    (i : ℕ) (z : α) (hz : ℝ) {v : PMState α}
    (hv : v ∈ (step k tb s i z hz).support) (p : ℕ × ℕ) :
    indexFamily s p <+: indexFamily v p := by
  rcases step_ledger_cases hk tb htb hs i z hz hv with ⟨he, _⟩ | ⟨_, e, _, q, _, he⟩
  · rw [he]
  · rw [he]
    by_cases hp : p = q
    · subst p
      rw [Function.update_self]
      exact List.prefix_append _ _
    · rw [Function.update_of_ne hp]

lemma continuation_index_prefix {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    (l : List ℕ) {s : PMState α} (hs : CacheInvariant k s)
    {v : PMState α} (hv : v ∈ (kernelRun (fun t i => indexedStep k tb σ h i t) s l).support) :
    CacheInvariant k v ∧ ∀ p, indexFamily s p <+: indexFamily v p := by
  apply kernelRun_support_invariant (fun t i => indexedStep k tb σ h i t)
    (fun t => CacheInvariant k t ∧ ∀ p, indexFamily s p <+: indexFamily t p) _ l s
    ⟨hs, fun _ => List.prefix_refl _⟩ v hv
  intro t ht i u hu
  unfold indexedStep at hu
  split_ifs at hu with hi
  · refine ⟨step_cacheInvariant hk tb htb ht.1 i _ _ hu, ?_⟩
    intro p
    exact (ht.2 p).trans (step_index_prefix hk tb htb ht.1 i _ _ hu p)
  · have he := (PMF.mem_support_pure_iff _ _).mp hu
    subst u
    exact ht

lemma prefix_loss_sum_le {β : Type*} (F : β → ℝ) (hF : ∀ x, 0 ≤ F x)
    {A B : List β} (hAB : A <+: B) : (A.map F).sum ≤ (B.map F).sum := by
  obtain ⟨C, rfl⟩ := hAB
  rw [List.map_append, List.sum_append]
  exact le_add_of_nonneg_right (List.sum_nonneg (by intro x hx; obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx; exact hF y))

lemma continuation_chainError_mono {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (ℓ : ℝ → ℝ → ℝ) (hℓ : ∀ x y, 0 ≤ ℓ x y)
    (σ : List α) (h : Fin σ.length → ℝ) (l : List ℕ)
    {s : PMState α} (hs : CacheInvariant k s) {v : PMState α}
    (hv : v ∈ (kernelRun (fun t i => indexedStep k tb σ h i t) s l).support)
    (p : ℕ × ℕ) : chainError ℓ σ h s p.1 p.2 ≤ chainError ℓ σ h v p.1 p.2 := by
  exact prefix_loss_sum_le (lossAt ℓ σ h) (lossAt_nonneg ℓ hℓ σ h)
    ((continuation_index_prefix hk tb htb σ h l hs hv).2 p)

end CachingML.PredMarker.PMFresh
end


section

open scoped ENNReal
namespace CachingML.PredMarker.PMFresh
variable {α : Type*} [DecidableEq α]

noncomputable def trackedChainPotential (k : ℕ) (p : ℕ × ℕ) (s : PMState α) (τ : List α) : ℝ≥0∞ :=
  if s.phase = p.1 then
    ∑ x ∈ s.stale \ s.cache, if s.chainOf x = p.2 then nativeArrivalPotential k s τ x else 0
  else 0

lemma trackedChainPotential_eq {k : ℕ} {p : ℕ × ℕ} {s : PMState α}
    (hs : NativeRepresentatives s) (hp : s.phase = p.1) {x : α}
    (hx : x ∈ s.stale \ s.cache) (hc : s.chainOf x = p.2) (τ : List α) :
    trackedChainPotential k p s τ = nativeArrivalPotential k s τ x := by
  unfold trackedChainPotential
  rw [if_pos hp]
  rw [Finset.sum_eq_single x]
  · rw [if_pos hc]
  · intro y hy hyx
    have hne : s.chainOf y ≠ p.2 := by
      intro he
      exact hyx (hs.injective hy hx (he.trans hc.symm))
    rw [if_neg hne]
  · intro hnot
    exact (hnot hx).elim

lemma trackedChainPotential_past {k : ℕ} {p : ℕ × ℕ} {s : PMState α}
    (hp : p.1 < s.phase) (τ : List α) : trackedChainPotential k p s τ = 0 := by
  simp [trackedChainPotential, ne_of_gt hp]

lemma trackedChainPotential_nil (k : ℕ) (p : ℕ × ℕ) (s : PMState α)
    (hs : CacheInvariant k s) : trackedChainPotential k p s [] = 0 := by
  unfold trackedChainPotential
  split_ifs
  · apply Finset.sum_eq_zero
    intro x hx
    split_ifs
    · exact nativeArrivalPotential_nil k s hx hs
    · rfl
  · rfl

lemma step_chainLen_mono {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) {s : PMState α} (hs : OperationalInvariant k s)
    (i : ℕ) (z : α) (hz : ℝ) {v : PMState α}
    (hv : v ∈ (step k tb s i z hz).support) (p : ℕ × ℕ) :
    s.chainLen p.1 p.2 ≤ v.chainLen p.1 p.2 := by
  have hvO := step_operationalInvariant hk tb htb hs i z hz hv
  change lengthFamily s p ≤ lengthFamily v p
  rw [hs.bookkeeping.lengths p, hvO.bookkeeping.lengths p]
  exact (step_index_prefix hk tb htb hs.cache i z hz hv p).length_le
end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

theorem stale_miss_no_reset (k : ℕ) (s : PMState α) (i : ℕ) (z : α) (hz : ℝ)
    (hzc : z ∉ s.cache) (hzS : z ∈ (phaseStart k (savePrediction s i z hz)).stale) :
    s.marked.card ≠ k ∧ phaseStart k (savePrediction s i z hz) = savePrediction s i z hz ∧
      z ∈ s.stale := by
  by_cases hm : s.marked.card = k
  · have hzc' : z ∈ s.cache := by simpa [phaseStart, savePrediction, hm] using hzS
    exact False.elim (hzc hzc')
  · have he : phaseStart k (savePrediction s i z hz) = savePrediction s i z hz := by
      simp [phaseStart, savePrediction, hm]
    refine ⟨hm, he, ?_⟩
    rw [he] at hzS
    exact hzS

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh
variable {α : Type*} [DecidableEq α]

lemma clean_eviction_existing_length (k : ℕ) (s : PMState α) (i : ℕ) (z e : α)
    (hz : ℝ) {c : ℕ} (hc : c ≤ s.clean) :
    let u := phaseStart k (savePrediction s i z hz)
    (evictInto (cleanState u) z (u.clean + 1) e).chainLen s.phase c = s.chainLen s.phase c := by
  dsimp only
  by_cases hm : s.marked.card = k
  · simp [phaseStart, savePrediction, hm, evictInto, cleanState, Function.update_of_ne]
  · have hne : c ≠ s.clean + 1 := by omega
    simp [phaseStart, savePrediction, hm, evictInto, cleanState, hne]

lemma step_length_other_missing {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (_htb : IsMaxTieBreak tb) {s : PMState α} (hs : OperationalInvariant k s)
    (i : ℕ) (z : α) (hz : ℝ) {v : PMState α}
    (hv : v ∈ (step k tb s i z hz).support) {x : α}
    (hx : x ∈ s.stale \ s.cache) (hxz : x ≠ z) :
    v.chainLen s.phase (s.chainOf x) = s.chainLen s.phase (s.chainOf x) := by
  let t := savePrediction s i z hz
  let u := phaseStart k t
  have hc := (hs.representatives.bounds x hx).2
  rw [step_factored] at hv
  change v ∈ (if z ∈ t.cache ∨ t.cache.card < k then PMF.pure (hitOrFill t z)
    else if z ∉ u.stale then PMF.pure (evictInto (cleanState u) z (u.clean + 1) (tb (cleanState u)))
    else if (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ) then
      PMF.pure (evictInto (staleState u z) z (u.chainOf z) (tb (staleState u z)))
    else randomEviction (staleState u z) z (u.chainOf z)).support at hv
  by_cases hh : z ∈ t.cache ∨ t.cache.card < k
  · rw [if_pos hh] at hv
    have he := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    rfl
  · rw [if_neg hh] at hv
    have ht : CacheInvariant k t := save_cacheInvariant hs.cache i z hz
    have hf : t.cache.card = k := by have := ht.card_le; simp only [not_or] at hh; omega
    have hne : (u.cache \ u.marked).Nonempty := phaseStart_candidates_nonempty hk ht hf
    have hzC : z ∉ s.cache := (not_or.mp hh).1
    by_cases hzS : z ∉ u.stale
    · rw [if_pos hzS] at hv
      have he := (PMF.mem_support_pure_iff _ _).mp hv
      subst v
      exact clean_eviction_existing_length k s i z _ hz hc
    · rw [if_neg hzS] at hv
      obtain ⟨_, hu, hzold⟩ := stale_miss_no_reset k s i z hz hzC (not_not.mp hzS)
      have hut : u = t := hu
      rw [hut] at hv
      rw [hut] at hne
      have hcz : s.chainOf x ≠ s.chainOf z := by
        intro he
        exact hxz (hs.representatives.injective hx (Finset.mem_sdiff.mpr ⟨hzold, hzC⟩) he)
      by_cases hr : (t.chainLen t.phase (t.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ)
      · rw [if_pos hr] at hv
        have he := (PMF.mem_support_pure_iff _ _).mp hv
        subst v
        simp [evictInto, staleState, t, savePrediction, hcz]
      · rw [if_neg hr] at hv
        obtain ⟨e, _, rfl⟩ := randomEviction_support (s := staleState t z) hne hv
        simp [evictInto, staleState, t, savePrediction, hcz]
end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh
variable {α : Type*} [DecidableEq α]

lemma step_existing_length_phase_change {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    {s : PMState α} (hs : CacheInvariant k s) (i : ℕ) (z : α) (hz : ℝ)
    {v : PMState α} (hv : v ∈ (step k tb s i z hz).support)
    (hp : v.phase ≠ s.phase) {c : ℕ} (hc : c ≤ s.clean) :
    v.chainLen s.phase c = s.chainLen s.phase c := by
  let t := savePrediction s i z hz
  let u := phaseStart k t
  rw [step_factored] at hv
  change v ∈ (if z ∈ t.cache ∨ t.cache.card < k then PMF.pure (hitOrFill t z)
    else if z ∉ u.stale then PMF.pure (evictInto (cleanState u) z (u.clean + 1) (tb (cleanState u)))
    else if (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ) then
      PMF.pure (evictInto (staleState u z) z (u.chainOf z) (tb (staleState u z)))
    else randomEviction (staleState u z) z (u.chainOf z)).support at hv
  by_cases hh : z ∈ t.cache ∨ t.cache.card < k
  · rw [if_pos hh] at hv
    have he := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    exact (hp rfl).elim
  · rw [if_neg hh] at hv
    have ht : CacheInvariant k t := save_cacheInvariant hs i z hz
    have hf : t.cache.card = k := by have := ht.card_le; simp only [not_or] at hh; omega
    have hne : (u.cache \ u.marked).Nonempty := phaseStart_candidates_nonempty hk ht hf
    have hzC : z ∉ s.cache := (not_or.mp hh).1
    by_cases hzS : z ∉ u.stale
    · rw [if_pos hzS] at hv
      have he := (PMF.mem_support_pure_iff _ _).mp hv
      subst v
      exact clean_eviction_existing_length k s i z _ hz hc
    · rw [if_neg hzS] at hv
      obtain ⟨_, hu, _⟩ := stale_miss_no_reset k s i z hz hzC (not_not.mp hzS)
      have hut : u = t := hu
      rw [hut] at hv hne
      by_cases hr : (t.chainLen t.phase (t.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ)
      · rw [if_pos hr] at hv
        have he := (PMF.mem_support_pure_iff _ _).mp hv
        subst v
        exact (hp rfl).elim
      · rw [if_neg hr] at hv
        obtain ⟨e, _, rfl⟩ := randomEviction_support (s := staleState t z) hne hv
        exact (hp rfl).elim
end CachingML.PredMarker.PMFresh
end


section

open scoped ENNReal

namespace CachingML.PredMarker.PMFresh

lemma pmExpectation_pure {α : Type*} (a : α) (F : α → ℝ≥0∞) :
    pmExpectation (PMF.pure a) F = F a := by
  simp [pmExpectation]

lemma pmExpectation_map {α β : Type*} (p : PMF α) (f : α → β) (F : β → ℝ≥0∞) :
    pmExpectation (p.map f) F = pmExpectation p (fun a => F (f a)) := by
  change pmExpectation (p.bind (fun a => PMF.pure (f a))) F = _
  rw [pmExpectation_bind]
  simp only [pmExpectation_pure]

lemma pmExpectation_add {α : Type*} (p : PMF α) (F G : α → ℝ≥0∞) :
    pmExpectation p (fun a => F a + G a) = pmExpectation p F + pmExpectation p G := by
  unfold pmExpectation
  simp only [mul_add, ENNReal.tsum_add]

lemma pmExpectation_const_add {α : Type*} (p : PMF α) (c : ℝ≥0∞) (F : α → ℝ≥0∞) :
    pmExpectation p (fun a => c + F a) = c + pmExpectation p F := by
  rw [pmExpectation_add, pmExpectation_const]

lemma pmExpectation_add_const {α : Type*} (p : PMF α) (F : α → ℝ≥0∞) (c : ℝ≥0∞) :
    pmExpectation p (fun a => F a + c) = pmExpectation p F + c := by
  rw [pmExpectation_add, pmExpectation_const]

lemma pmExpectation_congr_support {α : Type*} (p : PMF α) {F G : α → ℝ≥0∞}
    (h : ∀ a ∈ p.support, F a = G a) : pmExpectation p F = pmExpectation p G :=
  le_antisymm (pmExpectation_mono p (fun a ha => (h a ha).le))
    (pmExpectation_mono p (fun a ha => (h a ha).ge))

end CachingML.PredMarker.PMFresh
end


section

open scoped ENNReal
namespace CachingML.PredMarker.PMFresh
variable {α : Type*} [DecidableEq α]

lemma tracked_other_step_bound {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) {s : PMState α} (hs : OperationalInvariant k s)
    (i : ℕ) (z : α) (hz : ℝ) {v : PMState α}
    (hv : v ∈ (step k tb s i z hz).support) (p : ℕ × ℕ)
    (hp : s.phase = p.1) {x : α} (hx : x ∈ s.stale \ s.cache)
    (hc : s.chainOf x = p.2) (hxz : x ≠ z) (τ : List α) :
    (v.chainLen p.1 p.2 : ℝ≥0∞) + trackedChainPotential k p v τ ≤
      (s.chainLen p.1 p.2 : ℝ≥0∞) + trackedChainPotential k p s (z :: τ) := by
  have hlen := step_length_other_missing hk tb htb hs i z hz hv hx hxz
  rw [hp, hc] at hlen
  rw [hlen]
  apply add_le_add le_rfl
  rw [trackedChainPotential_eq hs.representatives hp hx hc]
  by_cases hvp : v.phase = s.phase
  · have hvO := step_operationalInvariant hk tb htb hs i z hz hv
    have hxv := step_representative_persists hk tb htb hs.cache i z hz hv hvp hx hxz
    rw [trackedChainPotential_eq hvO.representatives (hvp.trans hp) hxv.1 (hxv.2.trans hc)]
    exact nativeArrivalPotential_other_step hk tb hs.cache i z hz hv hvp τ hxz
  · have hvpn : v.phase ≠ p.1 := fun he => hvp (he.trans hp.symm)
    simp only [trackedChainPotential, if_neg hvpn]
    exact zero_le

lemma tracked_past_step_bound {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    {s : PMState α} (hs : CacheInvariant k s) (i : ℕ) (z : α) (hz : ℝ)
    {v : PMState α} (hv : v ∈ (step k tb s i z hz).support) (p : ℕ × ℕ)
    (hp : p.1 < s.phase) (τ : List α) :
    (v.chainLen p.1 p.2 : ℝ≥0∞) + trackedChainPotential k p v τ ≤
      (s.chainLen p.1 p.2 : ℝ≥0∞) + trackedChainPotential k p s (z :: τ) := by
  have hvp : p.1 < v.phase := hp.trans_le (step_phase_mono hk tb hs i z hz hv)
  rw [trackedChainPotential_past hp, trackedChainPotential_past hvp,
    step_old_phase_length hk tb hs i z hz hv hp]

lemma tracked_phase_change_step_bound {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    {s : PMState α} (hs : OperationalInvariant k s) (i : ℕ) (z : α) (hz : ℝ)
    {v : PMState α} (hv : v ∈ (step k tb s i z hz).support) (p : ℕ × ℕ)
    (hp : s.phase = p.1) (hc : p.2 ≤ s.clean) (hvp : v.phase ≠ s.phase) (τ : List α) :
    (v.chainLen p.1 p.2 : ℝ≥0∞) + trackedChainPotential k p v τ ≤
      (s.chainLen p.1 p.2 : ℝ≥0∞) + trackedChainPotential k p s (z :: τ) := by
  have hlen := step_existing_length_phase_change hk tb hs.cache i z hz hv hvp hc
  rw [hp] at hlen
  rw [hlen]
  have hvpn : v.phase ≠ p.1 := fun he => hvp (he.trans hp.symm)
  simp only [trackedChainPotential, if_neg hvpn, add_zero]
  exact le_add_right le_rfl
end CachingML.PredMarker.PMFresh
end


section

open scoped ENNReal
namespace CachingML.PredMarker.PMFresh
variable {α : Type*} [DecidableEq α]

lemma random_tracked_step_bound {k : ℕ} (_hk : 1 ≤ k) (tb : PMState α → α)
    {s : PMState α} (hs : OperationalInvariant k s) (i : ℕ) (z : α) (hz : ℝ)
    (hx : z ∈ s.stale \ s.cache) (hm : s.marked.card < k)
    (hR : ¬ (s.chainLen s.phase (s.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ))
    (τ : List α) :
    pmExpectation (step k tb s i z hz)
      (fun v => (v.chainLen s.phase (s.chainOf z) : ℝ≥0∞) +
        trackedChainPotential k (s.phase, s.chainOf z) v τ) ≤
      (s.chainLen s.phase (s.chainOf z) : ℝ≥0∞) +
        trackedChainPotential k (s.phase, s.chainOf z) s (z :: τ) := by
  have hzS := (Finset.mem_sdiff.mp hx).1
  have hzC := (Finset.mem_sdiff.mp hx).2
  have hfull : s.cache.card = k := hs.phaseCache.stale_full ⟨z, hzS⟩
  have hne : (s.cache \ s.marked).Nonempty := by
    apply Finset.sdiff_nonempty.mpr
    intro hsub
    have hcard := Finset.card_le_card hsub
    omega
  let t := savePrediction s i z hz
  let b := { staleState t z with randomChains := insert (s.phase, s.chainOf z) s.randomChains }
  let out := fun e => evictInto b z (s.chainOf z) e
  have hstep : step k tb s i z hz = (PMF.uniformOfFinset (s.cache \ s.marked) hne).map out := by
    rw [step_factored]
    change (if z ∈ t.cache ∨ t.cache.card < k then PMF.pure (hitOrFill t z)
      else let u := phaseStart k t
        if z ∉ u.stale then PMF.pure (evictInto (cleanState u) z (u.clean+1) (tb (cleanState u)))
        else if (u.chainLen u.phase (u.chainOf z)+1 : ℕ) ≤ (harmonic k : ℝ) then
          PMF.pure (evictInto (staleState u z) z (u.chainOf z) (tb (staleState u z)))
        else randomEviction (staleState u z) z (u.chainOf z)) = _
    have hnot : ¬ (z ∈ t.cache ∨ t.cache.card < k) := by
      change ¬ (z ∈ s.cache ∨ s.cache.card < k)
      simp [hzC, hfull]
    rw [if_neg hnot]
    have hu : phaseStart k t = t := by
      have hnm : s.marked.card ≠ k := by omega
      simp [phaseStart, t, savePrediction, hnm]
    dsimp only
    rw [hu]
    have hzSt : z ∈ t.stale := hzS
    have hRt : ¬ (t.chainLen t.phase (t.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ) := hR
    rw [if_neg (not_not_intro hzSt), if_neg hRt]
    unfold randomEviction
    have hnet : ((staleState t z).cache \ (staleState t z).marked).Nonempty := hne
    rw [dif_pos hnet]
    rfl
  rw [hstep, pmExpectation_map]
  let law := PMF.uniformOfFinset (s.cache \ s.marked) hne
  have heq : pmExpectation law
      (fun e => ((out e).chainLen s.phase (s.chainOf z) : ℝ≥0∞) +
        trackedChainPotential k (s.phase, s.chainOf z) (out e) τ) =
      pmExpectation law (fun e => ((s.chainLen s.phase (s.chainOf z) + 1 : ℕ) : ℝ≥0∞) +
        nativeArrivalPotential k (evictInto s z (s.chainOf z) e) τ e) := by
    apply pmExpectation_congr_support
    intro e he
    have heU : e ∈ s.cache \ s.marked := by simpa [law] using he
    have heC := (Finset.mem_sdiff.mp heU).1
    have heS := hs.phaseCache.unmarked_stale heU
    have hez : e ≠ z := ne_of_mem_of_not_mem heC hzC
    have hrep : NativeRepresentatives (out e) :=
      stale_eviction_nativeRepresentatives hs.phaseCache hs.representatives hzS hzC heU
    have hem : e ∈ (out e).stale \ (out e).cache := by
      change e ∈ s.stale \ insert z (s.cache.erase e)
      simp [heS, hez]
    have hec : (out e).chainOf e = s.chainOf z := by
      change Function.update s.chainOf e (s.chainOf z) e = _
      exact Function.update_self _ _ _
    rw [trackedChainPotential_eq hrep rfl hem hec]
    have hlen : (out e).chainLen s.phase (s.chainOf z) = s.chainLen s.phase (s.chainOf z) + 1 := by
      simp [out, b, t, evictInto, staleState, savePrediction]
    rw [hlen]
    rfl
  change pmExpectation law _ ≤ _
  rw [heq, pmExpectation_const_add]
  rw [trackedChainPotential_eq hs.representatives rfl hx rfl]
  simp only [Nat.cast_add, Nat.cast_one, add_assoc]
  exact add_le_add le_rfl (uniform_nativeArrivalPotential k s τ hzC hfull hm hs.cache.marked_subset hne (s.chainOf z))
end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh
variable {α : Type*} [DecidableEq α]

structure TrackedInvariant (k : ℕ) (p : ℕ × ℕ) (s : PMState α) : Prop where
  operational : OperationalInvariant k s
  phase_le : p.1 ≤ s.phase
  positive : 0 < s.chainLen p.1 p.2
  threshold : ¬ (s.chainLen p.1 p.2 + 1 : ℕ) ≤ (harmonic k : ℝ)

lemma trackedInvariant_step {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) {p : ℕ × ℕ} {s : PMState α}
    (hs : TrackedInvariant k p s) (i : ℕ) (z : α) (hz : ℝ)
    {v : PMState α} (hv : v ∈ (step k tb s i z hz).support) : TrackedInvariant k p v := by
  have hlen := step_chainLen_mono hk tb htb hs.operational i z hz hv p
  refine ⟨step_operationalInvariant hk tb htb hs.operational i z hz hv,
    hs.phase_le.trans (step_phase_mono hk tb hs.operational.cache i z hz hv),
    hs.positive.trans_le hlen, ?_⟩
  intro hR
  apply hs.threshold
  have hle : (s.chainLen p.1 p.2 + 1 : ℕ) ≤ (v.chainLen p.1 p.2 + 1 : ℝ) := by
    exact_mod_cast Nat.add_le_add_right hlen 1
  apply hle.trans
  simpa only [Nat.cast_add, Nat.cast_one] using hR

lemma trackedInvariant_representative {k : ℕ} {p : ℕ × ℕ} {s : PMState α}
    (hs : TrackedInvariant k p s) (hp : s.phase = p.1) :
    ∃ x ∈ s.stale \ s.cache, s.chainOf x = p.2 := by
  have hpos : 0 < s.chainLen s.phase p.2 := by rw [hp]; exact hs.positive
  have hcl : 1 ≤ p.2 ∧ p.2 ≤ s.clean := by
    by_contra hh
    have hbad : s.clean < p.2 ∨ p.2 = 0 := by omega
    have hempty := hs.operational.bookkeeping.current_empty p.2 hbad
    have hlen := hs.operational.bookkeeping.lengths (s.phase, p.2)
    change s.chainLen s.phase p.2 = (indexFamily s (s.phase, p.2)).length at hlen
    rw [hempty] at hlen
    simp only [List.length_nil] at hlen
    omega
  exact hs.operational.representatives.surjective p.2 hcl.1 hcl.2
end CachingML.PredMarker.PMFresh
end


section

open scoped ENNReal
namespace CachingML.PredMarker.PMFresh
variable {α : Type*} [DecidableEq α]

lemma tracked_step_expectation_bound {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) {p : ℕ × ℕ} {s : PMState α}
    (hs : TrackedInvariant k p s) (i : ℕ) (z : α) (hz : ℝ) (τ : List α) :
    pmExpectation (step k tb s i z hz)
      (fun v => (v.chainLen p.1 p.2 : ℝ≥0∞) + trackedChainPotential k p v τ) ≤
      (s.chainLen p.1 p.2 : ℝ≥0∞) + trackedChainPotential k p s (z :: τ) := by
  by_cases hp : s.phase = p.1
  · obtain ⟨x, hx, hc⟩ := trackedInvariant_representative hs hp
    by_cases hxz : x = z
    · subst x
      by_cases hm : s.marked.card = k
      · apply (pmExpectation_mono _ (fun v hv => ?_)).trans_eq (pmExpectation_const _ _)
        have hπ := congrArg PhaseState.number
          (step_nativePhase hk tb hs.operational.cache i z hz hv)
        have hzM : z ∉ s.marked := fun hzM =>
          (Finset.mem_sdiff.mp hx).2 (hs.operational.cache.marked_subset hzM)
        have hvp : v.phase = s.phase + 1 := by
          change v.phase = (phaseStep k (nativePhase s) z).number at hπ
          simpa [phaseStep, nativePhase, hzM, hm] using hπ
        exact tracked_phase_change_step_bound hk tb hs.operational i z hz hv p hp
          (by rw [← hc]; exact (hs.operational.representatives.bounds z hx).2)
          (by omega) τ
      · have hmlt : s.marked.card < k := lt_of_le_of_ne
          ((Finset.card_le_card hs.operational.cache.marked_subset).trans hs.operational.cache.card_le) hm
        have hR : ¬ (s.chainLen s.phase (s.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ) := by
          rw [hp, hc]
          exact hs.threshold
        have hh := random_tracked_step_bound hk tb hs.operational i z hz hx hmlt hR τ
        simpa only [hp, hc] using hh
    · apply (pmExpectation_mono _ (fun v hv => ?_)).trans_eq (pmExpectation_const _ _)
      exact tracked_other_step_bound hk tb htb hs.operational i z hz hv p hp hx hc hxz τ
  · have hlt : p.1 < s.phase := by have := hs.phase_le; omega
    apply (pmExpectation_mono _ (fun v hv => ?_)).trans_eq (pmExpectation_const _ _)
    exact tracked_past_step_bound hk tb hs.operational.cache i z hz hv p hlt τ
end CachingML.PredMarker.PMFresh
end


section

open scoped ENNReal
namespace CachingML.PredMarker.PMFresh
variable {α : Type*} [DecidableEq α]

lemma nativeArrivalPotential_le_harmonic {k : ℕ} {s : PMState α}
    (hs : OperationalInvariant k s) {x : α} (hx : x ∈ s.stale \ s.cache) (τ : List α) :
    nativeArrivalPotential k s τ x ≤ ENNReal.ofReal (harmonic k : ℝ) := by
  let F := phaseFuture k s.marked τ
  have hM : s.marked.card ≤ k := (Finset.card_le_card hs.cache.marked_subset).trans hs.cache.card_le
  have hF : F.card ≤ k := phaseFuture_card_le k s.marked hM τ
  by_cases hxF : x ∈ F
  · have hC := hs.phaseCache.stale_full ⟨x, (Finset.mem_sdiff.mp hx).1⟩
    have hcard := finite_future_candidates_card s.cache s.marked F hC hF
      (subset_phaseFuture k _ _) hxF (Finset.mem_sdiff.mp hx).2
    have hU : (s.cache \ s.marked).card ≤ k :=
      (Finset.card_le_card Finset.sdiff_subset).trans hs.cache.card_le
    apply (missingRepresentativePotential_current_bound F ((s.cache \ s.marked) ∩ F) τ.idxOf x).trans
    apply ENNReal.ofReal_le_ofReal
    apply harmonic_real_monotone
    omega
  · change missingRepresentativePotential F ((s.cache \ s.marked) ∩ F) τ.idxOf x ≤
      ENNReal.ofReal (harmonic k : ℝ)
    rw [missingRepresentativePotential, if_neg hxF]
    exact zero_le

lemma trackedChainPotential_le_harmonic {k : ℕ} {p : ℕ × ℕ} {s : PMState α}
    (hs : TrackedInvariant k p s) (τ : List α) :
    trackedChainPotential k p s τ ≤ ENNReal.ofReal (harmonic k : ℝ) := by
  by_cases hp : s.phase = p.1
  · obtain ⟨x, hx, hc⟩ := trackedInvariant_representative hs hp
    rw [trackedChainPotential_eq hs.operational.representatives hp hx hc]
    exact nativeArrivalPotential_le_harmonic hs.operational hx τ
  · simp only [trackedChainPotential, if_neg hp]
    exact zero_le
end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh
variable {α : Type*} [DecidableEq α]

def remainingRequests (σ : List α) (l : List ℕ) : List α :=
  l.filterMap (fun i => σ[i]?)

omit [DecidableEq α] in
lemma remainingRequests_cons_valid (σ : List α) (i : ℕ) (hi : i < σ.length) (l : List ℕ) :
    remainingRequests σ (i :: l) = σ.get ⟨i, hi⟩ :: remainingRequests σ l := by
  simp [remainingRequests, List.getElem?_eq_getElem hi]

omit [DecidableEq α] in
lemma remainingRequests_cons_invalid (σ : List α) (i : ℕ) (hi : ¬i < σ.length) (l : List ℕ) :
    remainingRequests σ (i :: l) = remainingRequests σ l := by
  have he : σ[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
  simp [remainingRequests, he]
end CachingML.PredMarker.PMFresh
end


section

open scoped ENNReal

namespace CachingML.PredMarker.PMFresh

lemma kernelRun_potential_bound {α β : Type*} (f : α → β → PMF α)
    (P : α → List β → Prop) (V : α → List β → ℝ≥0∞) (F : α → ℝ≥0∞)
    (hpreserve : ∀ s b l, P s (b :: l) → ∀ t ∈ (f s b).support, P t l)
    (hstep : ∀ s b l, P s (b :: l) → pmExpectation (f s b) (fun t => V t l) ≤ V s (b :: l))
    (hterminal : ∀ s, P s [] → F s ≤ V s [])
    (l : List β) (s : α) (hs : P s l) :
    pmExpectation (kernelRun f s l) F ≤ V s l := by
  induction l generalizing s with
  | nil => simpa [kernelRun, pmExpectation] using hterminal s hs
  | cons b l ih =>
    change pmExpectation ((f s b).bind (fun t => kernelRun f t l)) F ≤ _
    rw [pmExpectation_bind]
    apply (pmExpectation_mono _ (fun t ht => ih t (hpreserve s b l hs t ht))).trans
    exact hstep s b l hs

lemma kernelRun_additive_potential_bound {α β : Type*} (f : α → β → PMF α)
    (P : α → List β → Prop) (cost : α → ℝ≥0∞) (V : α → List β → ℝ≥0∞)
    (hpreserve : ∀ s b l, P s (b :: l) → ∀ t ∈ (f s b).support, P t l)
    (hstep : ∀ s b l, P s (b :: l) →
      pmExpectation (f s b) (fun t => cost t + V t l) ≤ cost s + V s (b :: l))
    (l : List β) (s : α) (hs : P s l) :
    pmExpectation (kernelRun f s l) cost ≤ cost s + V s l := by
  exact kernelRun_potential_bound f P (fun t r => cost t + V t r) cost hpreserve hstep
    (fun t _ => le_add_right le_rfl) l s hs

end CachingML.PredMarker.PMFresh
end


section

open scoped ENNReal
namespace CachingML.PredMarker.PMFresh
variable {α : Type*} [DecidableEq α]

lemma tracked_indexed_continuation {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    (l : List ℕ) {p : ℕ × ℕ} {s : PMState α} (hs : TrackedInvariant k p s) :
    pmExpectation (kernelRun (fun t i => indexedStep k tb σ h i t) s l)
      (fun v => (v.chainLen p.1 p.2 : ℝ≥0∞)) ≤
      (s.chainLen p.1 p.2 : ℝ≥0∞) + trackedChainPotential k p s (remainingRequests σ l) := by
  apply kernelRun_additive_potential_bound
    (fun t i => indexedStep k tb σ h i t) (fun t _ => TrackedInvariant k p t)
    (fun v => (v.chainLen p.1 p.2 : ℝ≥0∞))
    (fun t r => trackedChainPotential k p t (remainingRequests σ r)) _ _ l s hs
  · intro t i r ht v hv
    unfold indexedStep at hv
    split_ifs at hv with hi
    · exact trackedInvariant_step hk tb htb ht i _ _ hv
    · have he := (PMF.mem_support_pure_iff _ _).mp hv
      subst v
      exact ht
  · intro t i r ht
    unfold indexedStep
    split_ifs with hi
    · rw [remainingRequests_cons_valid σ i hi r]
      exact tracked_step_expectation_bound hk tb htb ht i _ _ (remainingRequests σ r)
    · rw [remainingRequests_cons_invalid σ i hi r, pmExpectation_pure]

lemma native_harmonic_continuation {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    (l : List ℕ) {p : ℕ × ℕ} {s : PMState α} (hs : TrackedInvariant k p s) :
    pmExpectation (kernelRun (fun t i => indexedStep k tb σ h i t) s l)
      (fun v => (v.chainLen p.1 p.2 : ℝ≥0∞)) ≤
      ENNReal.ofReal ((s.chainLen p.1 p.2 : ℝ) + (harmonic k : ℝ)) := by
  apply (tracked_indexed_continuation hk tb htb σ h l hs).trans
  rw [ENNReal.ofReal_add (by positivity) (harmonic_real_nonneg k), ENNReal.ofReal_natCast]
  exact add_le_add le_rfl (trackedChainPotential_le_harmonic hs _)
end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

noncomputable def nativeRandomKey (k : ℕ) (s : PMState α) (i : ℕ) (z : α) (hz : ℝ) :
    Option (ℕ × ℕ) :=
  let t := savePrediction s i z hz
  if z ∈ t.cache ∨ t.cache.card < k then none
  else
    let u := phaseStart k t
    if z ∉ u.stale then none
    else if (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ) then none
    else some (u.phase, u.chainOf z)

lemma step_randomChains_exact {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    {s : PMState α} (hs : CacheInvariant k s) (i : ℕ) (z : α) (hz : ℝ)
    {v : PMState α} (hv : v ∈ (step k tb s i z hz).support) :
    v.randomChains = match nativeRandomKey k s i z hz with
      | none => s.randomChains
      | some p => insert p s.randomChains := by
  rw [step_factored] at hv
  dsimp only at hv
  unfold nativeRandomKey
  dsimp only
  let t := savePrediction s i z hz
  have ht : CacheInvariant k t := save_cacheInvariant hs i z hz
  by_cases hh : z ∈ t.cache ∨ t.cache.card < k
  · rw [if_pos hh] at hv ⊢
    have he := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    rfl
  · rw [if_neg hh] at hv ⊢
    have hf : t.cache.card = k := by have := ht.card_le; simp only [not_or] at hh; omega
    let u := phaseStart k t
    have hne : (u.cache \ u.marked).Nonempty := phaseStart_candidates_nonempty hk ht hf
    have hflags : u.randomChains = s.randomChains := by
      dsimp [u, phaseStart]
      split_ifs <;> rfl
    by_cases hc : z ∉ u.stale
    · rw [if_pos hc] at hv ⊢
      have he := (PMF.mem_support_pure_iff _ _).mp hv
      subst v
      exact hflags
    · rw [if_neg hc] at hv ⊢
      by_cases hr : (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ)
      · rw [if_pos hr] at hv ⊢
        have he := (PMF.mem_support_pure_iff _ _).mp hv
        subst v
        exact hflags
      · rw [if_neg hr] at hv ⊢
        obtain ⟨e, _, rfl⟩ := randomEviction_support (s := staleState u z) hne hv
        change insert (u.phase, u.chainOf z) u.randomChains = insert (u.phase, u.chainOf z) s.randomChains
        rw [hflags]

lemma nativeRandomKey_some {k : ℕ} {s : PMState α} {i : ℕ} {z : α} {hz : ℝ}
    {p : ℕ × ℕ} (hp : nativeRandomKey k s i z hz = some p) :
    z ∉ s.cache ∧ ¬ s.cache.card < k ∧ z ∈ s.stale ∧
      p = (s.phase, s.chainOf z) ∧
      ¬ (s.chainLen p.1 p.2 + 1 : ℕ) ≤ (harmonic k : ℝ) := by
  unfold nativeRandomKey at hp
  dsimp only at hp
  split_ifs at hp with hh hc hr
  have hzC : z ∉ s.cache := (not_or.mp hh).1
  have hzS : z ∈ (phaseStart k (savePrediction s i z hz)).stale := hc
  obtain ⟨_, hreset, hzold⟩ := stale_miss_no_reset k s i z hz hzC hzS
  rw [hreset] at hp hr
  have hpeq : p = (s.phase, s.chainOf z) := (Option.some.inj hp).symm
  refine ⟨hzC, (not_or.mp hh).2, hzold, hpeq, ?_⟩
  rw [hpeq]
  exact hr

lemma step_nonrandom_of_not_switch {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    {s : PMState α} (hs : CacheInvariant k s) (i : ℕ) (z : α) (hz : ℝ)
    {v : PMState α} (hv : v ∈ (step k tb s i z hz).support)
    (p : ℕ × ℕ) (hp : p ∉ s.randomChains)
    (hstop : nativeRandomKey k s i z hz ≠ some p) : p ∉ v.randomChains := by
  rw [step_randomChains_exact hk tb hs i z hz hv]
  cases he : nativeRandomKey k s i z hz with
  | none => exact hp
  | some q =>
    intro hm
    rcases hm with heq | hm
    · exact hstop (he.trans (congrArg some heq.symm))
    · exact hp hm

end CachingML.PredMarker.PMFresh
end


section

open scoped ENNReal
namespace CachingML.PredMarker.PMFresh
variable {α : Type*} [DecidableEq α]

lemma actual_first_switch_suffix_bound {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    (n : ℕ) (hn : n < σ.length) {s : PMState α}
    (hs : s ∈ (prefixRun k tb σ h n).support) (p : ℕ × ℕ)
    (hkey : nativeRandomKey k s n (σ.get ⟨n, hn⟩) (h ⟨n, hn⟩) = some p) :
    pmExpectation (kernelRun (fun t i => indexedStep k tb σ h i t) s
      ((List.range σ.length).drop n)) (fun v => (v.chainLen p.1 p.2 : ℝ≥0∞)) ≤
      ENNReal.ofReal ((s.chainLen p.1 p.2 : ℝ) + (harmonic k : ℝ)) := by
  obtain ⟨_, _, _, hpeq, hR⟩ := nativeRandomKey_some hkey
  have hpos : 0 < s.chainLen p.1 p.2 := by
    by_contra hh
    have he : s.chainLen p.1 p.2 = 0 := by omega
    apply hR
    simp only [he, zero_add, Nat.cast_one]
    exact harmonic_real_one_le hk
  have hp : p.1 ≤ s.phase := by rw [hpeq]
  exact native_harmonic_continuation hk tb htb σ h _
    ⟨prefixRun_operationalInvariant hk tb htb σ h n hs, hp, hpos, hR⟩
end CachingML.PredMarker.PMFresh
end


section

open scoped ENNReal

namespace CachingML.PredMarker.PMFresh

noncomputable def firstHitRun {α β : Type*} (f : α → β → PMF α)
    (stop : α → List β → Bool) (s : α) : List β → PMF (α × List β)
  | [] => PMF.pure (s, [])
  | b :: l => if stop s (b :: l) then PMF.pure (s, b :: l)
      else (f s b).bind (fun t => firstHitRun f stop t l)

lemma firstHitRun_restart {α β : Type*} (f : α → β → PMF α)
    (stop : α → List β → Bool) (l : List β) (s : α) :
    (firstHitRun f stop s l).bind (fun p => kernelRun f p.1 p.2) = kernelRun f s l := by
  induction l generalizing s with
  | nil => simp [firstHitRun, kernelRun]
  | cons b l ih =>
    simp only [firstHitRun]
    split_ifs
    · simp
    · rw [PMF.bind_bind]
      change (f s b).bind _ = (f s b).bind _
      congr 1
      funext t
      exact ih t

lemma firstHitRun_stopped {α β : Type*} (f : α → β → PMF α)
    (stop : α → List β → Bool) (l : List β) (s : α)
    {p : α × List β} (hp : p ∈ (firstHitRun f stop s l).support) :
    p.2 = [] ∨ stop p.1 p.2 = true := by
  induction l generalizing s p with
  | nil =>
    have he := (PMF.mem_support_pure_iff _ _).mp hp
    subst p
    exact Or.inl rfl
  | cons b l ih =>
    simp only [firstHitRun] at hp
    split_ifs at hp with hstop
    · have he := (PMF.mem_support_pure_iff _ _).mp hp
      subst p
      exact Or.inr hstop
    · obtain ⟨t, _, hp⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
      exact ih t hp

lemma firstHitRun_reachable {α β : Type*} (f : α → β → PMF α)
    (stop : α → List β → Bool) (l : List β) (s : α)
    {p : α × List β} (hp : p ∈ (firstHitRun f stop s l).support) :
    ∃ pre : List β, l = pre ++ p.2 ∧ p.1 ∈ (kernelRun f s pre).support := by
  induction l generalizing s p with
  | nil =>
    have he := (PMF.mem_support_pure_iff _ _).mp hp
    subst p
    exact ⟨[], rfl, by simp [kernelRun]⟩
  | cons b l ih =>
    simp only [firstHitRun] at hp
    split_ifs at hp with hstop
    · have he := (PMF.mem_support_pure_iff _ _).mp hp
      subst p
      exact ⟨[], rfl, by simp [kernelRun]⟩
    · obtain ⟨t, ht, hp⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
      obtain ⟨pre, heq, hr⟩ := ih t hp
      refine ⟨b :: pre, ?_, ?_⟩
      · simp only [List.cons_append, heq]
      · exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨t, ht, hr⟩

lemma firstHitRun_finite_support {α β : Type*} (f : α → β → PMF α)
    (hf : ∀ s b, (f s b).support.Finite) (stop : α → List β → Bool)
    (l : List β) (s : α) : (firstHitRun f stop s l).support.Finite := by
  induction l generalizing s with
  | nil => simp [firstHitRun]
  | cons b l ih =>
    simp only [firstHitRun]
    split_ifs
    · simp
    · exact finite_support_bind _ _ (hf s b) (fun t _ => ih t)

lemma firstHitRun_expectation_compare {α β : Type*} (f : α → β → PMF α)
    (stop : α → List β → Bool) (l : List β) (s : α) (F G : α → ℝ≥0∞)
    (h : ∀ p ∈ (firstHitRun f stop s l).support,
      pmExpectation (kernelRun f p.1 p.2) F ≤ pmExpectation (kernelRun f p.1 p.2) G) :
    pmExpectation (kernelRun f s l) F ≤ pmExpectation (kernelRun f s l) G := by
  rw [← firstHitRun_restart f stop l s]
  rw [pmExpectation_bind, pmExpectation_bind]
  exact pmExpectation_mono _ h

end CachingML.PredMarker.PMFresh
end


section

open scoped ENNReal

namespace CachingML.PredMarker.PMFresh

lemma firstHitRun_invariant {α β : Type*} (f : α → β → PMF α)
    (stop : α → List β → Bool) (P : α → List β → Prop)
    (hstep : ∀ s b l, P s (b :: l) → stop s (b :: l) = false →
      ∀ t ∈ (f s b).support, P t l)
    (l : List β) (s : α) (hs : P s l)
    {p : α × List β} (hp : p ∈ (firstHitRun f stop s l).support) : P p.1 p.2 := by
  induction l generalizing s p with
  | nil =>
    have he := (PMF.mem_support_pure_iff _ _).mp hp
    subst p
    exact hs
  | cons b l ih =>
    simp only [firstHitRun] at hp
    split_ifs at hp with hstop
    · have he := (PMF.mem_support_pure_iff _ _).mp hp
      subst p
      exact hs
    · obtain ⟨t, ht, hp⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
      exact ih t (hstep s b l hs (Bool.eq_false_iff.mpr hstop) t ht) hp

lemma firstHitRun_comparison_cases {α β : Type*} (f : α → β → PMF α)
    (stop : α → List β → Bool) (P : α → List β → Prop)
    (hstep : ∀ s b l, P s (b :: l) → stop s (b :: l) = false →
      ∀ t ∈ (f s b).support, P t l)
    (l : List β) (s : α) (hs : P s l) (F G : α → ℝ≥0∞)
    (hterminal : ∀ t, P t [] → F t ≤ G t)
    (hstopped : ∀ t b r, P t (b :: r) → stop t (b :: r) = true →
      pmExpectation (kernelRun f t (b :: r)) F ≤ pmExpectation (kernelRun f t (b :: r)) G) :
    pmExpectation (kernelRun f s l) F ≤ pmExpectation (kernelRun f s l) G := by
  apply firstHitRun_expectation_compare f stop l s F G
  intro p hp
  have hP := firstHitRun_invariant f stop P hstep l s hs hp
  have hstop := firstHitRun_stopped f stop l s hp
  rcases p with ⟨t, r⟩
  cases r with
  | nil =>
    simpa [kernelRun, pmExpectation] using hterminal t hP
  | cons b r =>
    exact hstopped t b r hP (hstop.resolve_left (by simp))

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

noncomputable def nativeSwitchStop (k : ℕ) (σ : List α) (h : Fin σ.length → ℝ)
    (p : ℕ × ℕ) (s : PMState α) : List ℕ → Bool
  | [] => false
  | i :: _ => if hi : i < σ.length then
      decide (nativeRandomKey k s i (σ.get ⟨i, hi⟩) (h ⟨i, hi⟩) = some p)
    else false

lemma nativeSwitchStop_true {k : ℕ} {σ : List α} {h : Fin σ.length → ℝ}
    {p : ℕ × ℕ} {s : PMState α} {i : ℕ} {l : List ℕ}
    (hs : nativeSwitchStop k σ h p s (i :: l) = true) :
    ∃ hi : i < σ.length,
      nativeRandomKey k s i (σ.get ⟨i, hi⟩) (h ⟨i, hi⟩) = some p := by
  unfold nativeSwitchStop at hs
  dsimp only at hs
  split_ifs at hs with hi
  exact ⟨hi, of_decide_eq_true hs⟩

lemma nativeSwitchStop_nonrandom_step {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    (p : ℕ × ℕ) {s : PMState α} (hs : CacheInvariant k s) (hp : p ∉ s.randomChains)
    (i : ℕ) (l : List ℕ) (hstop : nativeSwitchStop k σ h p s (i :: l) = false)
    {v : PMState α} (hv : v ∈ (indexedStep k tb σ h i s).support) :
    CacheInvariant k v ∧ p ∉ v.randomChains := by
  unfold indexedStep at hv
  split_ifs at hv with hi
  · have hn : nativeRandomKey k s i (σ.get ⟨i, hi⟩) (h ⟨i, hi⟩) ≠ some p := by
      simpa [nativeSwitchStop, hi] using hstop
    exact ⟨step_cacheInvariant hk tb htb hs i _ _ hv,
      step_nonrandom_of_not_switch hk tb hs i _ _ hv p hp hn⟩
  · have he := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    exact ⟨hs, hp⟩

lemma native_firstSwitch_support {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ) (p : ℕ × ℕ)
    (l : List ℕ) {s : PMState α} (hs : CacheInvariant k s) (hp : p ∉ s.randomChains)
    {q : PMState α × List ℕ}
    (hq : q ∈ (firstHitRun (fun t i => indexedStep k tb σ h i t)
      (nativeSwitchStop k σ h p) s l).support) :
    CacheInvariant k q.1 ∧ p ∉ q.1.randomChains ∧
      (q.2 = [] ∨ ∃ i r, q.2 = i :: r ∧ ∃ hi : i < σ.length,
        nativeRandomKey k q.1 i (σ.get ⟨i, hi⟩) (h ⟨i, hi⟩) = some p) := by
  have hpres := firstHitRun_invariant (fun t i => indexedStep k tb σ h i t)
    (nativeSwitchStop k σ h p) (fun t _ => CacheInvariant k t ∧ p ∉ t.randomChains)
    (fun t i r ht hstop v hv => nativeSwitchStop_nonrandom_step hk tb htb σ h p
      ht.1 ht.2 i r hstop hv) l s ⟨hs, hp⟩ hq
  refine ⟨hpres.1, hpres.2, ?_⟩
  have hstop := firstHitRun_stopped (fun t i => indexedStep k tb σ h i t)
    (nativeSwitchStop k σ h p) l s hq
  rcases hstop with he | he
  · exact Or.inl he
  · cases hr : q.2 with
    | nil => exact Or.inl rfl
    | cons i r =>
      rw [hr] at he
      exact Or.inr ⟨i, r, rfl, nativeSwitchStop_true he⟩

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

lemma kernelRun_range_prefixRun (k : ℕ) (tb : PMState α → α) (σ : List α)
    (h : Fin σ.length → ℝ) (n : ℕ) :
    kernelRun (fun t i => indexedStep k tb σ h i t) (initState α) (List.range n) =
      prefixRun k tb σ h n := by
  rw [prefixRun_fold, kernelRun_fold]
  simp

lemma range_prefix_exact {N : ℕ} {pre rest : List ℕ} (he : List.range N = pre ++ rest) :
    pre.length ≤ N ∧ pre = List.range pre.length ∧ rest = (List.range N).drop pre.length := by
  have hlen := congrArg List.length he
  simp only [List.length_range, List.length_append] at hlen
  have hn : pre.length ≤ N := by omega
  have ht := congrArg (List.take pre.length) he
  simp only [List.take_range, Nat.min_eq_left hn, List.take_left] at ht
  have hd := congrArg (List.drop pre.length) he
  simp only [List.drop_left] at hd
  exact ⟨hn, ht.symm, hd.symm⟩

lemma firstHitRun_actual_prefix (k : ℕ) (tb : PMState α → α) (σ : List α)
    (h : Fin σ.length → ℝ) (stop : PMState α → List ℕ → Bool)
    {q : PMState α × List ℕ}
    (hq : q ∈ (firstHitRun (fun t i => indexedStep k tb σ h i t) stop
      (initState α) (List.range σ.length)).support) :
    ∃ n ≤ σ.length, q.1 ∈ (prefixRun k tb σ h n).support ∧
      q.2 = (List.range σ.length).drop n := by
  obtain ⟨pre, he, hr⟩ := firstHitRun_reachable (fun t i => indexedStep k tb σ h i t)
    stop (List.range σ.length) (initState α) hq
  obtain ⟨hn, hpre, hrest⟩ := range_prefix_exact he
  refine ⟨pre.length, hn, ?_, hrest⟩
  rw [hpre, kernelRun_range_prefixRun] at hr
  exact hr

lemma range_drop_head {N n i : ℕ} {r : List ℕ}
    (he : (List.range N).drop n = i :: r) : n < N ∧ i = n := by
  have hlen := congrArg List.length he
  simp only [List.length_drop, List.length_range, List.length_cons] at hlen
  have hn : n < N := by omega
  have hh := congrArg List.head? he
  simp [List.head?_drop, hn] at hh
  exact ⟨hn, hh.symm⟩

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

def NonrandomLengthCap (k : ℕ) (s : PMState α) : Prop :=
  ∀ p, p ∉ s.randomChains → (lengthFamily s p : ℝ) ≤ (harmonic k : ℝ)

omit [DecidableEq α] in
lemma init_nonrandomLengthCap (k : ℕ) : NonrandomLengthCap k (initState α) := by
  intro p _
  simpa [lengthFamily, initState] using harmonic_real_nonneg k

omit [DecidableEq α] in
lemma phaseStart_nonrandomLengthCap (k : ℕ) {s : PMState α}
    (hs : NonrandomLengthCap k s) : NonrandomLengthCap k (phaseStart k s) := by
  unfold phaseStart
  split_ifs <;> exact hs

lemma clean_eviction_lengthCap {k : ℕ} (hk : 1 ≤ k) {s : PMState α}
    (hs : NonrandomLengthCap k s) (z e : α) :
    NonrandomLengthCap k (evictInto (cleanState s) z (s.clean + 1) e) := by
  intro p hp
  rw [clean_lengthFamily]
  by_cases heq : p = (s.phase, s.clean + 1)
  · subst p
    rw [Function.update_self]
    simpa only [Nat.cast_one] using harmonic_real_one_le hk
  · rw [Function.update_of_ne heq]
    exact hs p hp

lemma stale_eviction_lengthCap {k : ℕ} {s : PMState α}
    (hs : NonrandomLengthCap k s) (z e : α)
    (hr : (s.chainLen s.phase (s.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ)) :
    NonrandomLengthCap k (evictInto (staleState s z) z (s.chainOf z) e) := by
  intro p hp
  rw [stale_lengthFamily]
  by_cases heq : p = (s.phase, s.chainOf z)
  · subst p
    rw [Function.update_self]
    exact hr
  · rw [Function.update_of_ne heq]
    exact hs p hp

lemma random_eviction_lengthCap {k : ℕ} {s : PMState α}
    (hs : NonrandomLengthCap k s) (z e : α) :
    NonrandomLengthCap k
      (evictInto { staleState s z with randomChains := insert (s.phase, s.chainOf z) s.randomChains }
        z (s.chainOf z) e) := by
  intro p hp
  change p ∉ insert (s.phase, s.chainOf z) s.randomChains at hp
  have hne : p ≠ (s.phase, s.chainOf z) := fun he => hp (Or.inl he)
  change (lengthFamily (evictInto (staleState
    { s with randomChains := insert (s.phase, s.chainOf z) s.randomChains } z)
      z (s.chainOf z) e) p : ℝ) ≤ _
  rw [stale_lengthFamily, Function.update_of_ne hne]
  exact hs p (fun he => hp (Or.inr he))

lemma step_nonrandomLengthCap {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (_htb : IsMaxTieBreak tb) {s : PMState α} (hs : CacheInvariant k s)
    (hcap : NonrandomLengthCap k s) (i : ℕ) (z : α) (hz : ℝ) {v : PMState α}
    (hv : v ∈ (step k tb s i z hz).support) : NonrandomLengthCap k v := by
  rw [step_factored] at hv
  dsimp only at hv
  let t := savePrediction s i z hz
  have ht : CacheInvariant k t := save_cacheInvariant hs i z hz
  by_cases hh : z ∈ t.cache ∨ t.cache.card < k
  · simp only [show z ∈ (savePrediction s i z hz).cache ∨
      (savePrediction s i z hz).cache.card < k from hh, if_pos] at hv
    have he := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    exact hcap
  · simp only [show ¬ (z ∈ (savePrediction s i z hz).cache ∨
      (savePrediction s i z hz).cache.card < k) from hh, if_false] at hv
    have hf : t.cache.card = k := by have := ht.card_le; simp only [not_or] at hh; omega
    let u := phaseStart k t
    have hne : (u.cache \ u.marked).Nonempty := phaseStart_candidates_nonempty hk ht hf
    have hu : NonrandomLengthCap k u := phaseStart_nonrandomLengthCap k hcap
    by_cases hc : z ∉ u.stale
    · rw [if_pos hc] at hv
      have he := (PMF.mem_support_pure_iff _ _).mp hv
      subst v
      exact clean_eviction_lengthCap hk hu z _
    · rw [if_neg hc] at hv
      by_cases hr : (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ)
      · rw [if_pos hr] at hv
        have he := (PMF.mem_support_pure_iff _ _).mp hv
        subst v
        exact stale_eviction_lengthCap hu z _ hr
      · rw [if_neg hr] at hv
        obtain ⟨e, _, rfl⟩ := randomEviction_support (s := staleState u z) hne hv
        exact random_eviction_lengthCap hu z e

lemma prefixRun_nonrandomLengthCap {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ) (n : ℕ)
    {s : PMState α} (hs : s ∈ (prefixRun k tb σ h n).support) : NonrandomLengthCap k s := by
  induction n generalizing s with
  | zero =>
    have he := (PMF.mem_support_pure_iff _ _).mp hs
    subst s
    exact init_nonrandomLengthCap k
  | succ n ih =>
    obtain ⟨t, ht, hs⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
    unfold indexedStep at hs
    split_ifs at hs with hn
    · exact step_nonrandomLengthCap hk tb htb (prefixRun_cacheInvariant hk tb htb σ h n ht)
        (ih ht) n _ _ hs
    · have he := (PMF.mem_support_pure_iff _ _).mp hs
      subst s
      exact ih ht

end CachingML.PredMarker.PMFresh
end


section

open Set Filter
open scoped ENNReal Topology

namespace CachingML.PredMarker.PMFresh

lemma spread_one_le (ℓ : ℝ → ℝ → ℝ) (m : ℝ) : (1 : ℕ∞) ≤ spread ℓ m := by
  apply le_sInf
  rintro T ⟨t, rfl, ht, _⟩
  exact_mod_cast ht

lemma majorant_one_le {ℓ : ℝ → ℝ → ℝ} {S : ℝ → ℝ}
    (hspread : ∀ m : ℝ, 0 ≤ m → ∃ t : ℕ, spread ℓ m = t ∧ (t : ℝ) ≤ S m)
    {m : ℝ} (hm : 0 ≤ m) : 1 ≤ S m := by
  obtain ⟨t, ht, hS⟩ := hspread m hm
  have h := spread_one_le ℓ m
  rw [ht] at h
  have ht1 : 1 ≤ t := by exact_mod_cast h
  exact le_trans (by exact_mod_cast ht1) hS

lemma concave_monotone_of_one_le {S : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Ici 0) S) (hlow : ∀ x, 0 ≤ x → 1 ≤ S x) :
    MonotoneOn S (Ici 0) := by
  intro x hx y hy hxy
  by_contra h
  have hgap : 0 < S x - S y := sub_pos.mpr (lt_of_not_ge h)
  have hxy' : x < y := lt_of_le_of_ne hxy (by intro he; subst y; exact h le_rfl)
  obtain ⟨N, hN⟩ := exists_nat_gt ((S y - 1) / (S x - S y))
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (sub_nonneg.mpr (hlow y hy)) hgap.le) hN
  let z : ℝ := y + N * (y - x)
  have hyz : y < z := by dsimp [z]; nlinarith
  have hz : 0 ≤ z := le_trans hy hyz.le
  have hs := hconc.slope_anti_adjacent hx hz hxy' hyz
  have hcross := (div_le_div_iff₀ (sub_pos.mpr hyz) (sub_pos.mpr hxy')).mp hs
  have hzlow := hlow z hz
  have hN' : S y - 1 < N * (S x - S y) := (div_lt_iff₀ hgap).mp hN
  have hprod : 0 < (y - x) * (N * (S x - S y) - (S y - 1)) :=
    mul_pos (sub_pos.mpr hxy') (sub_pos.mpr hN')
  dsimp [z] at hcross
  nlinarith [mul_nonneg (sub_nonneg.mpr hzlow) (sub_nonneg.mpr hxy)]

lemma majorant_monotone {ℓ : ℝ → ℝ → ℝ} {S : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Ici 0) S)
    (hspread : ∀ m : ℝ, 0 ≤ m → ∃ t : ℕ, spread ℓ m = t ∧ (t : ℝ) ≤ S m) :
    MonotoneOn S (Ici 0) :=
  concave_monotone_of_one_le hconc (fun _ hm => majorant_one_le hspread hm)

lemma majorant_continuous {S : ℝ → ℝ} (hconc : ConcaveOn ℝ (Ici 0) S)
    (hzero : ContinuousWithinAt S (Ici 0) 0) : ContinuousOn S (Ici 0) :=
  hconc.continuousOn_Ici hzero

end CachingML.PredMarker.PMFresh
end


section

open Set Filter
open scoped ENNReal Topology BigOperators

namespace CachingML.PredMarker.PMFresh

lemma spread_attained {ℓ : ℝ → ℝ → ℝ} {m : ℝ} {t : ℕ}
    (ht : spread ℓ m = t) : 1 ≤ t ∧
      ∀ a : Fin t → ℤ, StrictMono a → ∀ b : Fin t → ℝ, Antitone b →
        m ≤ ∑ i, ℓ (a i) (b i) := by
  let A : Set ℕ∞ := {T | ∃ u : ℕ, T = u ∧ 1 ≤ u ∧
    ∀ a : Fin u → ℤ, StrictMono a → ∀ b : Fin u → ℝ, Antitone b →
      m ≤ ∑ i, ℓ (a i) (b i)}
  have hne : A.Nonempty := by
    by_contra h
    have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have hx : spread ℓ m = ⊤ := by change sInf A = ⊤; rw [he, sInf_empty]
    rw [ht] at hx
    exact ENat.natCast_ne_top t hx
  have hm : sInf A ∈ A := csInf_mem hne
  change spread ℓ m ∈ A at hm
  rw [ht] at hm
  obtain ⟨u, hu, hu1, huall⟩ := hm
  have hut : t = u := by exact_mod_cast hu
  subst u
  exact ⟨hu1, huall⟩

lemma prefix_loss_le {ℓ : ℝ → ℝ → ℝ} (hℓ : ∀ a b, 0 ≤ ℓ a b)
    {u t : ℕ} (hut : u ≤ t) (a : Fin t → ℤ) (b : Fin t → ℝ) :
    (∑ i : Fin u, ℓ (a (Fin.castLE hut i)) (b (Fin.castLE hut i))) ≤
      ∑ i : Fin t, ℓ (a i) (b i) := by
  classical
  have heq : (∑ i ∈ Finset.univ.image (Fin.castLE hut), ℓ (a i) (b i)) =
      ∑ i : Fin u, ℓ (a (Fin.castLE hut i)) (b (Fin.castLE hut i)) := by
    apply Finset.sum_image
    intro i _ j _ hij
    exact Fin.ext (congrArg (fun v : Fin t => v.val) hij)
  rw [← heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ => hℓ _ _)

lemma length_lt_spread_above_error {ℓ : ℝ → ℝ → ℝ} (hℓ : ∀ a b, 0 ≤ ℓ a b)
    {t : ℕ} (a : Fin t → ℤ) (ha : StrictMono a) (b : Fin t → ℝ) (hb : Antitone b)
    {m : ℝ} (hm : (∑ i, ℓ (a i) (b i)) < m) {u : ℕ} (hu : spread ℓ m = u) :
    t < u := by
  by_contra h
  have hut : u ≤ t := Nat.le_of_not_gt h
  have hc : StrictMono (Fin.castLE hut) := by intro i j hij; exact hij
  have hcost := (spread_attained hu).2 (a ∘ Fin.castLE hut) (ha.comp hc)
    (b ∘ Fin.castLE hut) (hb.comp_monotone hc.monotone)
  have hle := prefix_loss_le hℓ hut a b
  exact (not_le_of_gt hm) (hcost.trans hle)

lemma reversed_length_le_majorant {ℓ : ℝ → ℝ → ℝ} {S : ℝ → ℝ}
    (hℓ : ∀ a b, 0 ≤ ℓ a b) (hconc : ConcaveOn ℝ (Ici 0) S)
    (hzero : ContinuousWithinAt S (Ici 0) 0)
    (hspread : ∀ m : ℝ, 0 ≤ m → ∃ t : ℕ, spread ℓ m = t ∧ (t : ℝ) ≤ S m)
    {t : ℕ} (a : Fin t → ℤ) (ha : StrictMono a) (b : Fin t → ℝ) (hb : Antitone b) :
    (t : ℝ) ≤ S (∑ i, ℓ (a i) (b i)) := by
  let E : ℝ := ∑ i, ℓ (a i) (b i)
  have hE : 0 ≤ E := Finset.sum_nonneg (fun i _ => hℓ _ _)
  have hseq : Tendsto (fun n : ℕ => E + 1 / ((n : ℝ) + 1)) atTop (𝓝 E) := by
    simpa using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hwithin : Tendsto (fun n : ℕ => E + 1 / ((n : ℝ) + 1)) atTop (𝓝[Ici 0] E) :=
    tendsto_nhdsWithin_iff.mpr ⟨hseq, Eventually.of_forall (fun n => by
      change 0 ≤ E + 1 / ((n : ℝ) + 1); positivity)⟩
  apply ge_of_tendsto ((majorant_continuous hconc hzero E hE).tendsto.comp hwithin)
  filter_upwards [] with n
  have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
  obtain ⟨u, hu, huS⟩ := hspread (E + 1 / ((n : ℝ) + 1)) (add_nonneg hE hp.le)
  have htu := length_lt_spread_above_error hℓ a ha b hb (by change E < _; linarith) hu
  exact le_trans (by exact_mod_cast htu.le) huS

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

def labelAt (σ : List α) (j : ℕ) : ℕ :=
  if hj : j < σ.length then nextArrival σ ⟨j, hj⟩ else 0

def predictionAt (σ : List α) (h : Fin σ.length → ℝ) (j : ℕ) : ℝ :=
  if hj : j < σ.length then h ⟨j, hj⟩ else 0

theorem labelAt_fin (σ : List α) (j : Fin σ.length) : labelAt σ j.val = nextArrival σ j := by
  simp [labelAt, j.isLt]

omit [DecidableEq α] in
theorem predictionAt_fin (σ : List α) (h : Fin σ.length → ℝ) (j : Fin σ.length) :
    predictionAt σ h j.val = h j := by
  simp [predictionAt, j.isLt]

omit [DecidableEq α] in
theorem pairwise_strict_append_last {β : Type*} (f : β → ℕ) {L : List β} {a b : β}
    (hL : L.Pairwise (fun x y => f x < f y)) (hlast : L.getLast? = some a)
    (hab : f a < f b) : (L ++ [b]).Pairwise (fun x y => f x < f y) := by
  rw [List.pairwise_append]
  refine ⟨hL, by simp, ?_⟩
  intro x hx y hy
  have hyb : y = b := by simpa using hy
  subst y
  have hweak : L.Pairwise (fun x y => f x ≤ f y) := hL.imp (fun h => h.le)
  have hle := hweak.rel_getLast_of_rel_getLast_getLast hx (le_refl _)
  rw [List.getLast_of_getLast?_eq_some hlast] at hle
  exact hle.trans_lt hab

end CachingML.PredMarker.PMFresh
end


section

open Set

namespace CachingML.PredMarker.PMFresh

lemma ordered_list_length_le_majorant {β : Type*} (L : List β)
    (a : β → ℤ) (b : β → ℝ)
    (ha : L.Pairwise (fun x y => a x < a y))
    (hb : L.Pairwise (fun x y => b y ≤ b x))
    {ℓ : ℝ → ℝ → ℝ} {S : ℝ → ℝ}
    (hℓ : ∀ x y, 0 ≤ ℓ x y) (hc : ConcaveOn ℝ (Ici 0) S)
    (h0 : ContinuousWithinAt S (Ici 0) 0)
    (hsp : ∀ m : ℝ, 0 ≤ m → ∃ t : ℕ, spread ℓ m = t ∧ (t : ℝ) ≤ S m) :
    (L.length : ℝ) ≤ S ((L.map (fun x => ℓ (a x) (b x))).sum) := by
  have ham : StrictMono (fun i : Fin L.length => a (L.get i)) :=
    fun _ _ hij => ha.rel_get_of_lt hij
  have hbm : Antitone (fun i : Fin L.length => b (L.get i)) := by
    intro i j hij
    rcases lt_or_eq_of_le hij with hij | rfl
    · exact hb.rel_get_of_lt hij
    · exact le_rfl
  have hh := reversed_length_le_majorant hℓ hc h0 hsp _ ham _ hbm
  have heq : (∑ i : Fin L.length, ℓ (a (L.get i)) (b (L.get i))) =
      (L.map (fun x => ℓ (a x) (b x))).sum := by
    rw [← List.sum_ofFn]
    congr 1
    change List.ofFn ((fun x => ℓ (a x) (b x)) ∘ L.get) = _
    rw [← List.map_ofFn, List.ofFn_get]
  rwa [heq] at hh

variable {α : Type*} [DecidableEq α]

lemma bounded_ordered_indices_majorant (σ : List α) (h : Fin σ.length → ℝ)
    (L : List ℕ) (hvalid : ∀ j ∈ L, j < σ.length)
    (ha : L.Pairwise (fun i j => labelAt σ i < labelAt σ j))
    (hb : L.Pairwise (fun i j => predictionAt σ h j ≤ predictionAt σ h i))
    {ℓ : ℝ → ℝ → ℝ} {S : ℝ → ℝ}
    (hℓ : ∀ x y, 0 ≤ ℓ x y) (hc : ConcaveOn ℝ (Ici 0) S)
    (h0 : ContinuousWithinAt S (Ici 0) 0)
    (hsp : ∀ m : ℝ, 0 ≤ m → ∃ t : ℕ, spread ℓ m = t ∧ (t : ℝ) ≤ S m) :
    (L.length : ℝ) ≤ S ((L.map (lossAt ℓ σ h)).sum) := by
  have hh := ordered_list_length_le_majorant L (fun j => (labelAt σ j : ℤ))
    (predictionAt σ h) (ha.imp (fun hij => by exact_mod_cast hij)) hb hℓ hc h0 hsp
  have heq : L.map (fun j => ℓ (((labelAt σ j : ℕ) : ℤ) : ℝ) (predictionAt σ h j)) =
      L.map (lossAt ℓ σ h) := by
    apply List.map_congr_left
    intro j hj
    simp [labelAt, predictionAt, lossAt, hvalid j hj]
  rwa [heq] at hh

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

def PredictionEnvelope (s : PMState α) : Prop :=
  ∀ e ∈ s.stale \ s.cache, (s.phase, s.chainOf e) ∉ s.randomChains →
    ∀ x ∈ s.cache \ s.marked, s.pred x ≤ s.pred e

def PredictionEnvelopeExcept (z : α) (s : PMState α) : Prop :=
  ∀ e ∈ s.stale \ s.cache, e ≠ z → (s.phase, s.chainOf e) ∉ s.randomChains →
    ∀ x ∈ s.cache \ s.marked, s.pred x ≤ s.pred e

lemma predictionEnvelope_init : PredictionEnvelope (initState α) := by
  intro e he
  simp [initState] at he

lemma PredictionEnvelope.except {s : PMState α} (h : PredictionEnvelope s) (z : α) :
    PredictionEnvelopeExcept z s := fun e he _ hr x hx => h e he hr x hx

lemma savePrediction_envelope_except {s : PMState α} (h : PredictionEnvelope s)
    (i : ℕ) (z : α) (hz : ℝ) (hzc : z ∉ s.cache) :
    PredictionEnvelopeExcept z (savePrediction s i z hz) := by
  intro e he hez hr x hx
  have hxc : x ∈ s.cache := (Finset.mem_sdiff.mp hx).1
  have hxz : x ≠ z := ne_of_mem_of_not_mem hxc hzc
  change Function.update s.pred z hz x ≤ Function.update s.pred z hz e
  rw [Function.update_of_ne hxz, Function.update_of_ne hez]
  exact h e he hr x hx

lemma phaseStart_envelope_except {s : PMState α} {z : α} (k : ℕ)
    (h : PredictionEnvelopeExcept z s) : PredictionEnvelopeExcept z (phaseStart k s) := by
  unfold phaseStart
  split_ifs
  · intro e he
    simp at he
  · exact h

lemma markRandom_envelope_except {s : PMState α} {z : α} (c : ℕ)
    (h : PredictionEnvelopeExcept z s) :
    PredictionEnvelopeExcept z { s with randomChains := insert (s.phase, c) s.randomChains } := by
  intro e he hez hr x hx
  exact h e he hez (fun hold => hr (Or.inr hold)) x hx

lemma evictInto_envelope {s : PMState α} (z : α) (c : ℕ) (e : α)
    (h : PredictionEnvelopeExcept z s)
    (hnew : (s.phase, c) ∉ s.randomChains → ∀ x ∈ s.cache \ s.marked, s.pred x ≤ s.pred e) :
    PredictionEnvelope (evictInto s z c e) := by
  intro r hr hn x hx
  have hr' : r ∈ s.stale ∧ r ∉ insert z (s.cache.erase e) := Finset.mem_sdiff.mp hr
  have hx' : x ∈ insert z (s.cache.erase e) ∧ x ∉ insert z s.marked := Finset.mem_sdiff.mp hx
  have hxz : x ≠ z := by intro heq; subst x; exact hx'.2 (Finset.mem_insert_self _ _)
  have hxC : x ∈ s.cache := Finset.mem_of_mem_erase ((Finset.mem_insert.mp hx'.1).resolve_left hxz)
  have hxM : x ∉ s.marked := fun hm => hx'.2 (Finset.mem_insert_of_mem hm)
  have hxold : x ∈ s.cache \ s.marked := Finset.mem_sdiff.mpr ⟨hxC, hxM⟩
  change s.pred x ≤ s.pred r
  by_cases hre : r = e
  · subst r
    have hn' : (s.phase, c) ∉ s.randomChains := by
      simpa only [evictInto, Function.update_self] using hn
    exact hnew hn' x hxold
  · have hrz : r ≠ z := by intro heq; subst r; exact hr'.2 (Finset.mem_insert_self _ _)
    have hrC : r ∉ s.cache := by
      intro hrc
      exact hr'.2 (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hre, hrc⟩))
    have hn' : (s.phase, s.chainOf r) ∉ s.randomChains := by
      simpa only [evictInto, Function.update_of_ne hre] using hn
    exact h r (Finset.mem_sdiff.mpr ⟨hr'.1, hrC⟩) hrz hn' x hxold

lemma hitOrFill_saved_envelope {s : PMState α} (h : PredictionEnvelope s)
    (i : ℕ) (z : α) (hz : ℝ) : PredictionEnvelope (hitOrFill (savePrediction s i z hz) z) := by
  intro r hr hn x hx
  have hr' : r ∈ s.stale ∧ r ∉ insert z s.cache := Finset.mem_sdiff.mp hr
  have hx' : x ∈ insert z s.cache ∧ x ∉ insert z s.marked := Finset.mem_sdiff.mp hx
  have hrz : r ≠ z := by intro heq; subst r; exact hr'.2 (Finset.mem_insert_self _ _)
  have hxz : x ≠ z := by intro heq; subst x; exact hx'.2 (Finset.mem_insert_self _ _)
  have hrC : r ∉ s.cache := fun hrc => hr'.2 (Finset.mem_insert_of_mem hrc)
  have hxC : x ∈ s.cache := (Finset.mem_insert.mp hx'.1).resolve_left hxz
  have hxM : x ∉ s.marked := fun hm => hx'.2 (Finset.mem_insert_of_mem hm)
  change Function.update s.pred z hz x ≤ Function.update s.pred z hz r
  rw [Function.update_of_ne hxz, Function.update_of_ne hrz]
  exact h r (Finset.mem_sdiff.mpr ⟨hr'.1, hrC⟩) hn x (Finset.mem_sdiff.mpr ⟨hxC, hxM⟩)

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

lemma miss_predictionEnvelope {k : ℕ} (u : PMState α) (z : α) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (hu : PredictionEnvelopeExcept z u)
    (hne : (u.cache \ u.marked).Nonempty) {v : PMState α}
    (hv : v ∈ (if z ∉ u.stale then
      PMF.pure (evictInto (cleanState u) z (u.clean + 1) (tb (cleanState u)))
      else if (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ) then
        PMF.pure (evictInto (staleState u z) z (u.chainOf z) (tb (staleState u z)))
      else randomEviction (staleState u z) z (u.chainOf z)).support) :
    PredictionEnvelope v := by
  by_cases hc : z ∉ u.stale
  · rw [if_pos hc] at hv
    have heq := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    exact evictInto_envelope z _ _ (s := cleanState u) hu
      (fun _ => (htb (cleanState u) hne).2)
  · rw [if_neg hc] at hv
    by_cases hr : (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ)
    · rw [if_pos hr] at hv
      have heq := (PMF.mem_support_pure_iff _ _).mp hv
      subst v
      exact evictInto_envelope z _ _ (s := staleState u z) hu
        (fun _ => (htb (staleState u z) hne).2)
    · rw [if_neg hr] at hv
      obtain ⟨e, _, rfl⟩ := randomEviction_support (s := staleState u z) hne hv
      apply evictInto_envelope z _ e
      · exact markRandom_envelope_except _ (s := staleState u z) hu
      · intro hn
        exact (hn (Or.inl rfl)).elim

lemma step_predictionEnvelope {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) {s : PMState α} (hs : CacheInvariant k s)
    (hE : PredictionEnvelope s) (i : ℕ) (z : α) (hz : ℝ) {v : PMState α}
    (hv : v ∈ (step k tb s i z hz).support) : PredictionEnvelope v := by
  rw [step_factored] at hv
  dsimp only at hv
  let t := savePrediction s i z hz
  have ht : CacheInvariant k t := save_cacheInvariant hs i z hz
  by_cases hh : z ∈ t.cache ∨ t.cache.card < k
  · simp only [show z ∈ (savePrediction s i z hz).cache ∨
      (savePrediction s i z hz).cache.card < k from hh, if_pos] at hv
    have heq := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    exact hitOrFill_saved_envelope hE i z hz
  · simp only [show ¬ (z ∈ (savePrediction s i z hz).cache ∨
      (savePrediction s i z hz).cache.card < k) from hh, if_false] at hv
    have hf : t.cache.card = k := by have := ht.card_le; simp only [not_or] at hh; omega
    have hEt : PredictionEnvelopeExcept z t := savePrediction_envelope_except hE i z hz (not_or.mp hh).1
    exact miss_predictionEnvelope (phaseStart k t) z tb htb (phaseStart_envelope_except k hEt)
      (phaseStart_candidates_nonempty hk ht hf) hv

lemma prefixRun_predictionEnvelope {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ) (n : ℕ)
    {s : PMState α} (hs : s ∈ (prefixRun k tb σ h n).support) : PredictionEnvelope s := by
  induction n generalizing s with
  | zero =>
    have he := (PMF.mem_support_pure_iff _ _).mp hs
    subst s
    exact predictionEnvelope_init
  | succ n ih =>
    obtain ⟨t, ht, hs⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
    unfold indexedStep at hs
    split_ifs at hs with hn
    · exact step_predictionEnvelope hk tb htb (prefixRun_cacheInvariant hk tb htb σ h n ht)
        (ih ht) n _ _ hs
    · have he := (PMF.mem_support_pure_iff _ _).mp hs
      subst s
      exact ih ht

lemma run_predictionEnvelope {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {s : PMState α} (hs : s ∈ (run k tb σ h).support) : PredictionEnvelope s := by
  rw [run_eq_prefixRun] at hs
  exact prefixRun_predictionEnvelope hk tb htb σ h σ.length hs

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

def RepresentativeTail (s : PMState α) : Prop :=
  ∀ e ∈ s.stale \ s.cache,
    (indexFamily s (s.phase, s.chainOf e)).getLast? = some (s.predIdx e)

def RepresentativeTailExcept (s : PMState α) (z : α) : Prop :=
  ∀ e ∈ s.stale \ s.cache, e ≠ z →
    (indexFamily s (s.phase, s.chainOf e)).getLast? = some (s.predIdx e)

theorem init_representativeTail : RepresentativeTail (initState α) := by
  intro e he
  simp [initState] at he

theorem save_representativeTailExcept {s : PMState α} (hs : RepresentativeTail s)
    (i : ℕ) (z : α) (hz : ℝ) : RepresentativeTailExcept (savePrediction s i z hz) z := by
  intro e he hez
  change (indexFamily s (s.phase, s.chainOf e)).getLast? =
    some (Function.update s.predIdx z i e)
  rw [Function.update_of_ne hez]
  exact hs e he

theorem phaseStart_representativeTailExcept (k : ℕ) {s : PMState α} {z : α}
    (hs : RepresentativeTailExcept s z) : RepresentativeTailExcept (phaseStart k s) z := by
  unfold phaseStart
  split_ifs
  · intro e he
    simp at he
  · exact hs

theorem hitOrFill_representativeTail {s : PMState α} {z : α}
    (hs : RepresentativeTailExcept s z) : RepresentativeTail (hitOrFill s z) := by
  intro e he
  have hD : e ∈ s.stale \ s.cache := by
    obtain ⟨heS, heC⟩ := Finset.mem_sdiff.mp he
    exact Finset.mem_sdiff.mpr ⟨heS, fun h => heC (Finset.mem_insert_of_mem h)⟩
  have hez : e ≠ z := by
    intro heq
    subst e
    exact (Finset.mem_sdiff.mp he).2 (Finset.mem_insert_self _ _)
  exact hs e hD hez

theorem clean_eviction_representativeTail {k : ℕ} {s : PMState α}
    (hp : PhaseCacheInvariant k s) (hr : NativeRepresentatives s)
    {z e : α} (hz : z ∉ s.stale) (he : e ∈ s.cache \ s.marked)
    (ht : RepresentativeTailExcept s z) :
    RepresentativeTail (evictInto (cleanState s) z (s.clean + 1) e) := by
  intro d hd
  have heS := hp.unmarked_stale he
  have heC := (Finset.mem_sdiff.mp he).1
  change d ∈ s.stale \ insert z (s.cache.erase e) at hd
  rw [missing_clean_update s.stale s.cache hz heS heC] at hd
  rcases Finset.mem_insert.mp hd with rfl | hd
  · simp [indexFamily, evictInto, cleanState]
  · have hde : d ≠ e := ne_of_mem_of_not_mem hd
      (show e ∉ s.stale \ s.cache from fun h => (Finset.mem_sdiff.mp h).2 heC)
    have hdz : d ≠ z := ne_of_mem_of_not_mem (Finset.mem_sdiff.mp hd).1 hz
    have hchain : s.chainOf d ≠ s.clean + 1 := by
      have := (hr.bounds d hd).2
      omega
    simpa [indexFamily, evictInto, cleanState, hde, hchain] using ht d hd hdz

theorem stale_eviction_representativeTail {k : ℕ} {s : PMState α}
    (hp : PhaseCacheInvariant k s) (hr : NativeRepresentatives s)
    {z e : α} (hzS : z ∈ s.stale) (hzC : z ∉ s.cache) (he : e ∈ s.cache \ s.marked)
    (ht : RepresentativeTailExcept s z) :
    RepresentativeTail (evictInto (staleState s z) z (s.chainOf z) e) := by
  intro d hd
  have heS := hp.unmarked_stale he
  have heC := (Finset.mem_sdiff.mp he).1
  change d ∈ s.stale \ insert z (s.cache.erase e) at hd
  rw [missing_stale_update s.stale s.cache hzS hzC heS heC] at hd
  rcases Finset.mem_insert.mp hd with rfl | hd
  · simp [indexFamily, evictInto, staleState]
  · obtain ⟨hdz, hd⟩ := Finset.mem_erase.mp hd
    have hde : d ≠ e := ne_of_mem_of_not_mem hd
      (show e ∉ s.stale \ s.cache from fun h => (Finset.mem_sdiff.mp h).2 heC)
    have hchain : s.chainOf d ≠ s.chainOf z := by
      intro h
      exact hdz (hr.injective hd (Finset.mem_sdiff.mpr ⟨hzS, hzC⟩) h)
    simpa [indexFamily, evictInto, staleState, hde, hchain] using ht d hd hdz

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

theorem miss_representativeTail {k : ℕ} (u : PMState α) (z : α) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (hp : PhaseCacheInvariant k u) (hu : NativeRepresentatives u)
    (ht : RepresentativeTailExcept u z) (hz : z ∉ u.cache)
    (hne : (u.cache \ u.marked).Nonempty) {v : PMState α}
    (hv : v ∈ (if z ∉ u.stale then
      PMF.pure (evictInto (cleanState u) z (u.clean + 1) (tb (cleanState u)))
      else if (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ) then
        PMF.pure (evictInto (staleState u z) z (u.chainOf z) (tb (staleState u z)))
      else randomEviction (staleState u z) z (u.chainOf z)).support) :
    RepresentativeTail v := by
  by_cases hc : z ∉ u.stale
  · rw [if_pos hc] at hv
    have he := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    exact clean_eviction_representativeTail hp hu hc (htb (cleanState u) hne).1 ht
  · rw [if_neg hc] at hv
    have hzS : z ∈ u.stale := not_not.mp hc
    by_cases hr : (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ)
    · rw [if_pos hr] at hv
      have he := (PMF.mem_support_pure_iff _ _).mp hv
      subst v
      exact stale_eviction_representativeTail hp hu hzS hz (htb (staleState u z) hne).1 ht
    · rw [if_neg hr] at hv
      obtain ⟨e, he, rfl⟩ := randomEviction_support (s := staleState u z) hne hv
      exact stale_eviction_representativeTail hp hu hzS hz he ht

theorem step_representativeTail {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) {s : PMState α} (hs : OperationalInvariant k s)
    (hTail : RepresentativeTail s) (i : ℕ) (z : α) (hz : ℝ) {v : PMState α}
    (hv : v ∈ (step k tb s i z hz).support) : RepresentativeTail v := by
  rw [step_factored] at hv
  dsimp only at hv
  let t := savePrediction s i z hz
  have ht : CacheInvariant k t := save_cacheInvariant hs.cache i z hz
  have hpt : PhaseCacheInvariant k t := ⟨hs.phaseCache.unmarked_stale, hs.phaseCache.stale_full⟩
  have hrt : NativeRepresentatives t := hs.representatives
  have htt : RepresentativeTailExcept t z := save_representativeTailExcept hTail i z hz
  by_cases hh : z ∈ t.cache ∨ t.cache.card < k
  · simp only [show z ∈ (savePrediction s i z hz).cache ∨
      (savePrediction s i z hz).cache.card < k from hh, if_pos] at hv
    have he := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    exact hitOrFill_representativeTail htt
  · simp only [show ¬ (z ∈ (savePrediction s i z hz).cache ∨
      (savePrediction s i z hz).cache.card < k) from hh, if_false] at hv
    have hf : t.cache.card = k := by have := ht.card_le; simp only [not_or] at hh; omega
    exact miss_representativeTail (phaseStart k t) z tb htb
      (phaseStart_phaseCacheInvariant ht hpt) (phaseStart_nativeRepresentatives k hrt)
      (phaseStart_representativeTailExcept k htt)
      (by rw [phaseStart_cache]; exact (not_or.mp hh).1)
      (phaseStart_candidates_nonempty hk ht hf) hv

theorem prefixRun_representativeTail {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ) (n : ℕ)
    {s : PMState α} (hs : s ∈ (prefixRun k tb σ h n).support) : RepresentativeTail s := by
  induction n generalizing s with
  | zero =>
    have he := (PMF.mem_support_pure_iff _ _).mp hs
    subst s
    exact init_representativeTail
  | succ n ih =>
    obtain ⟨t, ht, hs⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
    unfold indexedStep at hs
    split_ifs at hs with hn
    · exact step_representativeTail hk tb htb
        (prefixRun_operationalInvariant hk tb htb σ h n ht) (ih ht) n _ _ hs
    · have he := (PMF.mem_support_pure_iff _ _).mp hs
      subst s
      exact ih ht

theorem run_representativeTail {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {s : PMState α} (hs : s ∈ (run k tb σ h).support) : RepresentativeTail s := by
  rw [run_eq_prefixRun] at hs
  exact prefixRun_representativeTail hk tb htb σ h σ.length hs

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

def CachedPrediction (σ : List α) (h : Fin σ.length → ℝ) (n : ℕ) (s : PMState α) : Prop :=
  ∀ z ∈ s.cache, ∃ j : Fin σ.length,
    j.val < n ∧ σ.get j = z ∧ s.predIdx z = j.val ∧ s.pred z = h j ∧
      ∀ l : Fin σ.length, j.val < l.val → l.val < n → σ.get l ≠ z

omit [DecidableEq α] in
theorem cachedPrediction_init (σ : List α) (h : Fin σ.length → ℝ) :
    CachedPrediction σ h 0 (initState α) := by
  intro z hz
  simp [initState] at hz

theorem cachedPrediction_step {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (σ : List α) (h : Fin σ.length → ℝ) {n : ℕ} (hn : n < σ.length)
    {s : PMState α} (hs : CacheInvariant k s) (hp : CachedPrediction σ h n s)
    {v : PMState α}
    (hv : v ∈ (step k tb s n (σ.get ⟨n, hn⟩) (h ⟨n, hn⟩)).support) :
    CachedPrediction σ h (n + 1) v := by
  obtain ⟨hpred, hidx, _, hcache⟩ := step_observations hk tb hs n _ _ hv
  intro z hz
  by_cases he : z = σ.get ⟨n, hn⟩
  · subst z
    refine ⟨⟨n, hn⟩, by change n < n + 1; omega, rfl, ?_, ?_, ?_⟩
    · rw [hidx]
      simp
    · rw [hpred]
      simp
    · intro l hl hn'
      change n < l.val at hl
      omega
  · have hzs : z ∈ s.cache := (Finset.mem_insert.mp (hcache hz)).resolve_left he
    obtain ⟨j, hj, hjz, hji, hjp, hlast⟩ := hp z hzs
    refine ⟨j, by omega, hjz, ?_, ?_, ?_⟩
    · rw [hidx]
      rw [Function.update_of_ne he]
      exact hji
    · rw [hpred]
      rw [Function.update_of_ne he]
      exact hjp
    · intro l hjl hln
      by_cases hl : l.val < n
      · exact hlast l hjl hl
      · have hle : l = ⟨n, hn⟩ := Fin.ext (by change l.val = n; omega)
        rw [hle]
        exact Ne.symm he

theorem prefixRun_cachedPrediction {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {n : ℕ} (hn : n ≤ σ.length) {s : PMState α}
    (hs : s ∈ (prefixRun k tb σ h n).support) : CachedPrediction σ h n s := by
  induction n generalizing s with
  | zero =>
    have he := (PMF.mem_support_pure_iff _ _).mp hs
    subst s
    exact cachedPrediction_init σ h
  | succ n ih =>
    have hnlt : n < σ.length := by omega
    rw [prefixRun_succ tb σ h hnlt] at hs
    obtain ⟨t, ht, hs⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
    exact cachedPrediction_step hk tb σ h hnlt
      (prefixRun_cacheInvariant hk tb htb σ h n ht) (ih (by omega) ht) hs

theorem run_cachedPrediction {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {s : PMState α} (hs : s ∈ (run k tb σ h).support) : CachedPrediction σ h σ.length s := by
  rw [run_eq_prefixRun] at hs
  exact prefixRun_cachedPrediction hk tb htb σ h le_rfl hs

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

def KnownPrediction (σ : List α) (h : Fin σ.length → ℝ) (n : ℕ) (s : PMState α) : Prop :=
  ∀ z ∈ s.cache ∪ s.stale, ∃ j : Fin σ.length,
    j.val < n ∧ σ.get j = z ∧ s.predIdx z = j.val ∧ s.pred z = h j ∧
      ∀ l : Fin σ.length, j.val < l.val → l.val < n → σ.get l ≠ z

lemma knownPrediction_init (σ : List α) (h : Fin σ.length → ℝ) :
    KnownPrediction σ h 0 (initState α) := by
  intro z hz
  simp [initState] at hz

lemma step_known_subset {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    {s : PMState α} (hs : CacheInvariant k s) (i : ℕ) (z : α) (hz : ℝ)
    {v : PMState α} (hv : v ∈ (step k tb s i z hz).support) :
    v.cache ∪ v.stale ⊆ insert z (s.cache ∪ s.stale) := by
  have hc := (step_observations hk tb hs i z hz hv).2.2.2
  have hp := congrArg PhaseState.previous (step_nativePhase hk tb hs i z hz hv)
  change v.stale = (phaseStep k (nativePhase s) z).previous at hp
  have hstale : v.stale ⊆ s.cache ∪ s.stale := by
    rw [hp]
    unfold phaseStep nativePhase
    split_ifs
    · exact Finset.subset_union_right
    · exact Finset.subset_union_right
    · exact hs.marked_subset.trans Finset.subset_union_left
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · rcases Finset.mem_insert.mp (hc hx) with rfl | hx
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hx)
  · exact Finset.mem_insert_of_mem (hstale hx)

lemma knownPrediction_step {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (σ : List α) (h : Fin σ.length → ℝ) {n : ℕ} (hn : n < σ.length)
    {s : PMState α} (hs : CacheInvariant k s) (hp : KnownPrediction σ h n s)
    {v : PMState α}
    (hv : v ∈ (step k tb s n (σ.get ⟨n, hn⟩) (h ⟨n, hn⟩)).support) :
    KnownPrediction σ h (n + 1) v := by
  obtain ⟨hpred, hidx, _, _⟩ := step_observations hk tb hs n _ _ hv
  have hknown := step_known_subset hk tb hs n _ _ hv
  intro z hz
  by_cases he : z = σ.get ⟨n, hn⟩
  · subst z
    refine ⟨⟨n, hn⟩, by change n < n + 1; omega, rfl, ?_, ?_, ?_⟩
    · rw [hidx]; simp
    · rw [hpred]; simp
    · intro l hl hn'
      change n < l.val at hl
      omega
  · have hzs : z ∈ s.cache ∪ s.stale := (Finset.mem_insert.mp (hknown hz)).resolve_left he
    obtain ⟨j, hj, hjz, hji, hjp, hlast⟩ := hp z hzs
    refine ⟨j, by omega, hjz, ?_, ?_, ?_⟩
    · rw [hidx, Function.update_of_ne he]
      exact hji
    · rw [hpred, Function.update_of_ne he]
      exact hjp
    · intro l hjl hln
      by_cases hl : l.val < n
      · exact hlast l hjl hl
      · have hle : l = ⟨n, hn⟩ := Fin.ext (by change l.val = n; omega)
        rw [hle]
        exact Ne.symm he

lemma prefixRun_knownPrediction {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {n : ℕ} (hn : n ≤ σ.length) {s : PMState α}
    (hs : s ∈ (prefixRun k tb σ h n).support) : KnownPrediction σ h n s := by
  induction n generalizing s with
  | zero =>
    have he := (PMF.mem_support_pure_iff _ _).mp hs
    subst s
    exact knownPrediction_init σ h
  | succ n ih =>
    have hnlt : n < σ.length := by omega
    rw [prefixRun_succ tb σ h hnlt] at hs
    obtain ⟨t, ht, hs⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
    exact knownPrediction_step hk tb σ h hnlt
      (prefixRun_cacheInvariant hk tb htb σ h n ht) (ih (by omega) ht) hs

lemma run_knownPrediction {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {s : PMState α} (hs : s ∈ (run k tb σ h).support) : KnownPrediction σ h σ.length s := by
  rw [run_eq_prefixRun] at hs
  exact prefixRun_knownPrediction hk tb htb σ h le_rfl hs

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

def ChainPredictionOrder (σ : List α) (h : Fin σ.length → ℝ) (s : PMState α) : Prop :=
  ∀ p, p ∉ s.randomChains →
    (indexFamily s p).Pairwise (fun a b => predictionAt σ h b ≤ predictionAt σ h a)

omit [DecidableEq α] in
lemma pairwise_ge_append_last {β : Type*} (f : β → ℝ) {L : List β} {a b : β}
    (hL : L.Pairwise (fun x y => f y ≤ f x)) (hlast : L.getLast? = some a)
    (hab : f b ≤ f a) : (L ++ [b]).Pairwise (fun x y => f y ≤ f x) := by
  rw [List.pairwise_append]
  refine ⟨hL, by simp, ?_⟩
  intro x hx y hy
  have hyb : y = b := by simpa using hy
  subst y
  have hle := hL.rel_getLast_of_rel_getLast_getLast hx (le_refl _)
  rw [List.getLast_of_getLast?_eq_some hlast] at hle
  exact hab.trans hle

omit [DecidableEq α] in
lemma init_chainPredictionOrder (σ : List α) (h : Fin σ.length → ℝ) :
    ChainPredictionOrder σ h (initState α) := by
  intro p _
  simp [indexFamily, initState]

omit [DecidableEq α] in
lemma phaseStart_chainPredictionOrder (σ : List α) (h : Fin σ.length → ℝ)
    (k : ℕ) {s : PMState α} (hs : ChainPredictionOrder σ h s) :
    ChainPredictionOrder σ h (phaseStart k s) := by
  unfold phaseStart
  split_ifs <;> exact hs

lemma clean_eviction_predictionOrder (σ : List α) (h : Fin σ.length → ℝ)
    {s : PMState α} (hs : ChainPredictionOrder σ h s) (hb : ChainBookkeeping s)
    (z e : α) : ChainPredictionOrder σ h (evictInto (cleanState s) z (s.clean + 1) e) := by
  have hi := evictInto_indexFamily (cleanState s) z (s.clean + 1) e
  change indexFamily (evictInto (cleanState s) z (s.clean + 1) e) =
    Function.update (indexFamily s) (s.phase, s.clean + 1)
      (indexFamily s (s.phase, s.clean + 1) ++ [s.predIdx e]) at hi
  intro p hp
  rw [hi]
  by_cases heq : p = (s.phase, s.clean + 1)
  · subst p
    rw [Function.update_self, hb.current_empty _ (Or.inl (Nat.lt_succ_self _))]
    simp
  · rw [Function.update_of_ne heq]
    exact hs p hp

lemma random_eviction_predictionOrder (σ : List α) (h : Fin σ.length → ℝ)
    {s : PMState α} (hs : ChainPredictionOrder σ h s) (z e : α) (c : ℕ) :
    ChainPredictionOrder σ h
      (evictInto { s with randomChains := insert (s.phase, c) s.randomChains } z c e) := by
  have hi := evictInto_indexFamily { s with randomChains := insert (s.phase, c) s.randomChains } z c e
  change indexFamily (evictInto { s with randomChains := insert (s.phase, c) s.randomChains } z c e) =
    Function.update (indexFamily s) (s.phase, c)
      (indexFamily s (s.phase, c) ++ [s.predIdx e]) at hi
  intro p hp
  change p ∉ insert (s.phase, c) s.randomChains at hp
  have hpne : p ≠ (s.phase, c) := fun he => hp (Or.inl he)
  rw [hi, Function.update_of_ne hpne]
  exact hs p (fun he => hp (Or.inr he))

lemma stale_eviction_predictionOrder (σ : List α) (h : Fin σ.length → ℝ)
    {n : ℕ} {s : PMState α} (hs : ChainPredictionOrder σ h s)
    (ht : RepresentativeTail s) (hp : KnownPrediction σ h n s)
    (hE : PredictionEnvelope s) {z e : α} (hzS : z ∈ s.stale) (hzC : z ∉ s.cache)
    (he : e ∈ s.cache \ s.marked) (hz : ℝ) :
    ChainPredictionOrder σ h
      (evictInto (staleState (savePrediction s n z hz) z) z (s.chainOf z) e) := by
  have hez : e ≠ z := ne_of_mem_of_not_mem (Finset.mem_sdiff.mp he).1 hzC
  have hi := evictInto_indexFamily (staleState (savePrediction s n z hz) z) z (s.chainOf z) e
  change indexFamily (evictInto (staleState (savePrediction s n z hz) z) z (s.chainOf z) e) =
    Function.update (indexFamily s) (s.phase, s.chainOf z)
      (indexFamily s (s.phase, s.chainOf z) ++ [Function.update s.predIdx z n e]) at hi
  rw [Function.update_of_ne hez] at hi
  intro p hnr
  rw [hi]
  by_cases hpk : p = (s.phase, s.chainOf z)
  · subst p
    rw [Function.update_self]
    have hlast := ht z (Finset.mem_sdiff.mpr ⟨hzS, hzC⟩)
    obtain ⟨j, _, _, hjidx, hjpred, _⟩ := hp z (Finset.mem_union_right _ hzS)
    obtain ⟨l, _, _, hlidx, hlpred, _⟩ := hp e
      (Finset.mem_union_left _ (Finset.mem_sdiff.mp he).1)
    have hle := hE z (Finset.mem_sdiff.mpr ⟨hzS, hzC⟩) hnr e he
    have hvalues : predictionAt σ h (s.predIdx e) ≤ predictionAt σ h (s.predIdx z) := by
      rw [hjidx, hlidx, predictionAt_fin, predictionAt_fin]
      rwa [hjpred, hlpred] at hle
    exact pairwise_ge_append_last (predictionAt σ h) (hs _ hnr) hlast hvalues
  · rw [Function.update_of_ne hpk]
    exact hs p hnr

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

lemma step_chainPredictionOrder {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {n : ℕ} {s : PMState α} (hs : OperationalInvariant k s)
    (hO : ChainPredictionOrder σ h s) (hTail : RepresentativeTail s)
    (hP : KnownPrediction σ h n s) (hE : PredictionEnvelope s)
    (z : α) (hz : ℝ) {v : PMState α}
    (hv : v ∈ (step k tb s n z hz).support) : ChainPredictionOrder σ h v := by
  rw [step_factored] at hv
  dsimp only at hv
  let t := savePrediction s n z hz
  have ht : CacheInvariant k t := save_cacheInvariant hs.cache n z hz
  have hOt : ChainPredictionOrder σ h t := hO
  by_cases hh : z ∈ t.cache ∨ t.cache.card < k
  · simp only [show z ∈ (savePrediction s n z hz).cache ∨
      (savePrediction s n z hz).cache.card < k from hh, if_pos] at hv
    have heq := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    exact hO
  · simp only [show ¬ (z ∈ (savePrediction s n z hz).cache ∨
      (savePrediction s n z hz).cache.card < k) from hh, if_false] at hv
    have hf : t.cache.card = k := by have := ht.card_le; simp only [not_or] at hh; omega
    have hzc : z ∉ s.cache := (not_or.mp hh).1
    let u := phaseStart k t
    have hne : (u.cache \ u.marked).Nonempty := phaseStart_candidates_nonempty hk ht hf
    have hOu : ChainPredictionOrder σ h u := phaseStart_chainPredictionOrder σ h k hOt
    have hBt : ChainBookkeeping t :=
      ⟨hs.bookkeeping.lengths, hs.bookkeeping.future_empty, hs.bookkeeping.current_empty⟩
    have hBu : ChainBookkeeping u := phaseStart_chainBookkeeping k hBt
    by_cases hc : z ∉ u.stale
    · rw [if_pos hc] at hv
      have heq := (PMF.mem_support_pure_iff _ _).mp hv
      subst v
      exact clean_eviction_predictionOrder σ h hOu hBu z _
    · rw [if_neg hc] at hv
      have hzS : z ∈ u.stale := not_not.mp hc
      obtain ⟨_, hreset, hzold⟩ := stale_miss_no_reset k s n z hz hzc hzS
      have hu : u = t := hreset
      by_cases hr : (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ)
      · rw [if_pos hr] at hv
        have heq := (PMF.mem_support_pure_iff _ _).mp hv
        subst v
        have he := (htb (staleState u z) hne).1
        rw [hu] at he
        rw [hreset]
        exact stale_eviction_predictionOrder σ h hO hTail hP hE hzold hzc he hz
      · rw [if_neg hr] at hv
        obtain ⟨e, _, rfl⟩ := randomEviction_support (s := staleState u z) hne hv
        exact random_eviction_predictionOrder σ h hOu z e _

lemma prefixRun_chainPredictionOrder {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ) (n : ℕ)
    {s : PMState α} (hs : s ∈ (prefixRun k tb σ h n).support) :
    ChainPredictionOrder σ h s := by
  induction n generalizing s with
  | zero =>
    have he := (PMF.mem_support_pure_iff _ _).mp hs
    subst s
    exact init_chainPredictionOrder σ h
  | succ n ih =>
    obtain ⟨t, ht, hs⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
    unfold indexedStep at hs
    split_ifs at hs with hn
    · exact step_chainPredictionOrder hk tb htb σ h
        (prefixRun_operationalInvariant hk tb htb σ h n ht) (ih ht)
        (prefixRun_representativeTail hk tb htb σ h n ht)
        (prefixRun_knownPrediction hk tb htb σ h hn.le ht)
        (prefixRun_predictionEnvelope hk tb htb σ h n ht) _ _ hs
    · have he := (PMF.mem_support_pure_iff _ _).mp hs
      subst s
      exact ih ht

lemma run_chainPredictionOrder {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {s : PMState α} (hs : s ∈ (run k tb σ h).support) : ChainPredictionOrder σ h s := by
  rw [run_eq_prefixRun] at hs
  exact prefixRun_chainPredictionOrder hk tb htb σ h σ.length hs

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

lemma head_eq_of_sorted_min {β : Type*} [LinearOrder β] {L : List β} {x : β}
    (hL : L.Pairwise (· ≤ ·)) (hx : x ∈ L) (hmin : ∀ y ∈ L, x ≤ y) :
    L.head? = some x := by
  cases L with
  | nil => simp at hx
  | cons y ys =>
    have hxy : x ≤ y := hmin y (by simp)
    have hyx : y ≤ x := by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_rfl
      · exact (List.pairwise_cons.mp hL).1 x hx
    have heq : y = x := le_antisymm hyx hxy
    simp [heq]

lemma nextArrival_eq_of_no_between {α : Type*} [DecidableEq α] (σ : List α)
    (j l : Fin σ.length) (hjl : j < l) (heq : σ.get l = σ.get j)
    (hbetween : ∀ v : Fin σ.length, j < v → v < l → σ.get v ≠ σ.get j) :
    nextArrival σ j = l.val + 1 := by
  let L := (List.finRange σ.length).filter (fun v => decide (j < v ∧ σ.get v = σ.get j))
  have hsorted : L.Pairwise (· ≤ ·) := (List.pairwise_le_finRange _).filter _
  have hl : l ∈ L := by
    apply List.mem_filter.mpr
    exact ⟨by simp, by simpa only [decide_eq_true_eq] using And.intro hjl heq⟩
  have hmin : ∀ v ∈ L, l ≤ v := by
    intro v hv
    have hv' : j < v ∧ σ.get v = σ.get j := by simpa [L] using hv
    by_contra h
    exact hbetween v hv'.1 (lt_of_not_ge h) hv'.2
  have hh := head_eq_of_sorted_min hsorted hl hmin
  change (L.head?.map (fun v => v.val + 1)).getD (σ.length + 1) = l.val + 1
  rw [hh]
  rfl

lemma nextArrival_bounds {α : Type*} [DecidableEq α] (σ : List α) (j : Fin σ.length) :
    j.val + 1 < nextArrival σ j ∧ nextArrival σ j ≤ σ.length + 1 := by
  let L := (List.finRange σ.length).filter (fun v => decide (j < v ∧ σ.get v = σ.get j))
  change j.val + 1 < (L.head?.map (fun v => v.val + 1)).getD (σ.length + 1) ∧
    (L.head?.map (fun v => v.val + 1)).getD (σ.length + 1) ≤ σ.length + 1
  cases hh : L.head? with
  | none => simp only [Option.map_none, Option.getD_none]; have := j.isLt; omega
  | some q =>
    obtain ⟨R, hR⟩ := List.head?_eq_some_iff.mp hh
    have hq : q ∈ L := by rw [hR]; simp
    have hq' : j < q ∧ σ.get q = σ.get j := by simpa [L] using hq
    simp only [Option.map_some, Option.getD_some]
    have := q.isLt
    have hjq : j.val < q.val := hq'.1
    omega

lemma nextArrival_return_witness {α : Type*} [DecidableEq α] (σ : List α)
    (j : Fin σ.length) (hreturn : nextArrival σ j ≤ σ.length) :
    ∃ q : Fin σ.length, nextArrival σ j = q.val + 1 ∧ j < q ∧ σ.get q = σ.get j := by
  let L := (List.finRange σ.length).filter (fun v => decide (j < v ∧ σ.get v = σ.get j))
  change (L.head?.map (fun v => v.val + 1)).getD (σ.length + 1) ≤ σ.length at hreturn
  cases hh : L.head? with
  | none => simp [hh] at hreturn
  | some q =>
    obtain ⟨R, hR⟩ := List.head?_eq_some_iff.mp hh
    have hq : q ∈ L := by rw [hR]; simp
    have hq' : j < q ∧ σ.get q = σ.get j := by simpa [L] using hq
    refine ⟨q, ?_, hq'.1, hq'.2⟩
    change (L.head?.map (fun v => v.val + 1)).getD (σ.length + 1) = q.val + 1
    simp [hh]

lemma nextArrival_same_time_same_page {α : Type*} [DecidableEq α] (σ : List α)
    (i j : Fin σ.length) (hi : nextArrival σ i ≤ σ.length)
    (heq : nextArrival σ i = nextArrival σ j) : σ.get i = σ.get j := by
  obtain ⟨u, hu, _, hui⟩ := nextArrival_return_witness σ i hi
  obtain ⟨v, hv, _, hvj⟩ := nextArrival_return_witness σ j (by omega)
  have huv : u = v := Fin.ext (by omega)
  exact hui.symm.trans (by simpa [huv] using hvj)

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

lemma nextArrival_gt_prefix {α : Type*} [DecidableEq α] (σ : List α)
    (j : Fin σ.length) (n : ℕ) (hn : n ≤ σ.length)
    (hno : ∀ l : Fin σ.length, j < l → l.val < n → σ.get l ≠ σ.get j) :
    n < nextArrival σ j := by
  by_contra h
  have hle : nextArrival σ j ≤ n := Nat.le_of_not_gt h
  obtain ⟨l, hl, hjl, heq⟩ := nextArrival_return_witness σ j (hle.trans hn)
  exact hno l hjl (by omega) heq

lemma knownPrediction_return_label {α : Type*} [DecidableEq α]
    (σ : List α) (h : Fin σ.length → ℝ) {n : ℕ} (hn : n < σ.length)
    {s : PMState α} (hp : KnownPrediction σ h n s)
    {z : α} (hz : z ∈ s.cache ∪ s.stale) (hzn : σ.get ⟨n, hn⟩ = z) :
    ∃ j : Fin σ.length, s.predIdx z = j.val ∧ s.pred z = h j ∧
      nextArrival σ j = n + 1 := by
  obtain ⟨j, hj, hjz, hidx, hpred, hlast⟩ := hp z hz
  refine ⟨j, hidx, hpred, ?_⟩
  apply nextArrival_eq_of_no_between σ j ⟨n, hn⟩ hj
  · exact hzn.trans hjz.symm
  · intro l hjl hln
    simpa only [hjz] using hlast l hjl hln

lemma knownPrediction_candidate_label_gt {α : Type*} [DecidableEq α]
    (σ : List α) (h : Fin σ.length → ℝ) {n : ℕ} (hn : n < σ.length)
    {s : PMState α} (hp : KnownPrediction σ h n s)
    {x : α} (hx : x ∈ s.cache ∪ s.stale) (hxne : σ.get ⟨n, hn⟩ ≠ x) :
    ∃ j : Fin σ.length, s.predIdx x = j.val ∧ s.pred x = h j ∧
      n + 1 < nextArrival σ j := by
  obtain ⟨j, hj, hjx, hidx, hpred, hlast⟩ := hp x hx
  refine ⟨j, hidx, hpred, nextArrival_gt_prefix σ j (n + 1) (by omega) ?_⟩
  intro l hjl hln
  by_cases hlt : l.val < n
  · simpa only [hjx] using hlast l hjl hlt
  · have hle : l = ⟨n, hn⟩ := Fin.ext (by change l.val = n; omega)
    simpa only [hle, hjx] using hxne

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

def ChainChronology (σ : List α) (s : PMState α) : Prop :=
  ∀ p, (indexFamily s p).Pairwise (fun a b => labelAt σ a < labelAt σ b)

theorem init_chainChronology (σ : List α) : ChainChronology σ (initState α) := by
  intro p
  simp [indexFamily, initState]

theorem clean_eviction_chronology (σ : List α) {s : PMState α}
    (hs : ChainChronology σ s) (hb : ChainBookkeeping s) (z e : α) :
    ChainChronology σ (evictInto (cleanState s) z (s.clean + 1) e) := by
  have hi := evictInto_indexFamily (cleanState s) z (s.clean + 1) e
  change indexFamily (evictInto (cleanState s) z (s.clean + 1) e) =
    Function.update (indexFamily s) (s.phase, s.clean + 1)
      (indexFamily s (s.phase, s.clean + 1) ++ [s.predIdx e]) at hi
  intro p
  rw [hi]
  by_cases hp : p = (s.phase, s.clean + 1)
  · subst p
    rw [Function.update_self, hb.current_empty _ (Or.inl (Nat.lt_succ_self _))]
    simp
  · rw [Function.update_of_ne hp]
    exact hs p

theorem stale_eviction_chronology (σ : List α) (h : Fin σ.length → ℝ)
    {n : ℕ} (hn : n < σ.length) {s : PMState α}
    (hc : ChainChronology σ s) (ht : RepresentativeTail s)
    (hp : KnownPrediction σ h n s)
    (hzS : σ.get ⟨n, hn⟩ ∈ s.stale) (hzC : σ.get ⟨n, hn⟩ ∉ s.cache)
    {e : α} (he : e ∈ s.cache) :
    let z := σ.get ⟨n, hn⟩
    let u := savePrediction s n z (h ⟨n, hn⟩)
    ChainChronology σ (evictInto (staleState u z) z (s.chainOf z) e) := by
  dsimp only
  let z := σ.get ⟨n, hn⟩
  let u := savePrediction s n z (h ⟨n, hn⟩)
  have hez : e ≠ z := ne_of_mem_of_not_mem he hzC
  obtain ⟨j, hjidx, _, hjlabel⟩ := knownPrediction_return_label σ h hn hp
    (Finset.mem_union_right _ hzS) rfl
  obtain ⟨l, hlidx, _, hllabel⟩ := knownPrediction_candidate_label_gt σ h hn hp
    (Finset.mem_union_left _ he) hez.symm
  have hlast := ht z (Finset.mem_sdiff.mpr ⟨hzS, hzC⟩)
  have hlabels : labelAt σ (s.predIdx z) < labelAt σ (s.predIdx e) := by
    rw [hjidx, hlidx, labelAt_fin, labelAt_fin, hjlabel]
    exact hllabel
  have hi := evictInto_indexFamily (staleState u z) z (s.chainOf z) e
  change indexFamily (evictInto (staleState u z) z (s.chainOf z) e) =
    Function.update (indexFamily s) (s.phase, s.chainOf z)
      (indexFamily s (s.phase, s.chainOf z) ++ [Function.update s.predIdx z n e]) at hi
  rw [Function.update_of_ne hez] at hi
  intro p
  rw [hi]
  by_cases hpk : p = (s.phase, s.chainOf z)
  · subst p
    rw [Function.update_self]
    exact pairwise_strict_append_last (labelAt σ) (hc _) hlast hlabels
  · rw [Function.update_of_ne hpk]
    exact hc p

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh
variable {α : Type*} [DecidableEq α]

theorem step_chainChronology {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {n : ℕ} (hn : n < σ.length) {s : PMState α}
    (hs : OperationalInvariant k s) (hc : ChainChronology σ s)
    (htail : RepresentativeTail s) (hknown : KnownPrediction σ h n s)
    {v : PMState α}
    (hv : v ∈ (step k tb s n (σ.get ⟨n, hn⟩) (h ⟨n, hn⟩)).support) :
    ChainChronology σ v := by
  let z := σ.get ⟨n, hn⟩
  let t := savePrediction s n z (h ⟨n, hn⟩)
  let u := phaseStart k t
  rw [step_factored] at hv
  change v ∈ (if z ∈ t.cache ∨ t.cache.card < k then PMF.pure (hitOrFill t z)
    else if z ∉ u.stale then PMF.pure (evictInto (cleanState u) z (u.clean + 1) (tb (cleanState u)))
    else if (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ) then
      PMF.pure (evictInto (staleState u z) z (u.chainOf z) (tb (staleState u z)))
    else randomEviction (staleState u z) z (u.chainOf z)).support at hv
  by_cases hh : z ∈ t.cache ∨ t.cache.card < k
  · rw [if_pos hh] at hv
    have he := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    exact hc
  · rw [if_neg hh] at hv
    have ht : CacheInvariant k t := save_cacheInvariant hs.cache n z _
    have hf : t.cache.card = k := by have := ht.card_le; simp only [not_or] at hh; omega
    have hne := phaseStart_candidates_nonempty hk ht hf
    have hzC : z ∉ s.cache := (not_or.mp hh).1
    by_cases hzS : z ∉ u.stale
    · rw [if_pos hzS] at hv
      have he := (PMF.mem_support_pure_iff _ _).mp hv
      subst v
      have hcu : ChainChronology σ u := by
        dsimp [u, phaseStart]
        split_ifs <;> exact hc
      have hbt : ChainBookkeeping t := ⟨hs.bookkeeping.lengths,
        hs.bookkeeping.future_empty, hs.bookkeeping.current_empty⟩
      exact clean_eviction_chronology σ hcu (phaseStart_chainBookkeeping k hbt) z _
    · rw [if_neg hzS] at hv
      obtain ⟨_, hu, hzold⟩ := stale_miss_no_reset k s n z (h ⟨n, hn⟩) hzC (not_not.mp hzS)
      have hut : u = t := hu
      rw [hut] at hv
      have hnet : (t.cache \ t.marked).Nonempty := by change (u.cache \ u.marked).Nonempty at hne; rw [hut] at hne; exact hne
      by_cases hr : (t.chainLen t.phase (t.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ)
      · rw [if_pos hr] at hv
        have he := (PMF.mem_support_pure_iff _ _).mp hv
        subst v
        exact stale_eviction_chronology σ h hn hc htail hknown hzold hzC
          (Finset.mem_sdiff.mp (htb (staleState t z) hnet).1).1
      · rw [if_neg hr] at hv
        obtain ⟨e, he, rfl⟩ := randomEviction_support (s := staleState t z) hnet hv
        exact stale_eviction_chronology σ h hn hc htail hknown hzold hzC
          (Finset.mem_sdiff.mp he).1

theorem prefixRun_chainChronology {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {n : ℕ} (hn : n ≤ σ.length) {s : PMState α}
    (hs : s ∈ (prefixRun k tb σ h n).support) : ChainChronology σ s := by
  induction n generalizing s with
  | zero =>
    have he := (PMF.mem_support_pure_iff _ _).mp hs
    subst s
    exact init_chainChronology σ
  | succ n ih =>
    have hnlt : n < σ.length := by omega
    rw [prefixRun_succ tb σ h hnlt] at hs
    obtain ⟨t, ht, hs⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
    exact step_chainChronology hk tb htb σ h hnlt
      (prefixRun_operationalInvariant hk tb htb σ h n ht) (ih (by omega) ht)
      (prefixRun_representativeTail hk tb htb σ h n ht)
      (prefixRun_knownPrediction hk tb htb σ h (by omega) ht) hs

theorem run_chainChronology {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {s : PMState α} (hs : s ∈ (run k tb σ h).support) : ChainChronology σ s := by
  rw [run_eq_prefixRun] at hs
  exact prefixRun_chainChronology hk tb htb σ h le_rfl hs
end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem cached_index_lt {σ : List α} {h : Fin σ.length → ℝ} {n : ℕ} {s : PMState α}
    (hp : CachedPrediction σ h n s) {z : α} (hz : z ∈ s.cache) : s.predIdx z < n := by
  obtain ⟨j, hj, _, hi, _, _⟩ := hp z hz
  exact hi.symm ▸ hj

omit [DecidableEq α] in
theorem cached_index_injective {σ : List α} {h : Fin σ.length → ℝ} {n : ℕ} {s : PMState α}
    (hp : CachedPrediction σ h n s) {x y : α} (hx : x ∈ s.cache) (hy : y ∈ s.cache)
    (he : s.predIdx x = s.predIdx y) : x = y := by
  obtain ⟨i, _, hix, hi, _, _⟩ := hp x hx
  obtain ⟨j, _, hjy, hj, _, _⟩ := hp y hy
  have hij : i = j := Fin.ext (hi.symm.trans (he.trans hj))
  exact hix.symm.trans ((congrArg σ.get hij).trans hjy)

structure NativeLedger (n : ℕ) (s : PMState α) : Prop where
  valid : IndexFamilyValid n (indexFamily s)
  cached_fresh : ∀ z ∈ s.cache, ∀ p, s.predIdx z ∉ indexFamily s p

omit [DecidableEq α] in
theorem nativeLedger_init : NativeLedger 0 (initState α) := by
  constructor
  · exact IndexFamilyValid.empty 0
  · intro z hz
    simp [initState] at hz

theorem nativeLedger_step {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {n : ℕ} (hn : n < σ.length) {s : PMState α} (hs : CacheInvariant k s)
    (hp : CachedPrediction σ h n s) (hL : NativeLedger n s)
    {v : PMState α} (hv : v ∈ (step k tb s n (σ.get ⟨n, hn⟩) (h ⟨n, hn⟩)).support) :
    NativeLedger (n + 1) v := by
  obtain ⟨_, hidx, _, _⟩ := step_observations hk tb hs n _ _ hv
  rcases step_ledger_cases hk tb htb hs n _ _ hv with ⟨hi, hc⟩ | ⟨_, e, he, q, hc, hi⟩
  · constructor
    · rw [hi]
      exact hL.valid.mono (Nat.le_succ n)
    · intro z hz p hm
      by_cases hz0 : z = σ.get ⟨n, hn⟩
      · subst z
        rw [hi] at hm
        have hb := hL.valid.bounded p _ hm
        rw [hidx, Function.update_self] at hb
        omega
      · rw [hc] at hz
        have hzs := (Finset.mem_insert.mp hz).resolve_left hz0
        rw [hi, hidx, Function.update_of_ne hz0] at hm
        exact hL.cached_fresh z hzs p hm
  · have hj : s.predIdx e < n := cached_index_lt hp he
    have hnew : IndexFamilyValid n (indexFamily v) := by
      rw [hi]
      exact hL.valid.append q _ hj (hL.cached_fresh e he)
    constructor
    · exact hnew.mono (Nat.le_succ n)
    · intro z hz p hm
      by_cases hz0 : z = σ.get ⟨n, hn⟩
      · subst z
        have hb := hnew.bounded p _ hm
        rw [hidx, Function.update_self] at hb
        omega
      · rw [hc] at hz
        have hzE := (Finset.mem_insert.mp hz).resolve_left hz0
        obtain ⟨hze, hzs⟩ := Finset.mem_erase.mp hzE
        rw [hi, hidx, Function.update_of_ne hz0, mem_update_append] at hm
        rcases hm with hm | ⟨_, hm⟩
        · exact hL.cached_fresh z hzs p hm
        · exact hze (cached_index_injective hp hzs he hm)

theorem prefixRun_nativeLedger {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {n : ℕ} (hn : n ≤ σ.length) {s : PMState α}
    (hs : s ∈ (prefixRun k tb σ h n).support) : NativeLedger n s := by
  induction n generalizing s with
  | zero =>
    have he := (PMF.mem_support_pure_iff _ _).mp hs
    subst s
    exact nativeLedger_init
  | succ n ih =>
    have hnlt : n < σ.length := by omega
    rw [prefixRun_succ tb σ h hnlt] at hs
    obtain ⟨t, ht, hs⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
    exact nativeLedger_step hk tb htb σ h hnlt
      (prefixRun_cacheInvariant hk tb htb σ h n ht)
      (prefixRun_cachedPrediction hk tb htb σ h (by omega) ht) (ih (by omega) ht) hs

theorem run_nativeLedger {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {s : PMState α} (hs : s ∈ (run k tb σ h).support) : NativeLedger σ.length s := by
  rw [run_eq_prefixRun] at hs
  exact prefixRun_nativeLedger hk tb htb σ h le_rfl hs

end CachingML.PredMarker.PMFresh
end


section

open Set

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

lemma nonrandom_chain_bound {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {ℓ : ℝ → ℝ → ℝ} {S : ℝ → ℝ}
    (hℓ : ∀ x y, 0 ≤ ℓ x y) (hc : ConcaveOn ℝ (Ici 0) S)
    (h0 : ContinuousWithinAt S (Ici 0) 0)
    (hsp : ∀ m : ℝ, 0 ≤ m → ∃ t : ℕ, spread ℓ m = t ∧ (t : ℝ) ≤ S m)
    {n : ℕ} (hn : n ≤ σ.length) {s : PMState α}
    (hs : s ∈ (prefixRun k tb σ h n).support) (p : ℕ × ℕ)
    (hp : p ∉ s.randomChains) :
    (s.chainLen p.1 p.2 : ℝ) ≤ S (chainError ℓ σ h s p.1 p.2) := by
  have ho := prefixRun_operationalInvariant hk tb htb σ h n hs
  have hvalid := (prefixRun_nativeLedger hk tb htb σ h hn hs).valid
  have hchron := prefixRun_chainChronology hk tb htb σ h hn hs
  have hpred := prefixRun_chainPredictionOrder hk tb htb σ h n hs
  have hb := bounded_ordered_indices_majorant σ h (indexFamily s p)
    (fun j hj => (hvalid.bounded p j hj).trans_le hn) (hchron p) (hpred p hp)
    hℓ hc h0 hsp
  have hlen := ho.bookkeeping.lengths p
  change s.chainLen p.1 p.2 = (indexFamily s p).length at hlen
  rw [hlen]
  exact hb

lemma run_nonrandom_chain_bound {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {ℓ : ℝ → ℝ → ℝ} {S : ℝ → ℝ}
    (hℓ : ∀ x y, 0 ≤ ℓ x y) (hc : ConcaveOn ℝ (Ici 0) S)
    (h0 : ContinuousWithinAt S (Ici 0) 0)
    (hsp : ∀ m : ℝ, 0 ≤ m → ∃ t : ℕ, spread ℓ m = t ∧ (t : ℝ) ≤ S m)
    {s : PMState α} (hs : s ∈ (run k tb σ h).support)
    (p : ℕ × ℕ) (hp : p ∉ s.randomChains) :
    (s.chainLen p.1 p.2 : ℝ) ≤ S (chainError ℓ σ h s p.1 p.2) := by
  rw [run_eq_prefixRun] at hs
  exact nonrandom_chain_bound hk tb htb σ h hℓ hc h0 hsp le_rfl hs p hp

end CachingML.PredMarker.PMFresh
end


section

open Set
open scoped BigOperators

namespace CachingML.PredMarker.PMFresh

def chainBudget (S : ℝ → ℝ) (H : ℝ) (x : ℝ) : ℝ := min (1 + 2 * S x) (2 * H)

lemma chainBudget_concave {S : ℝ → ℝ} (H : ℝ) (hS : ConcaveOn ℝ (Ici 0) S) :
    ConcaveOn ℝ (Ici 0) (chainBudget S H) := by
  refine ⟨convex_Ici _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hc := hS.2 hx hy ha hb hab
  simp only [smul_eq_mul] at hc ⊢
  change a * min (1 + 2 * S x) (2 * H) + b * min (1 + 2 * S y) (2 * H) ≤
    min (1 + 2 * S (a * x + b * y)) (2 * H)
  apply le_min
  · have h1 := mul_le_mul_of_nonneg_left (min_le_left (1 + 2 * S x) (2 * H)) ha
    have h2 := mul_le_mul_of_nonneg_left (min_le_left (1 + 2 * S y) (2 * H)) hb
    nlinarith
  · have h1 := mul_le_mul_of_nonneg_left (min_le_right (1 + 2 * S x) (2 * H)) ha
    have h2 := mul_le_mul_of_nonneg_left (min_le_right (1 + 2 * S y) (2 * H)) hb
    have heq : (a + b) * H = H := by rw [hab, one_mul]
    nlinarith

lemma chainBudget_monotone {S : ℝ → ℝ} (H : ℝ) (hS : MonotoneOn S (Ici 0)) :
    MonotoneOn (chainBudget S H) (Ici 0) := by
  intro x hx y hy hxy
  apply min_le_min
  · have := hS hx hy hxy
    linarith
  · exact le_rfl

lemma chainBudget_one_le {S : ℝ → ℝ} {H x : ℝ} (hH : 1 ≤ H) (hS : 1 ≤ S x) :
    1 ≤ chainBudget S H x := by
  apply le_min <;> linarith

lemma concave_sum_le_card_mul {g : ℝ → ℝ} (hg : ConcaveOn ℝ (Ici 0) g)
    {n : ℕ} (hn : 0 < n) (e : Fin n → ℝ) (he : ∀ i, 0 ≤ e i) :
    (∑ i, g (e i)) ≤ n * g ((∑ i, e i) / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : (∑ _ : Fin n, (n : ℝ)⁻¹) = 1 := by
    simp [ne_of_gt hnR]
  have h := hg.le_map_sum (t := Finset.univ) (w := fun _ : Fin n => (n : ℝ)⁻¹)
    (p := e) (fun _ _ => inv_nonneg.mpr hnR.le) hw (fun i _ => he i)
  simp only [smul_eq_mul, ← Finset.mul_sum] at h
  have h' := mul_le_mul_of_nonneg_left h hnR.le
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, ne_of_gt hnR] using h'

lemma total_chain_budget {S : ℝ → ℝ} (H : ℝ) (hS : ConcaveOn ℝ (Ici 0) S)
    (hmono : MonotoneOn S (Ici 0)) {n : ℕ} (hn : 0 < n)
    (e : Fin n → ℝ) (he : ∀ i, 0 ≤ e i) {E ε : ℝ}
    (hE : (∑ i, e i) ≤ E) (hε : E ≤ ε * n) :
    (∑ i, chainBudget S H (e i)) ≤ n * chainBudget S H ε := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : 0 ≤ ∑ i, e i := Finset.sum_nonneg (fun i _ => he i)
  have hε0 : 0 ≤ ε := by nlinarith
  apply (concave_sum_le_card_mul (chainBudget_concave H hS) hn e he).trans
  apply mul_le_mul_of_nonneg_left _ hnR.le
  apply chainBudget_monotone H hmono (div_nonneg hsum hnR.le) hε0
  exact (div_le_iff₀ hnR).mpr (hE.trans hε)

lemma stopped_budget_bound {H q E : ℝ} {S : ℝ → ℝ}
    (hq : q ≤ H) (hH : H < q + 1) (hE : q ≤ S E) :
    q + H ≤ chainBudget S H E := by
  apply le_min <;> linarith

end CachingML.PredMarker.PMFresh
end


section

open Set

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

lemma chainError_nonneg (ℓ : ℝ → ℝ → ℝ) (hℓ : ∀ x y, 0 ≤ ℓ x y)
    (σ : List α) (h : Fin σ.length → ℝ) (s : PMState α) (p : ℕ × ℕ) :
    0 ≤ chainError ℓ σ h s p.1 p.2 := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  exact lossAt_nonneg ℓ hℓ σ h j

lemma nonrandom_prefix_majorant_of_continuation {k : ℕ} (hk : 1 ≤ k)
    (tb : PMState α → α) (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {ℓ : ℝ → ℝ → ℝ} {S : ℝ → ℝ}
    (hℓ : ∀ x y, 0 ≤ ℓ x y) (hc : ConcaveOn ℝ (Ici 0) S)
    (h0 : ContinuousWithinAt S (Ici 0) 0)
    (hsp : ∀ m : ℝ, 0 ≤ m → ∃ t : ℕ, spread ℓ m = t ∧ (t : ℝ) ≤ S m)
    {n : ℕ} (hn : n ≤ σ.length) {s : PMState α}
    (hs : s ∈ (prefixRun k tb σ h n).support) (p : ℕ × ℕ)
    (hp : p ∉ s.randomChains) (l : List ℕ) {v : PMState α}
    (hv : v ∈ (kernelRun (fun t i => indexedStep k tb σ h i t) s l).support) :
    (s.chainLen p.1 p.2 : ℝ) ≤ S (chainError ℓ σ h v p.1 p.2) := by
  apply (nonrandom_chain_bound hk tb htb σ h hℓ hc h0 hsp hn hs p hp).trans
  exact majorant_monotone hc hsp (chainError_nonneg ℓ hℓ σ h s p)
    (chainError_nonneg ℓ hℓ σ h v p)
    (continuation_chainError_mono hk tb htb ℓ hℓ σ h l
      (prefixRun_cacheInvariant hk tb htb σ h n hs) hv p)

end CachingML.PredMarker.PMFresh
end


section

open Set

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

lemma first_switch_length_floor {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ) (n : ℕ)
    {s : PMState α} (hs : s ∈ (prefixRun k tb σ h n).support)
    (p : ℕ × ℕ) (hp : p ∉ s.randomChains)
    (hnext : ¬ (s.chainLen p.1 p.2 + 1 : ℕ) ≤ (harmonic k : ℝ)) :
    s.chainLen p.1 p.2 = Nat.floor (harmonic k : ℝ) := by
  apply Eq.symm
  apply (Nat.floor_eq_iff (harmonic_real_nonneg k)).mpr
  refine ⟨prefixRun_nonrandomLengthCap hk tb htb σ h n hs p hp, ?_⟩
  simpa only [Nat.cast_add, Nat.cast_one] using lt_of_not_ge hnext

lemma nonrandom_terminal_budget {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {ℓ : ℝ → ℝ → ℝ} {S : ℝ → ℝ}
    (hℓ : ∀ x y, 0 ≤ ℓ x y) (hc : ConcaveOn ℝ (Ici 0) S)
    (h0 : ContinuousWithinAt S (Ici 0) 0)
    (hsp : ∀ m : ℝ, 0 ≤ m → ∃ t : ℕ, spread ℓ m = t ∧ (t : ℝ) ≤ S m)
    {n : ℕ} (hn : n ≤ σ.length) {s : PMState α}
    (hs : s ∈ (prefixRun k tb σ h n).support) (p : ℕ × ℕ)
    (hp : p ∉ s.randomChains) :
    (s.chainLen p.1 p.2 : ℝ) ≤ chainBudget S (harmonic k) (chainError ℓ σ h s p.1 p.2) := by
  have hS := nonrandom_chain_bound hk tb htb σ h hℓ hc h0 hsp hn hs p hp
  have hH := prefixRun_nonrandomLengthCap hk tb htb σ h n hs p hp
  change (s.chainLen p.1 p.2 : ℝ) ≤ (harmonic k : ℝ) at hH
  have hN : (0 : ℝ) ≤ s.chainLen p.1 p.2 := Nat.cast_nonneg _
  apply le_min <;> linarith

lemma first_switch_continuation_budget {k : ℕ} (hk : 1 ≤ k)
    (tb : PMState α → α) (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {ℓ : ℝ → ℝ → ℝ} {S : ℝ → ℝ}
    (hℓ : ∀ x y, 0 ≤ ℓ x y) (hc : ConcaveOn ℝ (Ici 0) S)
    (h0 : ContinuousWithinAt S (Ici 0) 0)
    (hsp : ∀ m : ℝ, 0 ≤ m → ∃ t : ℕ, spread ℓ m = t ∧ (t : ℝ) ≤ S m)
    {n : ℕ} (hn : n ≤ σ.length) {s : PMState α}
    (hs : s ∈ (prefixRun k tb σ h n).support) (p : ℕ × ℕ)
    (hp : p ∉ s.randomChains)
    (hnext : ¬ (s.chainLen p.1 p.2 + 1 : ℕ) ≤ (harmonic k : ℝ))
    (l : List ℕ) {v : PMState α}
    (hv : v ∈ (kernelRun (fun t i => indexedStep k tb σ h i t) s l).support) :
    (s.chainLen p.1 p.2 : ℝ) + harmonic k ≤
      chainBudget S (harmonic k) (chainError ℓ σ h v p.1 p.2) := by
  apply stopped_budget_bound (prefixRun_nonrandomLengthCap hk tb htb σ h n hs p hp)
  · simpa only [lengthFamily, Nat.cast_add, Nat.cast_one] using lt_of_not_ge hnext
  · exact nonrandom_prefix_majorant_of_continuation hk tb htb σ h hℓ hc h0 hsp hn hs p hp l hv

end CachingML.PredMarker.PMFresh
end


section

open Set
open scoped ENNReal

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

noncomputable def activeChainBudget (ℓ : ℝ → ℝ → ℝ) (S : ℝ → ℝ) (k : ℕ)
    (σ : List α) (h : Fin σ.length → ℝ) (p : ℕ × ℕ) (s : PMState α) : ℝ≥0∞ :=
  if indexFamily s p = [] then 0 else
    ENNReal.ofReal (chainBudget S (harmonic k) (chainError ℓ σ h s p.1 p.2))

lemma active_chain_expectation_from_native_suffix {k : ℕ} (hk : 1 ≤ k)
    (tb : PMState α → α) (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {ℓ : ℝ → ℝ → ℝ} {S : ℝ → ℝ}
    (hℓ : ∀ x y, 0 ≤ ℓ x y) (hc : ConcaveOn ℝ (Ici 0) S)
    (h0 : ContinuousWithinAt S (Ici 0) 0)
    (hsp : ∀ m : ℝ, 0 ≤ m → ∃ t : ℕ, spread ℓ m = t ∧ (t : ℝ) ≤ S m)
    (p : ℕ × ℕ)
    (htail : ∀ (n : ℕ) (hn : n < σ.length) (s : PMState α),
      s ∈ (prefixRun k tb σ h n).support → p ∉ s.randomChains →
      nativeRandomKey k s n (σ.get ⟨n, hn⟩) (h ⟨n, hn⟩) = some p →
      pmExpectation (kernelRun (fun t i => indexedStep k tb σ h i t) s
        ((List.range σ.length).drop n)) (fun v => (v.chainLen p.1 p.2 : ℝ≥0∞)) ≤
        ENNReal.ofReal ((s.chainLen p.1 p.2 : ℝ) + harmonic k)) :
    pmExpectation (run k tb σ h) (fun s => (s.chainLen p.1 p.2 : ℝ≥0∞)) ≤
      pmExpectation (run k tb σ h)
        (activeChainBudget ℓ S k σ h p) := by
  let f := fun t i => indexedStep k tb σ h i t
  let stop := nativeSwitchStop k σ h p
  have hrun : run k tb σ h = kernelRun f (initState α) (List.range σ.length) := by
    rw [kernelRun_range_prefixRun, run_eq_prefixRun]
  rw [hrun]
  apply firstHitRun_expectation_compare f stop (List.range σ.length) (initState α)
  intro q hq
  obtain ⟨n, hn, hprefix, hrest⟩ := firstHitRun_actual_prefix k tb σ h stop hq
  have hsupport := native_firstSwitch_support hk tb htb σ h p (List.range σ.length)
    (init_cacheInvariant k) (by simp [initState]) hq
  have hp := hsupport.2.1
  rcases hsupport.2.2 with hnil | ⟨i, r, hir, hi, hkey⟩
  · have hb := nonrandom_terminal_budget hk tb htb σ h hℓ hc h0 hsp hn hprefix p hp
    rw [hnil]
    simp only [kernelRun, pmExpectation_pure]
    by_cases he : indexFamily q.1 p = []
    · have hlen := (prefixRun_operationalInvariant hk tb htb σ h n hprefix).bookkeeping.lengths p
      have hzero : q.1.chainLen p.1 p.2 = 0 := by
        change q.1.chainLen p.1 p.2 = (indexFamily q.1 p).length at hlen
        simpa only [he, List.length_nil] using hlen
      simp [activeChainBudget, he, hzero]
    · simp only [activeChainBudget, if_neg he]
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hb
  · have hhead := range_drop_head (hrest.symm.trans hir)
    have hin : i = n := hhead.2
    subst i
    have hbound := htail n hhead.1 q.1 hprefix hp hkey
    rw [← hrest] at hbound
    apply hbound.trans
    have hnext := (nativeRandomKey_some hkey).2.2.2.2
    calc
      ENNReal.ofReal ((q.1.chainLen p.1 p.2 : ℝ) + harmonic k) =
          pmExpectation (kernelRun f q.1 q.2)
            (fun _ => ENNReal.ofReal ((q.1.chainLen p.1 p.2 : ℝ) + harmonic k)) :=
        (pmExpectation_const _ _).symm
      _ ≤ _ := by
        apply pmExpectation_mono
        intro v hv
        have hpos : 0 < q.1.chainLen p.1 p.2 := by
          have hH := harmonic_real_one_le hk
          by_contra hneg
          have he : q.1.chainLen p.1 p.2 = 0 := by omega
          simp only [he, Nat.zero_add, Nat.cast_one] at hnext
          exact hnext hH
        have hnonempty : indexFamily q.1 p ≠ [] := by
          intro he
          have hlen := (prefixRun_operationalInvariant hk tb htb σ h n hprefix).bookkeeping.lengths p
          change q.1.chainLen p.1 p.2 = (indexFamily q.1 p).length at hlen
          rw [he, List.length_nil] at hlen
          omega
        have hvnonempty : indexFamily v p ≠ [] := by
          intro he
          obtain ⟨tail, ht⟩ := (continuation_index_prefix hk tb htb σ h q.2
            (prefixRun_cacheInvariant hk tb htb σ h n hprefix) hv).2 p
          exact hnonempty (List.append_eq_nil_iff.mp (ht.trans he)).1
        simp only [activeChainBudget, if_neg hvnonempty]
        exact ENNReal.ofReal_le_ofReal
          (first_switch_continuation_budget hk tb htb σ h hℓ hc h0 hsp hn hprefix p hp hnext q.2 hv)

end CachingML.PredMarker.PMFresh
end


section

open Set

namespace CachingML.PredMarker.PMFresh

lemma sum_fin_get_map {α : Type*} (L : List α) (f : α → ℝ) :
    (∑ i : Fin L.length, f (L.get i)) = (L.map f).sum := by
  rw [← List.sum_ofFn]
  congr 1
  change List.ofFn (f ∘ L.get) = _
  rw [← List.map_ofFn, List.ofFn_get]

lemma list_total_chain_budget {S : ℝ → ℝ} (H : ℝ)
    (hS : ConcaveOn ℝ (Ici 0) S) (hmono : MonotoneOn S (Ici 0))
    (L : List ℝ) (hn : 0 < L.length) (he : ∀ x ∈ L, 0 ≤ x) {E ε : ℝ}
    (hE : L.sum ≤ E) (hε : E ≤ ε * L.length) :
    (L.map (chainBudget S H)).sum ≤ L.length * chainBudget S H ε := by
  have hi : ∀ i : Fin L.length, 0 ≤ L.get i := fun i => he _ (List.get_mem _ _)
  have hsum : (∑ i : Fin L.length, L.get i) = L.sum := by
    simp
  have hh := total_chain_budget H hS hmono hn (fun i : Fin L.length => L.get i) hi
    (by rwa [hsum]) hε
  rwa [sum_fin_get_map] at hh

lemma active_budget_with_singletons {ι : Type*} [DecidableEq ι]
    {S : ℝ → ℝ} (H : ℝ) (hS : ConcaveOn ℝ (Ici 0) S)
    (hmono : MonotoneOn S (Ici 0)) (hzero : 1 ≤ chainBudget S H 0)
    (m : ℕ) (A : Finset ι) (e : ι → ℝ) (he : ∀ i ∈ A, 0 ≤ e i)
    (hn : 0 < m + A.card) {E ε : ℝ}
    (hE : (∑ i ∈ A, e i) ≤ E) (hε : E ≤ ε * (m + A.card : ℕ)) :
    (m : ℝ) + (∑ i ∈ A, chainBudget S H (e i)) ≤
      (m + A.card : ℕ) * chainBudget S H ε := by
  let L := List.replicate m (0 : ℝ) ++ A.toList.map e
  have hlen : L.length = m + A.card := by simp [L]
  have hnonneg : ∀ x ∈ L, 0 ≤ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have hx0 : x = 0 := (List.mem_replicate.mp hx).2
      subst x
      exact le_rfl
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact he i (Finset.mem_toList.mp hi)
  have hsum : L.sum = ∑ i ∈ A, e i := by simp [L, Finset.sum_map_toList]
  have hbound := list_total_chain_budget H hS hmono L (by omega) hnonneg
    (hsum.trans_le hE) (by rwa [hlen])
  have hbudget : (L.map (chainBudget S H)).sum =
      m * chainBudget S H 0 + ∑ i ∈ A, chainBudget S H (e i) := by
    simp [L, List.map_map, Finset.sum_map_toList, Function.comp_def]
  rw [hbudget, hlen] at hbound
  have hm : (m : ℝ) ≤ m * chainBudget S H 0 := by
    simpa using mul_le_mul_of_nonneg_left hzero (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  exact (add_le_add hm le_rfl).trans hbound

end CachingML.PredMarker.PMFresh
end


section

open scoped BigOperators ENNReal

namespace CachingML.PredMarker.PMFresh

lemma IndexFamilyValid.finite_support {ι : Type*} {n : ℕ} {I : ι → List ℕ}
    (h : IndexFamilyValid n I) : Set.Finite {p | I p ≠ []} := by
  classical
  let S : Set ι := {p | I p ≠ []}
  have hex : ∀ p : S, ∃ j, j ∈ I p.val := fun p => List.exists_mem_of_ne_nil _ p.property
  choose j hj using hex
  let f : S → Fin n := fun p => ⟨j p, h.bounded p.val _ (hj p)⟩
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    by_contra hne
    have heq : j p = j q := congrArg Fin.val hpq
    exact h.separate p.val q.val hne (j p) (hj p) (by simpa [heq] using hj q)
  have : Finite S := Finite.of_injective f hf
  exact Set.toFinite S

noncomputable def indexLengthTotal {ι : Type*} (I : ι → List ℕ) : ℝ≥0∞ :=
  ∑' p, ((I p).length : ℝ≥0∞)

lemma indexLengthTotal_empty {ι : Type*} : indexLengthTotal (fun _ : ι => []) = 0 := by
  simp [indexLengthTotal]

lemma indexLengthTotal_append {ι : Type*} [DecidableEq ι] (I : ι → List ℕ) (p : ι) (j : ℕ) :
    indexLengthTotal (Function.update I p (I p ++ [j])) = indexLengthTotal I + 1 := by
  have heq : (fun q => ((Function.update I p (I p ++ [j]) q).length : ℝ≥0∞)) =
      fun q => ((I q).length : ℝ≥0∞) + if q = p then 1 else 0 := by
    funext q
    by_cases hq : q = p
    · subst q; simp
    · simp [hq]
  unfold indexLengthTotal
  rw [heq, ENNReal.tsum_add]
  simp

lemma indexLengthTotal_eq_sum {ι : Type*} [DecidableEq ι] (I : ι → List ℕ)
    (keys : Finset ι) (hkeys : ∀ p, I p ≠ [] → p ∈ keys) :
    indexLengthTotal I = ∑ p ∈ keys, ((I p).length : ℝ≥0∞) := by
  apply tsum_eq_sum
  intro p hp
  have hempty : I p = [] := by by_contra h; exact hp (hkeys p h)
  simp [hempty]

lemma IndexFamilyValid.length_total_ne_top {ι : Type*} {n : ℕ} {I : ι → List ℕ}
    (h : IndexFamilyValid n I) : indexLengthTotal I ≠ ⊤ := by
  classical
  let keys := h.finite_support.toFinset
  have hkeys : ∀ p, I p ≠ [] → p ∈ keys := by
    intro p hp
    exact h.finite_support.mem_toFinset.mpr hp
  rw [indexLengthTotal_eq_sum I keys hkeys]
  simp

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

def indexSupport {ι : Type*} (I : ι → List ℕ) : Set ι := {p | I p ≠ []}

lemma indexSupport_append {ι : Type*} [DecidableEq ι] (I : ι → List ℕ) (p : ι) (j : ℕ) :
    indexSupport (Function.update I p (I p ++ [j])) = insert p (indexSupport I) := by
  ext q
  by_cases hq : q = p
  · subst q; simp [indexSupport]
  · simp [indexSupport, hq]

lemma indexSupport_card_append_new {ι : Type*} [DecidableEq ι] {n : ℕ} {I : ι → List ℕ}
    (hI : IndexFamilyValid n I) (p : ι) (j : ℕ) (hp : I p = []) :
    (indexSupport (Function.update I p (I p ++ [j]))).ncard = (indexSupport I).ncard + 1 := by
  rw [indexSupport_append]
  exact Set.ncard_insert_of_notMem (by simpa [indexSupport] using hp) hI.finite_support

lemma indexSupport_card_append_old {ι : Type*} [DecidableEq ι] (I : ι → List ℕ)
    (p : ι) (j : ℕ) (hp : I p ≠ []) :
    (indexSupport (Function.update I p (I p ++ [j]))).ncard = (indexSupport I).ncard := by
  rw [indexSupport_append]
  exact Set.ncard_insert_of_mem hp

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh
variable {α : Type*} [DecidableEq α]

noncomputable def analyticChainCount (s : PMState α) : ℕ :=
  s.cache.card + (indexSupport (indexFamily s)).ncard

lemma eviction_cache_card {s : PMState α} {z e : α}
    (hz : z ∉ s.cache) (he : e ∈ s.cache) (c : ℕ) :
    (evictInto s z c e).cache.card = s.cache.card := by
  change (insert z (s.cache.erase e)).card = _
  rw [Finset.card_insert_of_notMem (fun hz' => hz (Finset.mem_of_mem_erase hz'))]
  exact Finset.card_erase_add_one he

lemma clean_eviction_chainCount {s : PMState α} {n : ℕ}
    (hI : IndexFamilyValid n (indexFamily s)) (hb : ChainBookkeeping s)
    {z e : α} (hz : z ∉ s.cache) (he : e ∈ s.cache) :
    analyticChainCount (evictInto (cleanState s) z (s.clean + 1) e) =
      analyticChainCount s + 1 := by
  unfold analyticChainCount
  rw [eviction_cache_card (s := cleanState s) hz he, evictInto_indexFamily]
  change s.cache.card + (indexSupport (Function.update (indexFamily s)
    (s.phase, s.clean + 1) (indexFamily s (s.phase, s.clean + 1) ++ [s.predIdx e]))).ncard = _
  rw [indexSupport_card_append_new hI _ _
    (hb.current_empty _ (Or.inl (Nat.lt_succ_self _)))]
  omega

lemma stale_eviction_chainCount {s : PMState α} (ht : RepresentativeTail s)
    {z e : α} (hz : z ∈ s.stale \ s.cache) (he : e ∈ s.cache) :
    analyticChainCount (evictInto (staleState s z) z (s.chainOf z) e) =
      analyticChainCount s := by
  have hnon : indexFamily s (s.phase, s.chainOf z) ≠ [] := by
    intro hempty
    have hh := ht z hz
    rw [hempty] at hh
    simp at hh
  unfold analyticChainCount
  rw [eviction_cache_card (s := staleState s z) (Finset.mem_sdiff.mp hz).2 he, evictInto_indexFamily]
  change s.cache.card + (indexSupport (Function.update (indexFamily s)
    (s.phase, s.chainOf z) (indexFamily s (s.phase, s.chainOf z) ++ [s.predIdx e]))).ncard = _
  rw [indexSupport_card_append_old _ _ _ hnon]

lemma phaseCharge_hitOrFill {k : ℕ} {s : PMState α}
    (hc : CacheInvariant k s) (hp : PhaseCacheInvariant k s) (z : α)
    (hh : z ∈ s.cache ∨ s.cache.card < k) :
    phaseCharge k (nativePhase s) z = if z ∈ s.cache then 0 else 1 := by
  by_cases hzM : z ∈ s.marked
  · have hzC := hc.marked_subset hzM
    simp [phaseCharge, nativePhase, hzM, hzC]
  · have hm : s.marked.card < k := by
      rcases hh with hzC | hcard
      · have hlt : s.marked.card < s.cache.card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hc.marked_subset,
            fun he => hzM (he.symm ▸ hzC)⟩)
        exact hlt.trans_le hc.card_le
      · exact (Finset.card_le_card hc.marked_subset).trans_lt hcard
    by_cases hzC : z ∈ s.cache
    · have hzS := hp.unmarked_stale (Finset.mem_sdiff.mpr ⟨hzC, hzM⟩)
      simp [phaseCharge, nativePhase, hzM, hm, hzS, hzC]
    · have hf : s.cache.card < k := hh.resolve_left hzC
      have hse : s.stale = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have := hp.stale_full ⟨x, hx⟩
        omega
      simp [phaseCharge, nativePhase, hzM, hm, hse, hzC]

lemma phaseCharge_miss {k : ℕ} {s : PMState α}
    (hc : CacheInvariant k s) {z : α} (hz : z ∉ s.cache) :
    phaseCharge k (nativePhase s) z = if z ∈ (phaseStart k s).stale then 0 else 1 := by
  have hzM : z ∉ s.marked := fun h => hz (hc.marked_subset h)
  have hmle : s.marked.card ≤ k := (Finset.card_le_card hc.marked_subset).trans hc.card_le
  by_cases hm : s.marked.card = k
  · simp [phaseCharge, nativePhase, hzM, hm, phaseStart, hz]
  · have hmlt : s.marked.card < k := by omega
    change (if z ∈ s.marked then 0 else if s.marked.card < k then
      (if z ∈ s.stale then 0 else 1) else 1) = _
    rw [if_neg hzM, if_pos hmlt]
    simp only [phaseStart, if_neg hm]
end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh
variable {α : Type*} [DecidableEq α]

lemma step_analyticChainCount {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) {s : PMState α} (hs : OperationalInvariant k s)
    {n : ℕ} (hI : IndexFamilyValid n (indexFamily s)) (hTail : RepresentativeTail s)
    (i : ℕ) (z : α) (hz : ℝ) {v : PMState α}
    (hv : v ∈ (step k tb s i z hz).support) :
    analyticChainCount v = analyticChainCount s + phaseCharge k (nativePhase s) z := by
  let t := savePrediction s i z hz
  let u := phaseStart k t
  rw [step_factored] at hv
  change v ∈ (if z ∈ t.cache ∨ t.cache.card < k then PMF.pure (hitOrFill t z)
    else if z ∉ u.stale then PMF.pure (evictInto (cleanState u) z (u.clean + 1) (tb (cleanState u)))
    else if (u.chainLen u.phase (u.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ) then
      PMF.pure (evictInto (staleState u z) z (u.chainOf z) (tb (staleState u z)))
    else randomEviction (staleState u z) z (u.chainOf z)).support at hv
  by_cases hh : z ∈ t.cache ∨ t.cache.card < k
  · rw [if_pos hh] at hv
    have he := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    rw [phaseCharge_hitOrFill hs.cache hs.phaseCache z hh]
    by_cases hzC : z ∈ s.cache
    · change (insert z s.cache).card + (indexSupport (indexFamily s)).ncard = _
      rw [Finset.insert_eq_of_mem hzC, if_pos hzC, Nat.add_zero]
      rfl
    · change (insert z s.cache).card + (indexSupport (indexFamily s)).ncard = _
      rw [Finset.card_insert_of_notMem hzC, if_neg hzC]
      unfold analyticChainCount
      omega
  · rw [if_neg hh] at hv
    have ht : CacheInvariant k t := save_cacheInvariant hs.cache i z hz
    have hf : t.cache.card = k := by have := ht.card_le; simp only [not_or] at hh; omega
    have hne : (u.cache \ u.marked).Nonempty := phaseStart_candidates_nonempty hk ht hf
    have hzC : z ∉ s.cache := (not_or.mp hh).1
    have hcharge : phaseCharge k (nativePhase s) z = if z ∈ u.stale then 0 else 1 := by
      exact phaseCharge_miss (s := t) ht hzC
    rw [hcharge]
    by_cases hzS : z ∉ u.stale
    · rw [if_pos hzS] at hv
      rw [if_neg hzS]
      have he := (PMF.mem_support_pure_iff _ _).mp hv
      subst v
      have hbu : ChainBookkeeping u := phaseStart_chainBookkeeping k
        ⟨hs.bookkeeping.lengths, hs.bookkeeping.future_empty, hs.bookkeeping.current_empty⟩
      have hIu : IndexFamilyValid n (indexFamily u) := by
        dsimp [u, phaseStart]; split_ifs <;> exact hI
      have huC : z ∉ u.cache := by change z ∉ (phaseStart k t).cache; rw [phaseStart_cache]; exact hzC
      have hcount : analyticChainCount u = analyticChainCount s := by
        dsimp [u, phaseStart]; split_ifs <;> rfl
      rw [← hcount]
      exact clean_eviction_chainCount hIu hbu huC (Finset.mem_sdiff.mp (htb (cleanState u) hne).1).1
    · rw [if_neg hzS] at hv
      rw [if_pos (not_not.mp hzS), Nat.add_zero]
      obtain ⟨_, hu, hzold⟩ := stale_miss_no_reset k s i z hz hzC (not_not.mp hzS)
      have hut : u = t := hu
      rw [hut] at hv
      have hnet : (t.cache \ t.marked).Nonempty := by rw [hut] at hne; exact hne
      have hnon : indexFamily t (t.phase, t.chainOf z) ≠ [] := by
        intro hempty
        have hh := hTail z (Finset.mem_sdiff.mpr ⟨hzold, hzC⟩)
        change indexFamily s (s.phase, s.chainOf z) = [] at hempty
        rw [hempty] at hh
        simp at hh
      have hcost (e : α) (he : e ∈ t.cache) :
          analyticChainCount (evictInto (staleState t z) z (t.chainOf z) e) = analyticChainCount s := by
        unfold analyticChainCount
        rw [eviction_cache_card (s := staleState t z) hzC he, evictInto_indexFamily]
        change s.cache.card + (indexSupport (Function.update (indexFamily t)
          (t.phase, t.chainOf z) (indexFamily t (t.phase, t.chainOf z) ++ [t.predIdx e]))).ncard = _
        rw [indexSupport_card_append_old _ _ _ hnon]
        rfl
      by_cases hr : (t.chainLen t.phase (t.chainOf z) + 1 : ℕ) ≤ (harmonic k : ℝ)
      · rw [if_pos hr] at hv
        have he := (PMF.mem_support_pure_iff _ _).mp hv
        subst v
        exact hcost _ (Finset.mem_sdiff.mp (htb (staleState t z) hnet).1).1
      · rw [if_neg hr] at hv
        obtain ⟨e, he, rfl⟩ := randomEviction_support (s := staleState t z) hnet hv
        exact hcost e (Finset.mem_sdiff.mp he).1
end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh
variable {α : Type*} [DecidableEq α]

lemma prefixRun_chainCount_remaining {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {n : ℕ} (hn : n ≤ σ.length) {s : PMState α}
    (hs : s ∈ (prefixRun k tb σ h n).support) :
    analyticChainCount s + cleanCountAux k s.stale s.marked (σ.drop n) = cleanCount k σ := by
  induction n generalizing s with
  | zero =>
    have he := (PMF.mem_support_pure_iff _ _).mp hs
    subst s
    simp [analyticChainCount, indexSupport, indexFamily, initState, cleanCount]
  | succ n ih =>
    have hnlt : n < σ.length := by omega
    rw [prefixRun_succ tb σ h hnlt] at hs
    obtain ⟨t, ht, hs⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
    have hcount := step_analyticChainCount hk tb htb
      (prefixRun_operationalInvariant hk tb htb σ h n ht)
      (prefixRun_nativeLedger hk tb htb σ h (by omega) ht).valid
      (prefixRun_representativeTail hk tb htb σ h n ht) n _ _ hs
    have hphase := step_nativePhase hk tb
      (prefixRun_cacheInvariant hk tb htb σ h n ht) n _ _ hs
    have hp := congrArg PhaseState.previous hphase
    have hc := congrArg PhaseState.current hphase
    change s.stale = _ at hp
    change s.marked = _ at hc
    have hi := ih (by omega) ht
    rw [List.drop_eq_getElem_cons hnlt] at hi
    have haux := cleanCountAux_step k (nativePhase t) (σ.get ⟨n, hnlt⟩) (σ.drop (n+1))
    change cleanCountAux k t.stale t.marked (σ.get ⟨n, hnlt⟩ :: σ.drop (n+1)) = _ at haux
    change analyticChainCount t + cleanCountAux k t.stale t.marked
      (σ.get ⟨n, hnlt⟩ :: σ.drop (n+1)) = _ at hi
    rw [haux] at hi
    rw [hcount, hp, hc]
    omega

lemma actual_chainCount_eq_cleanCount {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {s : PMState α} (hs : s ∈ (run k tb σ h).support) :
    analyticChainCount s = cleanCount k σ := by
  rw [run_eq_prefixRun] at hs
  have hh := prefixRun_chainCount_remaining hk tb htb σ h le_rfl hs
  simpa [cleanCountAux] using hh
end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

theorem actual_chain_errors_le {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (ℓ : ℝ → ℝ → ℝ) (hℓ : ∀ a b, 0 ≤ ℓ a b)
    (σ : List α) (h : Fin σ.length → ℝ) {s : PMState α}
    (hs : s ∈ (run k tb σ h).support) (keys : Finset (ℕ × ℕ)) :
    (∑ p ∈ keys, chainError ℓ σ h s p.1 p.2) ≤ predError ℓ σ h := by
  exact indexFamily_loss_le_predError ℓ hℓ σ h (indexFamily s)
    (run_nativeLedger hk tb htb σ h hs).valid keys

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

lemma exists_cache_outside_phase {α : Type*} [DecidableEq α] {C N : Finset α}
    {k : ℕ} (hC : C.card = k) (hN : N.card ≤ k) {z : α}
    (hzN : z ∈ N) (hzC : z ∉ C) : ∃ e ∈ C, e ∉ N := by
  by_contra! h
  have hsub : C ⊆ N := h
  have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
  exact hzC (heq.symm ▸ hzN)

lemma optFrom_evict_le {α : Type*} [DecidableEq α] (k : ℕ) (C : Finset α)
    (z e : α) (τ : List α) (hz : z ∉ C) (hfull : k ≤ C.card) (he : e ∈ C) :
    optFrom k C (z :: τ) ≤ 1 + optFrom k (insert z (C.erase e)) τ := by
  have hC : C.Nonempty := ⟨e, he⟩
  simp only [optFrom, if_neg hz, if_neg (not_lt.mpr hfull), dif_pos hC]
  exact Nat.add_le_add_left (Finset.inf'_le _ he) 1

lemma optFrom_le_cleanCountAux {α : Type*} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k)
    (τ : List α) (C prev cur : Finset α) (hC : C.card ≤ k) (hcur : cur ⊆ C)
    (hkeep : phaseFuture k cur τ ∩ prev ⊆ C) :
    optFrom k C τ ≤ cleanCountAux k prev cur τ := by
  induction τ generalizing C prev cur with
  | nil => simp [optFrom, cleanCountAux]
  | cons z τ ih =>
    have hcurcard : cur.card ≤ k := (Finset.card_le_card hcur).trans hC
    by_cases hzcur : z ∈ cur
    · have hzC := hcur hzcur
      have hkeep' : phaseFuture k cur τ ∩ prev ⊆ C := by
        simpa [phaseFuture_cons_of_mem k cur z τ hzcur] using hkeep
      simpa [optFrom, cleanCountAux, hzcur, hzC] using ih C prev cur hC hcur hkeep'
    · by_cases hsmall : cur.card < k
      · let N := phaseFuture k (insert z cur) τ
        have hN : N.card ≤ k := phaseFuture_card_le k _
          ((Finset.card_insert_le _ _).trans (by omega)) τ
        have hzN : z ∈ N := subset_phaseFuture k _ _ (Finset.mem_insert_self _ _)
        have hkeepN : N ∩ prev ⊆ C := by
          simpa [N, phaseFuture_cons_of_card_lt k cur z τ hsmall] using hkeep
        by_cases hzC : z ∈ C
        · have hc' : insert z cur ⊆ C := Finset.insert_subset hzC hcur
          have hind := ih C prev (insert z cur) hC hc' hkeepN
          simp only [optFrom, if_pos hzC, cleanCountAux, if_neg hzcur, if_pos hsmall]
          omega
        · have hzprev : z ∉ prev := by
            intro hzp
            exact hzC (hkeepN (Finset.mem_inter.mpr ⟨hzN, hzp⟩))
          by_cases hroom : C.card < k
          · have hC' : (insert z C).card ≤ k := (Finset.card_insert_le _ _).trans (by omega)
            have hcur' : insert z cur ⊆ insert z C := Finset.insert_subset_insert z hcur
            have hkeep' : N ∩ prev ⊆ insert z C := hkeepN.trans (Finset.subset_insert _ _)
            have hind := ih (insert z C) prev (insert z cur) hC' hcur' hkeep'
            simpa [optFrom, cleanCountAux, hzC, hzcur, hsmall, hzprev, hroom] using Nat.add_le_add_left hind 1
          · have hfull : C.card = k := by omega
            obtain ⟨e, heC, heN⟩ := exists_cache_outside_phase hfull hN hzN hzC
            let C' := insert z (C.erase e)
            have hC' : C'.card ≤ k := by
              dsimp [C']
              rw [Finset.card_insert_of_notMem (fun h => hzC (Finset.mem_of_mem_erase h)), Finset.card_erase_of_mem heC]
              omega
            have hcur' : insert z cur ⊆ C' := by
              intro x hx
              rcases Finset.mem_insert.mp hx with rfl | hx
              · exact Finset.mem_insert_self _ _
              · apply Finset.mem_insert_of_mem
                apply Finset.mem_erase.mpr
                refine ⟨?_, hcur hx⟩
                intro heq
                subst x
                exact heN (subset_phaseFuture k _ _ (Finset.mem_insert_of_mem hx))
            have hkeep' : N ∩ prev ⊆ C' := by
              intro x hx
              apply Finset.mem_insert_of_mem
              exact Finset.mem_erase.mpr ⟨(by intro heq; subst x; exact heN (Finset.mem_inter.mp hx).1), hkeepN hx⟩
            have hind := ih C' prev (insert z cur) hC' hcur' hkeep'
            have hcost := optFrom_evict_le k C z e τ hzC (by omega) heC
            simp only [cleanCountAux, if_neg hzcur, if_pos hsmall, if_neg hzprev]
            exact hcost.trans (Nat.add_le_add_left hind 1)
      · have hfullcur : cur.card = k := by omega
        have heq : cur = C := Finset.eq_of_subset_of_card_le hcur (by omega)
        subst C
        let N := phaseFuture k {z} τ
        have hN : N.card ≤ k := phaseFuture_card_le k {z} (by simpa using hk) τ
        have hzN : z ∈ N := subset_phaseFuture k _ _ (Finset.mem_singleton_self _)
        obtain ⟨e, hecur, heN⟩ := exists_cache_outside_phase hfullcur hN hzN hzcur
        let C' := insert z (cur.erase e)
        have hC' : C'.card ≤ k := by
          dsimp [C']
          rw [Finset.card_insert_of_notMem (fun h => hzcur (Finset.mem_of_mem_erase h)), Finset.card_erase_of_mem hecur]
          omega
        have hcur' : {z} ⊆ C' := by simp [C']
        have hkeep' : N ∩ cur ⊆ C' := by
          intro x hx
          apply Finset.mem_insert_of_mem
          exact Finset.mem_erase.mpr ⟨(by intro heq; subst x; exact heN (Finset.mem_inter.mp hx).1), (Finset.mem_inter.mp hx).2⟩
        have hind := ih C' cur {z} hC' hcur' hkeep'
        have hcost := optFrom_evict_le k cur z e τ hzcur (by omega) hecur
        simp only [cleanCountAux, if_neg hzcur, if_neg hsmall]
        exact hcost.trans (Nat.add_le_add_left hind 1)

lemma native_opt_le_cleanCount {α : Type*} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k)
    (σ : List α) : opt k σ ≤ cleanCount k σ := by
  exact optFrom_le_cleanCountAux k hk σ ∅ ∅ ∅ (by simp) (by simp) (by simp)

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

def phaseCut {α : Type*} [DecidableEq α] (k : ℕ) : Finset α → List α → List α × List α
  | _, [] => ([], [])
  | C, z :: τ =>
    if z ∈ C ∨ C.card < k then
      let p := phaseCut k (insert z C) τ
      (z :: p.1, p.2)
    else ([], z :: τ)

lemma phaseCut_append {α : Type*} [DecidableEq α] (k : ℕ) (C : Finset α) (τ : List α) :
    (phaseCut k C τ).1 ++ (phaseCut k C τ).2 = τ := by
  induction τ generalizing C with
  | nil => rfl
  | cons z τ ih =>
    simp only [phaseCut]
    split_ifs
    · simp only [List.cons_append]
      rw [ih]
    · rfl

lemma phaseCut_current {α : Type*} [DecidableEq α] (k : ℕ) (C : Finset α) (τ : List α) :
    C ∪ (phaseCut k C τ).1.toFinset = phaseFuture k C τ := by
  induction τ generalizing C with
  | nil => simp [phaseCut, phaseFuture]
  | cons z τ ih =>
    simp only [phaseCut, phaseFuture]
    split_ifs
    · simpa [List.toFinset_cons, Finset.union_insert, Finset.insert_union] using ih (insert z C)
    · simp

lemma phaseCut_full {α : Type*} [DecidableEq α] (k : ℕ) (C : Finset α)
    (hC : C.card ≤ k) (τ : List α) (hne : (phaseCut k C τ).2 ≠ []) :
    (C ∪ (phaseCut k C τ).1.toFinset).card = k := by
  induction τ generalizing C with
  | nil => exact (hne rfl).elim
  | cons z τ ih =>
    by_cases h : z ∈ C ∨ C.card < k
    · have hcard : (insert z C).card ≤ k := by
        rcases h with hz | hsmall
        · simpa [Finset.insert_eq_of_mem hz] using hC
        · exact (Finset.card_insert_le _ _).trans (by omega)
      have hn : (phaseCut k (insert z C) τ).2 ≠ [] := by simpa [phaseCut, h] using hne
      simpa [phaseCut, h, List.toFinset_cons, Finset.union_insert, Finset.insert_union] using ih _ hcard hn
    · simp only [phaseCut, if_neg h, List.toFinset_nil, Finset.union_empty]
      have : ¬ C.card < k := fun hc => h (Or.inr hc)
      omega

lemma phaseCut_first_nonempty {α : Type*} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k)
    (τ : List α) (hne : τ ≠ []) : (phaseCut k ∅ τ).1 ≠ [] := by
  cases τ with
  | nil => exact (hne rfl).elim
  | cons z τ => simp [phaseCut, show 0 < k by omega]

lemma phaseCut_rest_length_lt {α : Type*} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k)
    (τ : List α) (hne : τ ≠ []) : (phaseCut k ∅ τ).2.length < τ.length := by
  have h := congrArg List.length (phaseCut_append k ∅ τ)
  rw [List.length_append] at h
  have hp := List.length_pos_iff.mpr (phaseCut_first_nonempty k hk τ hne)
  omega

lemma clean_insert_card {α : Type*} [DecidableEq α] (C P : Finset α) (z : α)
    (hz : z ∉ C) : (insert z C \ P).card = (if z ∈ P then 0 else 1) + (C \ P).card := by
  by_cases hzP : z ∈ P
  · simp [Finset.insert_sdiff_of_mem, hzP]
  · rw [Finset.insert_sdiff_of_notMem _ hzP, Finset.card_insert_of_notMem]
    · simp [hzP, Nat.add_comm]
    · simp [hz]

lemma phaseCut_clean {α : Type*} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k)
    (C P : Finset α) (hC : C.card ≤ k) (τ : List α) :
    cleanCountAux k P C τ + (C \ P).card =
      ((C ∪ (phaseCut k C τ).1.toFinset) \ P).card +
        cleanCountAux k (C ∪ (phaseCut k C τ).1.toFinset) ∅ (phaseCut k C τ).2 := by
  induction τ generalizing C P with
  | nil => simp [phaseCut, cleanCountAux]
  | cons z τ ih =>
    by_cases hz : z ∈ C
    · simpa [phaseCut, cleanCountAux, hz, Finset.insert_eq_of_mem hz,
        List.toFinset_cons, Finset.union_insert, Finset.insert_union] using ih C P hC
    · by_cases hsmall : C.card < k
      · have hcard : (insert z C).card ≤ k := (Finset.card_insert_le _ _).trans (by omega)
        have h := ih (insert z C) P hcard
        rw [clean_insert_card C P z hz] at h
        simpa [phaseCut, cleanCountAux, hz, hsmall, List.toFinset_cons,
          Finset.union_insert, Finset.insert_union, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
      · simp [phaseCut, cleanCountAux, hz, hsmall, show 0 < k by omega,
          Nat.add_comm, Nat.add_left_comm]

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

inductive OfflineTrace {α : Type*} [DecidableEq α] (k : ℕ) :
    Finset α → List α → Finset α → ℕ → Prop
  | nil (C : Finset α) : OfflineTrace k C [] C 0
  | hit {C D : Finset α} {z : α} {τ : List α} {c : ℕ}
      (hz : z ∈ C) (tail : OfflineTrace k C τ D c) : OfflineTrace k C (z :: τ) D c
  | room {C D : Finset α} {z : α} {τ : List α} {c : ℕ}
      (hz : z ∉ C) (hroom : C.card < k) (tail : OfflineTrace k (insert z C) τ D c) :
      OfflineTrace k C (z :: τ) D (1 + c)
  | evict {C D : Finset α} {z e : α} {τ : List α} {c : ℕ}
      (hz : z ∉ C) (hfull : C.card = k) (he : e ∈ C)
      (tail : OfflineTrace k (insert z (C.erase e)) τ D c) :
      OfflineTrace k C (z :: τ) D (1 + c)

lemma optFrom_attained {α : Type*} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k)
    (C : Finset α) (hC : C.card ≤ k) (σ : List α) :
    ∃ D, OfflineTrace k C σ D (optFrom k C σ) := by
  induction σ generalizing C with
  | nil => exact ⟨C, OfflineTrace.nil C⟩
  | cons z τ ih =>
    by_cases hz : z ∈ C
    · obtain ⟨D, ht⟩ := ih C hC
      exact ⟨D, by simpa [optFrom, hz] using OfflineTrace.hit hz ht⟩
    · by_cases hroom : C.card < k
      · have hcard : (insert z C).card ≤ k := (Finset.card_insert_le _ _).trans (by omega)
        obtain ⟨D, ht⟩ := ih (insert z C) hcard
        exact ⟨D, by simpa [optFrom, hz, hroom] using OfflineTrace.room hz hroom ht⟩
      · have hfull : C.card = k := by omega
        have hne : C.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨e, he, hemin⟩ := Finset.exists_mem_eq_inf' hne (fun e => optFrom k (insert z (C.erase e)) τ)
        have hcard : (insert z (C.erase e)).card ≤ k := by
          rw [Finset.card_insert_of_notMem (by simp [hz]), Finset.card_erase_of_mem he]
          omega
        obtain ⟨D, ht⟩ := ih (insert z (C.erase e)) hcard
        refine ⟨D, ?_⟩
        have htrace := OfflineTrace.evict hz hfull he ht
        simpa [optFrom, hz, hroom, hne, hemin] using htrace

lemma OfflineTrace.final_card_le {α : Type*} [DecidableEq α] {k : ℕ}
    {C D : Finset α} {σ : List α} {c : ℕ} (h : OfflineTrace k C σ D c)
    (hC : C.card ≤ k) : D.card ≤ k := by
  induction h with
  | nil => exact hC
  | hit _ _ ih => exact ih hC
  | room _ hroom _ ih => exact ih ((Finset.card_insert_le _ _).trans (by omega))
  | @evict C D z e τ c hz hfull he ht ih =>
    have hc : (insert z (C.erase e)).card ≤ k := by
      rw [Finset.card_insert_of_notMem (fun h => hz (Finset.mem_of_mem_erase h)), Finset.card_erase_of_mem he]
      have hpos := Finset.card_pos.mpr (show C.Nonempty from ⟨e, he⟩)
      omega
    exact ih hc

lemma OfflineTrace.request_cover {α : Type*} [DecidableEq α] {k : ℕ}
    {C D : Finset α} {σ : List α} {c : ℕ} (h : OfflineTrace k C σ D c) :
    ∃ L : List α, L.length = c ∧ σ.toFinset ⊆ C ∪ L.toFinset := by
  induction h with
  | nil C => exact ⟨[], rfl, by simp⟩
  | hit hz _ ih =>
    obtain ⟨L, hL, hcover⟩ := ih
    refine ⟨L, hL, ?_⟩
    simpa only [List.toFinset_cons] using Finset.insert_subset (Finset.mem_union_left _ hz) hcover
  | @room C D z τ c hz hroom tail ih =>
    obtain ⟨L, hL, hcover⟩ := ih
    refine ⟨z :: L, by simp [hL, Nat.add_comm], ?_⟩
    simp only [List.toFinset_cons] at hcover ⊢
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · subst x; simp
    · have := hcover hx
      simpa [Finset.insert_union, Finset.union_insert] using this
  | @evict C D z e τ c hz hfull he tail ih =>
    obtain ⟨L, hL, hcover⟩ := ih
    refine ⟨z :: L, by simp [hL, Nat.add_comm], ?_⟩
    simp only [List.toFinset_cons] at hcover ⊢
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · subst x; simp
    · rcases Finset.mem_union.mp (hcover hx) with hc | hLx
      · rcases Finset.mem_insert.mp hc with hzx | herase
        · subst x; simp
        · exact Finset.mem_union_left _ (Finset.mem_of_mem_erase herase)
      · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hLx)

lemma OfflineTrace.distinct_requests_le {α : Type*} [DecidableEq α] {k : ℕ}
    {C D : Finset α} {σ : List α} {c : ℕ} (h : OfflineTrace k C σ D c) :
    σ.toFinset.card ≤ C.card + c := by
  obtain ⟨L, hL, hcover⟩ := h.request_cover
  calc
    σ.toFinset.card ≤ (C ∪ L.toFinset).card := Finset.card_le_card hcover
    _ ≤ C.card + L.toFinset.card := Finset.card_union_le _ _
    _ ≤ C.card + c := Nat.add_le_add_left (by simpa [hL] using List.toFinset_card_le L) _

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

lemma OfflineTrace.split {α : Type*} [DecidableEq α] {k : ℕ}
    {C D : Finset α} (σ τ : List α) {c : ℕ} (h : OfflineTrace k C (σ ++ τ) D c) :
    ∃ M c₁ c₂, OfflineTrace k C σ M c₁ ∧ OfflineTrace k M τ D c₂ ∧ c = c₁ + c₂ := by
  induction σ generalizing C c with
  | nil => exact ⟨C, 0, c, OfflineTrace.nil C, h, by simp⟩
  | cons z σ ih =>
    cases h with
    | hit hz ht =>
      obtain ⟨M, c₁, c₂, h₁, h₂, hc⟩ := ih ht
      exact ⟨M, c₁, c₂, OfflineTrace.hit hz h₁, h₂, hc⟩
    | room hz hroom ht =>
      obtain ⟨M, c₁, c₂, h₁, h₂, hc⟩ := ih ht
      exact ⟨M, 1 + c₁, c₂, OfflineTrace.room hz hroom h₁, h₂, by omega⟩
    | evict hz hfull he ht =>
      obtain ⟨M, c₁, c₂, h₁, h₂, hc⟩ := ih ht
      exact ⟨M, 1 + c₁, c₂, OfflineTrace.evict hz hfull he h₁, h₂, by omega⟩

lemma OfflineTrace.append {α : Type*} [DecidableEq α] {k : ℕ}
    {C M D : Finset α} {σ τ : List α} {c₁ c₂ : ℕ}
    (h₁ : OfflineTrace k C σ M c₁) (h₂ : OfflineTrace k M τ D c₂) :
    OfflineTrace k C (σ ++ τ) D (c₁ + c₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | hit hz _ ih => exact OfflineTrace.hit hz (ih h₂)
  | room hz hroom _ ih => simpa [Nat.add_assoc] using OfflineTrace.room hz hroom (ih h₂)
  | evict hz hfull he _ ih => simpa [Nat.add_assoc] using OfflineTrace.evict hz hfull he (ih h₂)

lemma OfflineTrace.initial_distinct_le {α : Type*} [DecidableEq α] {k : ℕ}
    {D : Finset α} {σ : List α} {c : ℕ} (h : OfflineTrace k ∅ σ D c) :
    σ.toFinset.card ≤ c := by
  simpa using h.distinct_requests_le

lemma OfflineTrace.adjacent_clean_le {α : Type*} [DecidableEq α] {k : ℕ}
    {C M D : Finset α} {σ τ : List α} {c₁ c₂ : ℕ}
    (h₁ : OfflineTrace k C σ M c₁) (h₂ : OfflineTrace k M τ D c₂)
    (hC : C.card ≤ k) (hσ : σ.toFinset.card = k) :
    (τ.toFinset \ σ.toFinset).card ≤ c₁ + c₂ := by
  have h := (h₁.append h₂).distinct_requests_le
  rw [List.toFinset_append] at h
  have hc := Finset.card_union_add_card_inter σ.toFinset τ.toFinset
  have hd := Finset.card_sdiff_add_card_inter τ.toFinset σ.toFinset
  rw [Finset.inter_comm τ.toFinset σ.toFinset] at hd
  omega

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

lemma trace_tail_clean_le {α : Type*} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k)
    (prev τ : List α) (C₀ C D : Finset α) (p c : ℕ)
    (hC₀ : C₀.card ≤ k) (hp : prev.toFinset.card = k)
    (hprev : OfflineTrace k C₀ prev C p) (ht : OfflineTrace k C τ D c) :
    cleanCountAux k prev.toFinset ∅ τ ≤ p + 2 * c := by
  by_cases hnil : τ = []
  · subst τ
    simp [cleanCountAux]
  let A := (phaseCut k ∅ τ).1
  let B := (phaseCut k ∅ τ).2
  have hcat : A ++ B = τ := phaseCut_append k ∅ τ
  have htr : OfflineTrace k C (A ++ B) D c := by rw [hcat]; exact ht
  obtain ⟨M, a, b, hA, hB, hc⟩ := htr.split A B
  have hclean : cleanCountAux k prev.toFinset ∅ τ =
      (A.toFinset \ prev.toFinset).card + cleanCountAux k A.toFinset ∅ B := by
    simpa [A, B] using phaseCut_clean k hk ∅ prev.toFinset (by simp) τ
  have hfirst : (A.toFinset \ prev.toFinset).card ≤ p + a :=
    hprev.adjacent_clean_le hA hC₀ hp
  by_cases hBnil : B = []
  · rw [hclean, hBnil]
    simp only [cleanCountAux, Nat.add_zero]
    omega
  · have hfull : A.toFinset.card = k := by
      simpa [A] using phaseCut_full k ∅ (by simp) τ hBnil
    have hC : C.card ≤ k := hprev.final_card_le hC₀
    have hrec := trace_tail_clean_le k hk A B C M D a b hC hfull hA hB
    rw [hclean]
    omega
termination_by τ.length
decreasing_by exact phaseCut_rest_length_lt k hk τ hnil

lemma native_clean_le_two_opt {α : Type*} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k)
    (σ : List α) : cleanCount k σ ≤ 2 * opt k σ := by
  by_cases hnil : σ = []
  · subst σ
    simp [cleanCount, cleanCountAux, opt, optFrom]
  obtain ⟨D, ht⟩ := optFrom_attained k hk ∅ (by simp) σ
  let A := (phaseCut k ∅ σ).1
  let B := (phaseCut k ∅ σ).2
  have hcat : A ++ B = σ := phaseCut_append k ∅ σ
  have htr : OfflineTrace k ∅ (A ++ B) D (opt k σ) := by
    rw [hcat]
    exact ht
  obtain ⟨M, a, b, hA, hB, hc⟩ := htr.split A B
  have hclean : cleanCount k σ = A.toFinset.card + cleanCountAux k A.toFinset ∅ B := by
    simpa [cleanCount, A, B] using phaseCut_clean k hk ∅ ∅ (by simp) σ
  have hfirst : A.toFinset.card ≤ a := hA.initial_distinct_le
  by_cases hBnil : B = []
  · rw [hclean, hBnil]
    simp only [cleanCountAux, Nat.add_zero]
    omega
  · have hfull : A.toFinset.card = k := by
      simpa [A] using phaseCut_full k ∅ (by simp) σ hBnil
    have htail := trace_tail_clean_le k hk A B ∅ M D a b (by simp) hfull hA hB
    rw [hclean]
    omega

end CachingML.PredMarker.PMFresh
end


section

open Set
open scoped BigOperators

namespace CachingML.PredMarker.PMFresh

lemma cleanCount_pos_of_ne_nil {α : Type*} [DecidableEq α] {k : ℕ} (hk : 1 ≤ k)
    {σ : List α} (hσ : σ ≠ []) : 0 < cleanCount k σ := by
  cases σ with
  | nil => exact (hσ rfl).elim
  | cons z τ => simp [cleanCount, cleanCountAux, show 0 < k by omega]

lemma native_opt_pos_of_ne_nil {α : Type*} [DecidableEq α] {k : ℕ} (hk : 1 ≤ k)
    {σ : List α} (hσ : σ ≠ []) : 0 < opt k σ := by
  have h := cleanCount_pos_of_ne_nil hk hσ
  have h' := native_clean_le_two_opt k hk σ
  omega

lemma benchmark_chain_budget {S : ℝ → ℝ} {H ε E : ℝ}
    (hS : ConcaveOn ℝ (Ici 0) S) (hmono : MonotoneOn S (Ici 0))
    (hH : 1 ≤ H) (hSε : 1 ≤ S ε) (hε : 0 ≤ ε)
    {Q O : ℕ} (hOQ : O ≤ Q) (hQO : Q ≤ 2 * O)
    (e : Fin Q → ℝ) (he : ∀ i, 0 ≤ e i)
    (hE : (∑ i, e i) ≤ E) (hacc : E ≤ ε * O) :
    (∑ i, chainBudget S H (e i)) ≤
      2 * min (1 + 2 * S ε) (2 * H) * O := by
  have hg : 0 ≤ chainBudget S H ε := (by norm_num : (0 : ℝ) ≤ 1).trans (chainBudget_one_le hH hSε)
  by_cases hQ : Q = 0
  · subst Q
    simp only [Fin.sum_univ_zero]
    change 0 ≤ 2 * chainBudget S H ε * O
    positivity
  · have haccQ : E ≤ ε * Q := hacc.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hOQ) hε)
    have hsum := total_chain_budget H hS hmono (Nat.pos_of_ne_zero hQ) e he hE haccQ
    have hcard : (Q : ℝ) ≤ 2 * O := by exact_mod_cast hQO
    have hmul := mul_le_mul_of_nonneg_right hcard hg
    calc
      (∑ i, chainBudget S H (e i)) ≤ Q * chainBudget S H ε := hsum
      _ ≤ (2 * O) * chainBudget S H ε := hmul
      _ = 2 * min (1 + 2 * S ε) (2 * H) * O := by unfold chainBudget; ring

end CachingML.PredMarker.PMFresh
end


section

open Set
open scoped ENNReal

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

lemma actual_active_budget_bound {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ) (hσ : σ ≠ [])
    {ℓ : ℝ → ℝ → ℝ} {S : ℝ → ℝ} {ε : ℝ}
    (hℓ : ∀ x y, 0 ≤ ℓ x y) (hc : ConcaveOn ℝ (Ici 0) S)
    (hsp : ∀ m : ℝ, 0 ≤ m → ∃ t : ℕ, spread ℓ m = t ∧ (t : ℝ) ≤ S m)
    (hε : 0 ≤ ε) (hacc : predError ℓ σ h ≤ ε * opt k σ)
    {s : PMState α} (hs : s ∈ (run k tb σ h).support)
    (K : Finset (ℕ × ℕ)) (hK : ∀ p, indexFamily s p ≠ [] → p ∈ K) :
    (s.cache.card : ℝ≥0∞) + (∑ p ∈ K, activeChainBudget ℓ S k σ h p s) ≤
      ENNReal.ofReal (2 * min (1 + 2 * S ε) (2 * (harmonic k : ℝ)) * opt k σ) := by
  classical
  let A := K.filter (fun p => indexFamily s p ≠ [])
  have hA : (↑A : Set (ℕ × ℕ)) = indexSupport (indexFamily s) := by
    ext p
    simp only [A, Finset.mem_coe, Finset.mem_filter, indexSupport, Set.mem_ofPred_eq]
    exact ⟨fun hp => hp.2, fun hp => ⟨hK p hp, hp⟩⟩
  have hcard : A.card = (indexSupport (indexFamily s)).ncard := by
    rw [← hA, Set.ncard_coe_finset]
  have hQ : s.cache.card + A.card = cleanCount k σ := by
    rw [hcard]
    exact actual_chainCount_eq_cleanCount hk tb htb σ h hs
  have hnonneg : ∀ p : ℕ × ℕ, 0 ≤ chainError ℓ σ h s p.1 p.2 :=
    fun p => chainError_nonneg ℓ hℓ σ h s p
  have hbudgetnonneg : ∀ p : ℕ × ℕ, 0 ≤ chainBudget S (harmonic k) (chainError ℓ σ h s p.1 p.2) := by
    intro p
    exact (by norm_num : (0 : ℝ) ≤ 1).trans
      (chainBudget_one_le (harmonic_real_one_le hk) (majorant_one_le hsp (hnonneg p)))
  have haccQ : predError ℓ σ h ≤ ε * (s.cache.card + A.card : ℕ) := by
    rw [hQ]
    exact hacc.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast native_opt_le_cleanCount k hk σ) hε)
  have hreal := active_budget_with_singletons (harmonic k : ℝ) hc (majorant_monotone hc hsp)
    (chainBudget_one_le (harmonic_real_one_le hk) (majorant_one_le hsp (by norm_num)))
    s.cache.card A (fun p => chainError ℓ σ h s p.1 p.2) (fun p _ => hnonneg p)
    (by rw [hQ]; exact cleanCount_pos_of_ne_nil hk hσ)
    (actual_chain_errors_le hk tb htb ℓ hℓ σ h hs A) haccQ
  rw [hQ] at hreal
  have hg : 0 ≤ chainBudget S (harmonic k) ε := (by norm_num : (0 : ℝ) ≤ 1).trans
    (chainBudget_one_le (harmonic_real_one_le hk) (majorant_one_le hsp hε))
  have hQO : (cleanCount k σ : ℝ) ≤ 2 * opt k σ := by exact_mod_cast native_clean_le_two_opt k hk σ
  have hfinal : (s.cache.card : ℝ) + (∑ p ∈ A, chainBudget S (harmonic k) (chainError ℓ σ h s p.1 p.2)) ≤
      2 * min (1 + 2 * S ε) (2 * (harmonic k : ℝ)) * opt k σ := by
    apply hreal.trans
    calc
      (cleanCount k σ : ℝ) * chainBudget S (harmonic k) ε ≤
          (2 * opt k σ) * chainBudget S (harmonic k) ε := mul_le_mul_of_nonneg_right hQO hg
      _ = _ := by unfold chainBudget; ring
  have hsum : (∑ p ∈ K, activeChainBudget ℓ S k σ h p s) =
      ENNReal.ofReal (∑ p ∈ A, chainBudget S (harmonic k) (chainError ℓ σ h s p.1 p.2)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun p _ => hbudgetnonneg p)]
    change (∑ p ∈ K, if indexFamily s p = [] then 0 else _) = ∑ p ∈ K.filter _, _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hempty : indexFamily s p = [] <;> simp [hempty]
  rw [hsum]
  have heq : (s.cache.card : ℝ≥0∞) + ENNReal.ofReal
      (∑ p ∈ A, chainBudget S (harmonic k) (chainError ℓ σ h s p.1 p.2)) =
      ENNReal.ofReal ((s.cache.card : ℝ) + ∑ p ∈ A,
        chainBudget S (harmonic k) (chainError ℓ σ h s p.1 p.2)) := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg _) (Finset.sum_nonneg (fun p _ => hbudgetnonneg p))]
    simp
  rw [heq]
  exact ENNReal.ofReal_le_ofReal hfinal

end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker.PMFresh

lemma finite_support_union_keys {α ι : Type*} (P : PMF α) (I : α → ι → List ℕ)
    (hP : P.support.Finite) (hI : ∀ s ∈ P.support, Set.Finite {p | I s p ≠ []}) :
    ∃ K : Finset ι, ∀ s ∈ P.support, ∀ p, I s p ≠ [] → p ∈ K := by
  classical
  have hf : (⋃ s ∈ P.support, {p | I s p ≠ []}).Finite := hP.biUnion hI
  refine ⟨hf.toFinset, ?_⟩
  intro s hs p hp
  apply hf.mem_toFinset.mpr
  exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨hs, hp⟩⟩

lemma actual_global_chain_keys {α : Type*} [DecidableEq α] {k : ℕ} (hk : 1 ≤ k)
    (tb : PMState α → α) (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ) :
    ∃ K : Finset (ℕ × ℕ), ∀ s ∈ (run k tb σ h).support, ∀ p,
      indexFamily s p ≠ [] → p ∈ K := by
  exact finite_support_union_keys (run k tb σ h) indexFamily (run_finite_support k tb σ h)
    (fun s hs => (run_nativeLedger hk tb htb σ h hs).valid.finite_support)

end CachingML.PredMarker.PMFresh
end


section

open scoped ENNReal

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

def NativeCostBalance (s : PMState α) : Prop :=
  (s.misses : ℝ≥0∞) = (s.cache.card : ℝ≥0∞) + indexLengthTotal (indexFamily s)

omit [DecidableEq α] in
theorem init_nativeCostBalance : NativeCostBalance (initState α) := by
  simp [NativeCostBalance, initState, indexFamily, indexLengthTotal]

theorem step_nativeCostBalance {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) {s : PMState α} (hs : CacheInvariant k s)
    (hb : NativeCostBalance s) (i : ℕ) (z : α) (hz : ℝ) {v : PMState α}
    (hv : v ∈ (step k tb s i z hz).support) : NativeCostBalance v := by
  obtain ⟨_, _, hm, _⟩ := step_observations hk tb hs i z hz hv
  change (v.misses : ℝ≥0∞) = (v.cache.card : ℝ≥0∞) + indexLengthTotal (indexFamily v)
  change (s.misses : ℝ≥0∞) = (s.cache.card : ℝ≥0∞) + indexLengthTotal (indexFamily s) at hb
  rcases step_ledger_cases hk tb htb hs i z hz hv with ⟨hi, hc⟩ | ⟨hzc, e, he, p, hc, hi⟩
  · by_cases hzc : z ∈ s.cache
    · rw [hm, if_pos hzc, Nat.add_zero, hc, Finset.insert_eq_of_mem hzc, hi]
      exact hb
    · rw [hm, if_neg hzc, hc, Finset.card_insert_of_notMem hzc, hi]
      simp only [Nat.cast_add, Nat.cast_one]
      rw [hb]
      ac_rfl
  · have hcard : v.cache.card = s.cache.card := by
      rw [hc, Finset.card_insert_of_notMem (fun hz => hzc (Finset.mem_of_mem_erase hz))]
      exact Finset.card_erase_add_one he
    rw [hm, if_neg hzc, hcard, hi, indexLengthTotal_append]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [hb]
    ac_rfl

theorem prefixRun_nativeCostBalance {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ) (n : ℕ)
    {s : PMState α} (hs : s ∈ (prefixRun k tb σ h n).support) : NativeCostBalance s := by
  induction n generalizing s with
  | zero =>
    have he := (PMF.mem_support_pure_iff _ _).mp hs
    subst s
    exact init_nativeCostBalance
  | succ n ih =>
    obtain ⟨t, ht, hs⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
    unfold indexedStep at hs
    split_ifs at hs with hn
    · exact step_nativeCostBalance hk tb htb (prefixRun_cacheInvariant hk tb htb σ h n ht)
        (ih ht) n _ _ hs
    · have he := (PMF.mem_support_pure_iff _ _).mp hs
      subst s
      exact ih ht

theorem actual_misses_eq_cache_plus_chains {k : ℕ} (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {s : PMState α} (hs : s ∈ (run k tb σ h).support) :
    (s.misses : ℝ≥0∞) = (s.cache.card : ℝ≥0∞) + ∑' p : ℕ × ℕ, (s.chainLen p.1 p.2 : ℝ≥0∞) := by
  have hb := run_operationalInvariant hk tb htb σ h hs
  have hs' := hs
  rw [run_eq_prefixRun] at hs'
  have hc := prefixRun_nativeCostBalance hk tb htb σ h σ.length hs'
  change (s.misses : ℝ≥0∞) = (s.cache.card : ℝ≥0∞) + indexLengthTotal (indexFamily s) at hc
  rw [hc]
  congr 1
  apply tsum_congr
  intro p
  exact congrArg (fun n : ℕ => (n : ℝ≥0∞)) (hb.bookkeeping.lengths p).symm

end CachingML.PredMarker.PMFresh
end


section

open scoped ENNReal

namespace CachingML.PredMarker.PMFresh

lemma pmExpectation_finset_sum {α ι : Type*} (P : PMF α) (K : Finset ι)
    (F : ι → α → ℝ≥0∞) :
    pmExpectation P (fun s => ∑ p ∈ K, F p s) = ∑ p ∈ K, pmExpectation P (F p) := by
  classical
  induction K using Finset.induction_on with
  | empty => simp [pmExpectation]
  | @insert p K hp ih => simp [Finset.sum_insert, hp, pmExpectation_add, ih]

end CachingML.PredMarker.PMFresh
end


section

open Set
open scoped ENNReal

namespace CachingML.PredMarker.PMFresh

variable {α : Type*} [DecidableEq α]

lemma native_competitive_of_active_chain_bounds {k : ℕ} (hk : 1 ≤ k)
    (tb : PMState α → α) (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {ℓ : ℝ → ℝ → ℝ} {S : ℝ → ℝ} {ε : ℝ}
    (hℓ : ∀ x y, 0 ≤ ℓ x y) (hc : ConcaveOn ℝ (Ici 0) S)
    (hsp : ∀ m : ℝ, 0 ≤ m → ∃ t : ℕ, spread ℓ m = t ∧ (t : ℝ) ≤ S m)
    (hε : 0 ≤ ε) (hacc : predError ℓ σ h ≤ ε * opt k σ)
    (hchain : ∀ p : ℕ × ℕ,
      pmExpectation (run k tb σ h) (fun s => (s.chainLen p.1 p.2 : ℝ≥0∞)) ≤
        pmExpectation (run k tb σ h) (activeChainBudget ℓ S k σ h p)) :
    expCost k tb σ h ≤
      ENNReal.ofReal (2 * min (1 + 2 * S ε) (2 * (harmonic k : ℝ)) * opt k σ) := by
  classical
  by_cases hσ : σ = []
  · subst σ
    have hz : expCost k tb [] h = 0 := by simp [expCost, run, initState]
    rw [hz]
    exact zero_le
  obtain ⟨K, hK⟩ := actual_global_chain_keys hk tb htb σ h
  have hcost : ∀ s ∈ (run k tb σ h).support,
      (s.misses : ℝ≥0∞) = (s.cache.card : ℝ≥0∞) + ∑ p ∈ K, (s.chainLen p.1 p.2 : ℝ≥0∞) := by
    intro s hs
    rw [actual_misses_eq_cache_plus_chains hk tb htb σ h hs]
    congr 1
    apply tsum_eq_sum
    intro p hp
    have hempty : indexFamily s p = [] := by
      by_contra he
      exact hp (hK s hs p he)
    have hlen := (run_operationalInvariant hk tb htb σ h hs).bookkeeping.lengths p
    change s.chainLen p.1 p.2 = (indexFamily s p).length at hlen
    simp [hlen, hempty]
  change pmExpectation (run k tb σ h) (fun s => (s.misses : ℝ≥0∞)) ≤ _
  rw [pmExpectation_congr_support (run k tb σ h) hcost, pmExpectation_add, pmExpectation_finset_sum]
  apply (add_le_add le_rfl (Finset.sum_le_sum (fun p _ => hchain p))).trans
  rw [← pmExpectation_finset_sum, ← pmExpectation_add]
  calc
    pmExpectation (run k tb σ h)
        (fun s => (s.cache.card : ℝ≥0∞) + ∑ p ∈ K, activeChainBudget ℓ S k σ h p s) ≤
      pmExpectation (run k tb σ h) (fun _ => ENNReal.ofReal
        (2 * min (1 + 2 * S ε) (2 * (harmonic k : ℝ)) * opt k σ)) :=
      pmExpectation_mono _ (fun s hs => actual_active_budget_bound hk tb htb σ h hσ
        hℓ hc hsp hε hacc hs K (hK s hs))
    _ = _ := pmExpectation_const _ _

end CachingML.PredMarker.PMFresh
end


section

open Set
open scoped ENNReal
namespace CachingML.PredMarker.PMFresh
variable {α : Type*} [DecidableEq α]

lemma native_predictiveMarker_competitive {k : ℕ} (hk : 1 ≤ k)
    (tb : PMState α → α) (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {ℓ : ℝ → ℝ → ℝ} {S : ℝ → ℝ} {ε : ℝ}
    (hℓ : ∀ x y, 0 ≤ ℓ x y) (hc : ConcaveOn ℝ (Ici 0) S)
    (h0 : ContinuousWithinAt S (Ici 0) 0)
    (hsp : ∀ m : ℝ, 0 ≤ m → ∃ t : ℕ, spread ℓ m = t ∧ (t : ℝ) ≤ S m)
    (hε : 0 ≤ ε) (hacc : predError ℓ σ h ≤ ε * opt k σ) :
    expCost k tb σ h ≤
      ENNReal.ofReal (2 * min (1 + 2 * S ε) (2 * (harmonic k : ℝ)) * opt k σ) := by
  apply native_competitive_of_active_chain_bounds hk tb htb σ h hℓ hc hsp hε hacc
  intro p
  apply active_chain_expectation_from_native_suffix hk tb htb σ h hℓ hc h0 hsp p
  intro n hn s hs _ hkey
  exact actual_first_switch_suffix_bound hk tb htb σ h n hn hs p hkey
end CachingML.PredMarker.PMFresh
end


section

namespace CachingML.PredMarker

/-- Theorem 3.3 of Lykouris–Vassilvitskii (arXiv:1802.05399v4, p. 14): for cache size `k ≥ 1`, a
nonnegative loss `ℓ` whose spread is bounded by a concave function `S` (continuous at `0`), and any
`ε ≥ 0`, Predictive Marker (with any tie-breaking of its `arg max`) satisfies, on every request sequence
`σ` and prediction sequence `h` with error `η_ℓ(h, σ) ≤ ε · Opt(σ)`,
`E[cost_PM(σ)] ≤ 2 · min(1 + 2 S(ε), 2 H_k) · Opt(σ)`. -/
theorem predictiveMarker_competitive {α : Type*} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k)
    (ℓ : ℝ → ℝ → ℝ) (hℓ : ∀ a b, 0 ≤ ℓ a b)
    (S : ℝ → ℝ) (hSconc : ConcaveOn ℝ (Set.Ici 0) S)
    (hScont : ContinuousWithinAt S (Set.Ici 0) 0)
    (hspread : ∀ m : ℝ, 0 ≤ m → ∃ t : ℕ, spread ℓ m = t ∧ (t : ℝ) ≤ S m)
    (ε : ℝ) (hε : 0 ≤ ε)
    (tb : PMState α → α) (htb : IsMaxTieBreak tb)
    (σ : List α) (h : Fin σ.length → ℝ)
    (hacc : predError ℓ σ h ≤ ε * (opt k σ : ℝ)) :
    expCost k tb σ h ≤
      ENNReal.ofReal (2 * min (1 + 2 * S ε) (2 * (harmonic k : ℝ)) * (opt k σ : ℝ)) := by
  exact PMFresh.native_predictiveMarker_competitive hk tb htb σ h hℓ hSconc hScont hspread hε hacc

end CachingML.PredMarker
end


theorem solution {α : Type*} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k)
    (ℓ : ℝ → ℝ → ℝ) (hℓ : ∀ a b, 0 ≤ ℓ a b)
    (S : ℝ → ℝ) (hSconc : ConcaveOn ℝ (Set.Ici 0) S)
    (hScont : ContinuousWithinAt S (Set.Ici 0) 0)
    (hspread : ∀ m : ℝ, 0 ≤ m → ∃ t : ℕ, CachingML.PredMarker.spread ℓ m = t ∧ (t : ℝ) ≤ S m)
    (ε : ℝ) (hε : 0 ≤ ε)
    (tb : CachingML.PredMarker.PMState α → α) (htb : CachingML.PredMarker.IsMaxTieBreak tb)
    (σ : List α) (h : Fin σ.length → ℝ)
    (hacc : CachingML.PredMarker.predError ℓ σ h ≤ ε * (CachingML.PredMarker.opt k σ : ℝ)) :
    CachingML.PredMarker.expCost k tb σ h ≤
      ENNReal.ofReal (2 * min (1 + 2 * S ε) (2 * (harmonic k : ℝ)) * (CachingML.PredMarker.opt k σ : ℝ)) := by
  exact CachingML.PredMarker.predictiveMarker_competitive k hk ℓ hℓ S hSconc hScont hspread ε hε tb htb σ h hacc
