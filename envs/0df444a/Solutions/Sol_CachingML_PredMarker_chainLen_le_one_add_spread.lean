-- Prove2me | solution 1 for CachingML.PredMarker.chainLen_le_one_add_spread
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-24T08:29:49.160155+00:00
-- url     : https://prove2.me/submissions/c063753b-2e3a-406f-9f14-c7fdbe9fed91

import Init
import Mathlib
import Definitions.Def_CachingML_PredMarker_predictiveMarker
import Definitions.Def_CachingML_PredMarker_spread

namespace CachingML.PredMarker.RunBounds
variable {α : Type*} [DecidableEq α]
def Bounded (k : ℕ) (s : PMState α) : Prop :=
  s.marked ⊆ s.cache ∧ s.cache.card ≤ k

theorem evict_bounded {k : ℕ} {s : PMState α} (hs : Bounded k s)
    (z : α) (c : ℕ) {e : α} (he : e ∈ s.cache \ s.marked) :
    Bounded k (evictInto s z c e) := by
  obtain ⟨hec,hem⟩ := Finset.mem_sdiff.mp he
  constructor
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by intro h; subst x; exact hem hx, hs.1 hx⟩)
  · change (insert z (s.cache.erase e)).card ≤ k
    have hp : 0 < s.cache.card := Finset.card_pos.mpr ⟨e,hec⟩
    have hc := Finset.card_insert_le z (s.cache.erase e)
    rw [Finset.card_erase_of_mem hec] at hc
    have hcap := hs.2
    omega

theorem unmarked_nonempty {k : ℕ} {s : PMState α} (hs : Bounded k s)
    (hfull : k ≤ s.cache.card) (hmark : s.marked.card < k) :
    (s.cache \ s.marked).Nonempty := by
  rw [Finset.sdiff_nonempty]
  intro hc
  have h := Finset.card_le_card hc
  omega

theorem step_bounded (k : ℕ) (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) {s : PMState α} (hs : Bounded k s)
    (i : ℕ) (z : α) (hz : ℝ) {t : PMState α}
    (ht : t ∈ (step k tb s i z hz).support) : Bounded k t := by
  classical
  let u : PMState α := {s with pred := Function.update s.pred z hz, predIdx := Function.update s.predIdx z i}
  have hu : Bounded k u := hs
  let v : PMState α := if u.marked.card = k then
    {u with phase := u.phase+1, clean := 0, stale := u.cache, marked := ∅} else u
  have hv : Bounded k v := by
    dsimp [v]; split
    · exact ⟨Finset.empty_subset _,hu.2⟩
    · exact hu
  have hvc : v.cache = u.cache := by dsimp [v]; split <;> rfl
  unfold step at ht
  change t ∈ (if z ∈ u.cache ∨ u.cache.card < k then _ else _ : PMF (PMState α)).support at ht
  by_cases hf : z ∈ u.cache ∨ u.cache.card < k
  · rw [if_pos hf] at ht
    rw [PMF.mem_support_pure_iff] at ht
    subst t
    constructor
    · exact Finset.insert_subset_insert z hu.1
    · rcases hf with hz | hcard
      · simpa [u,Finset.insert_eq_of_mem hz] using hu.2
      · exact (Finset.card_insert_le z u.cache).trans (by omega)
  · rw [if_neg hf] at ht
    have hfull : k ≤ v.cache.card := by rw [hvc]; exact Nat.le_of_not_gt (not_or.mp hf).2
    have hm : v.marked.card < k := by
      dsimp [v]; split
      · simpa using (show 0 < k by omega)
      · rename_i hne
        have hle := (Finset.card_le_card hu.1).trans hu.2
        omega
    have hne := unmarked_nonempty hv hfull hm
    change t ∈ (if z ∉ v.stale then _ else _ : PMF (PMState α)).support at ht
    by_cases hclean : z ∉ v.stale
    · rw [if_pos hclean] at ht
      rw [PMF.mem_support_pure_iff] at ht
      subst t
      apply evict_bounded (s := {v with
        clean := v.clean+1
        chainLen := Function.update v.chainLen v.phase
          (Function.update (v.chainLen v.phase) (v.clean+1) 1)}) hv
      exact (htb {v with clean := v.clean+1, chainLen := Function.update v.chainLen v.phase (Function.update (v.chainLen v.phase) (v.clean+1) 1)} hne).1
    · rw [if_neg hclean] at ht
      change t ∈ (if ((v.chainLen v.phase (v.chainOf z) + 1 : ℕ) : ℝ) ≤
          (harmonic k : ℝ) then _ else _ : PMF (PMState α)).support at ht
      by_cases hpred : ((v.chainLen v.phase (v.chainOf z) + 1 : ℕ) : ℝ) ≤ (harmonic k : ℝ)
      · rw [if_pos hpred] at ht
        rw [PMF.mem_support_pure_iff] at ht
        subst t
        apply evict_bounded (s := {v with
          chainLen := Function.update v.chainLen v.phase
            (Function.update (v.chainLen v.phase) (v.chainOf z)
              (v.chainLen v.phase (v.chainOf z) + 1))}) hv
        exact (htb {v with chainLen := Function.update v.chainLen v.phase (Function.update (v.chainLen v.phase) (v.chainOf z) (v.chainLen v.phase (v.chainOf z) + 1))} hne).1
      · rw [if_neg hpred, dif_pos hne, PMF.mem_support_map_iff] at ht
        obtain ⟨e,he,rfl⟩ := ht
        rw [PMF.mem_support_uniformOfFinset_iff] at he
        exact evict_bounded hv z (v.chainOf z) he

theorem run_invariant (P : PMState α → Prop) (k : ℕ) (tb : PMState α → α)
    (hinit : P (initState α))
    (hstep : ∀ s, P s → ∀ i z hz t, t ∈ (step k tb s i z hz).support → P t)
    (σ : List α) (h : Fin σ.length → ℝ) {s : PMState α}
    (hs : s ∈ (run k tb σ h).support) : P s := by
  have hf : ∀ s ∈ (run k tb σ h).support, P s := by
    unfold run
    apply List.foldlRecOn (motive := fun μ : PMF (PMState α) => ∀ s ∈ μ.support, P s)
    · intro s hs
      rw [PMF.mem_support_pure_iff] at hs
      simpa [hs] using hinit
    · intro μ hμ j hj t ht
      rw [PMF.mem_support_bind_iff] at ht
      obtain ⟨u,hu,ht⟩ := ht
      exact hstep u (hμ u hu) j.val (σ.get j) (h j) t ht
  exact hf s hs

theorem run_bounded (k : ℕ) (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {s : PMState α} (hs : s ∈ (run k tb σ h).support) : Bounded k s := by
  apply run_invariant (Bounded k) k tb (by simp [Bounded,initState])
    (fun _ hu i z hz _ ht => step_bounded k hk tb htb hu i z hz ht) σ h hs

#print axioms run_bounded
end CachingML.PredMarker.RunBounds

namespace CachingML.PredMarker.Bookkeeping
variable {α : Type*} [DecidableEq α]
structure Coherent (s : PMState α) : Prop where
  lengths : ∀ r c, (s.chainIdx r c).length = s.chainLen r c
  fresh : ∀ r c, s.phase < r ∨ (r = s.phase ∧ s.clean < c) → s.chainIdx r c = []
  missing : ∀ e ∈ s.stale, e ∉ s.cache → s.chainOf e ≤ s.clean

def bump (s : PMState α) (c : ℕ) : PMState α :=
  {s with
    chainLen := Function.update s.chainLen s.phase
      (Function.update (s.chainLen s.phase) c (s.chainLen s.phase c + 1))}

def push (s : PMState α) (z : α) (c : ℕ) (e : α) : PMState α :=
  evictInto (bump s c) z c e

theorem push_coherent {s : PMState α} (hs : Coherent s) (z : α) {c : ℕ}
    (hc : c ≤ s.clean) (e : α) : Coherent (push s z c e) := by
  constructor
  · intro r d
    by_cases hr : r = s.phase <;> by_cases hd : d = c <;>
      simp [push,evictInto,bump,Function.update_apply,hr,hd,hs.lengths]
  · intro r d hrd
    change s.phase < r ∨ (r = s.phase ∧ s.clean < d) at hrd
    have hd : r = s.phase → d ≠ c := by rintro rfl rfl; omega
    have he := hs.fresh r d hrd
    by_cases hr : r = s.phase
    · simpa [push,evictInto,bump,Function.update_apply,hr,hd hr] using he
    · simpa [push,evictInto,bump,Function.update_apply,hr] using he
  · intro x hx hxc
    change x ∈ s.stale at hx
    change x ∉ insert z (s.cache.erase e) at hxc
    change Function.update s.chainOf e c x ≤ s.clean
    by_cases he : x = e
    · simpa [he] using hc
    · rw [Function.update_of_ne he]
      apply hs.missing x hx
      intro hm
      exact hxc (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨he,hm⟩))

theorem reset_coherent {s : PMState α} (hs : Coherent s) :
    Coherent {s with phase := s.phase+1, clean := 0, stale := s.cache, marked := ∅} := by
  constructor
  · exact hs.lengths
  · intro r c hrc
    apply hs.fresh r c (Or.inl ?_)
    change s.phase+1 < r ∨ (r = s.phase+1 ∧ 0 < c) at hrc
    omega
  · intro e he hne
    exact (hne he).elim

theorem clean_coherent {s : PMState α} (hs : Coherent s) :
    Coherent {s with clean := s.clean+1} := by
  constructor
  · exact hs.lengths
  · intro r c hrc
    apply hs.fresh r c
    change s.phase < r ∨ (r = s.phase ∧ s.clean+1 < c) at hrc
    rcases hrc with hr | ⟨hr,hc⟩
    · exact Or.inl hr
    · exact Or.inr ⟨hr,by omega⟩
  · intro e he hne
    exact (hs.missing e he hne).trans (Nat.le_succ _)

theorem load_coherent {s : PMState α} (hs : Coherent s) (z : α) (m : ℕ) :
    Coherent {s with cache := insert z s.cache, marked := insert z s.marked, misses := m} := by
  constructor
  · exact hs.lengths
  · exact hs.fresh
  · intro e he hne
    exact hs.missing e he (fun hc => hne (Finset.mem_insert_of_mem hc))

theorem step_coherent (k : ℕ) (tb : PMState α → α)
    {s : PMState α} (hs : Coherent s) (i : ℕ) (z : α) (hz : ℝ) {t : PMState α}
    (ht : t ∈ (step k tb s i z hz).support) : Coherent t := by
  classical
  let u : PMState α := {s with pred := Function.update s.pred z hz, predIdx := Function.update s.predIdx z i}
  have hu : Coherent u := ⟨hs.lengths,hs.fresh,hs.missing⟩
  let v : PMState α := if u.marked.card = k then
    {u with phase := u.phase+1, clean := 0, stale := u.cache, marked := ∅} else u
  have hv : Coherent v := by dsimp [v]; split; exact reset_coherent hu; exact hu
  have hvc : v.cache = u.cache := by dsimp [v]; split <;> rfl
  unfold step at ht
  change t ∈ (if z ∈ u.cache ∨ u.cache.card < k then _ else _ : PMF (PMState α)).support at ht
  by_cases hf : z ∈ u.cache ∨ u.cache.card < k
  · rw [if_pos hf, PMF.mem_support_pure_iff] at ht
    subst t
    exact load_coherent hu z _
  · rw [if_neg hf] at ht
    have hzc : z ∉ v.cache := by rw [hvc]; exact (not_or.mp hf).1
    change t ∈ (if z ∉ v.stale then _ else _ : PMF (PMState α)).support at ht
    by_cases hclean : z ∉ v.stale
    · rw [if_pos hclean, PMF.mem_support_pure_iff] at ht
      subst t
      have hz0 : v.chainLen v.phase (v.clean+1) = 0 := by
        rw [← hv.lengths, hv.fresh _ _ (Or.inr ⟨rfl,by omega⟩)]
        rfl
      let w : PMState α := {v with clean := v.clean+1}
      have hw := clean_coherent hv
      have hh := push_coherent hw z (le_refl (v.clean+1))
        (tb {v with clean := v.clean+1, chainLen := Function.update v.chainLen v.phase (Function.update (v.chainLen v.phase) (v.clean+1) 1)})
      simpa [push,bump,hz0] using hh
    · rw [if_neg hclean] at ht
      have hc : v.chainOf z ≤ v.clean := hv.missing z (not_not.mp hclean) hzc
      change t ∈ (if ((v.chainLen v.phase (v.chainOf z) + 1 : ℕ) : ℝ) ≤
        (harmonic k : ℝ) then _ else _ : PMF (PMState α)).support at ht
      by_cases hp : ((v.chainLen v.phase (v.chainOf z)+1 : ℕ) : ℝ) ≤ (harmonic k : ℝ)
      · rw [if_pos hp, PMF.mem_support_pure_iff] at ht
        subst t
        exact push_coherent hv z hc (tb (bump v (v.chainOf z)))
      · rw [if_neg hp] at ht
        by_cases hne : (v.cache \ v.marked).Nonempty
        · rw [dif_pos hne,PMF.mem_support_map_iff] at ht
          obtain ⟨e,_,rfl⟩ := ht
          have hv' : Coherent {v with randomChains := insert (v.phase,v.chainOf z) v.randomChains} :=
            ⟨hv.lengths,hv.fresh,hv.missing⟩
          exact push_coherent hv' z hc e
        · rw [dif_neg hne,PMF.mem_support_pure_iff] at ht
          subst t
          exact push_coherent hv z hc z

theorem run_coherent (k : ℕ) (tb : PMState α → α) (σ : List α)
    (h : Fin σ.length → ℝ) {s : PMState α} (hs : s ∈ (run k tb σ h).support) : Coherent s := by
  have hi : Coherent (initState α) := by
    constructor <;> simp [initState]
  exact RunBounds.run_invariant Coherent k tb hi
    (fun _ hu i z hz _ ht => step_coherent k tb hu i z hz ht) σ h hs

theorem run_chain_length (k : ℕ) (tb : PMState α → α) (σ : List α)
    (h : Fin σ.length → ℝ) {s : PMState α} (hs : s ∈ (run k tb σ h).support) (r c : ℕ) :
    (s.chainIdx r c).length = s.chainLen r c := (run_coherent k tb σ h hs).lengths r c
#print axioms run_chain_length
end CachingML.PredMarker.Bookkeeping

namespace CachingML.PredMarker.History
variable {α : Type*} [DecidableEq α]

/-- Every supported transition saves exactly this request's prediction and
introduces no cache page other than the requested page. -/
theorem step_saved (k : ℕ) (tb : PMState α → α) (s : PMState α)
    (i : ℕ) (z : α) (hz : ℝ) {t : PMState α}
    (ht : t ∈ (step k tb s i z hz).support) :
    t.pred = Function.update s.pred z hz ∧
    t.predIdx = Function.update s.predIdx z i ∧ t.cache ⊆ insert z s.cache := by
  classical
  let u : PMState α := {s with pred := Function.update s.pred z hz, predIdx := Function.update s.predIdx z i}
  let v : PMState α := if u.marked.card = k then
    {u with phase := u.phase+1, clean := 0, stale := u.cache, marked := ∅} else u
  have hvc : v.cache = s.cache := by dsimp [v]; split <;> rfl
  have hvp : v.pred = Function.update s.pred z hz := by dsimp [v]; split <;> rfl
  have hvi : v.predIdx = Function.update s.predIdx z i := by dsimp [v]; split <;> rfl
  have he (e : α) : insert z (v.cache.erase e) ⊆ insert z s.cache := by
    rw [hvc]
    exact Finset.insert_subset_insert z (Finset.erase_subset e s.cache)
  unfold step at ht
  change t ∈ (if z ∈ u.cache ∨ u.cache.card < k then _ else _ : PMF (PMState α)).support at ht
  split at ht
  · rw [PMF.mem_support_pure_iff] at ht
    subst t
    exact ⟨rfl,rfl,fun _ hx => hx⟩
  · change t ∈ (if z ∉ v.stale then _ else _ : PMF (PMState α)).support at ht
    split at ht
    · rw [PMF.mem_support_pure_iff] at ht
      subst t
      exact ⟨hvp,hvi,he _⟩
    · change t ∈ (if ((v.chainLen v.phase (v.chainOf z)+1 : ℕ) : ℝ) ≤ (harmonic k : ℝ)
        then _ else _ : PMF (PMState α)).support at ht
      split at ht
      · rw [PMF.mem_support_pure_iff] at ht
        subst t
        exact ⟨hvp,hvi,he _⟩
      · by_cases hne : (v.cache \ v.marked).Nonempty
        · rw [dif_pos hne,PMF.mem_support_map_iff] at ht
          obtain ⟨e,_,rfl⟩ := ht
          exact ⟨hvp,hvi,he _⟩
        · rw [dif_neg hne,PMF.mem_support_pure_iff] at ht
          subst t
          exact ⟨hvp,hvi,he _⟩

/-- Cached pages carry the prediction and index of their most recent request
in the processed prefix, with no later occurrence of that page in the prefix. -/
def Saved (σ : List α) (h : Fin σ.length → ℝ) (n : ℕ) (s : PMState α) : Prop :=
  ∀ x ∈ s.cache, ∃ j : Fin σ.length,
    j.val < n ∧ σ.get j = x ∧ s.predIdx x = j.val ∧ s.pred x = h j ∧
    ∀ a : Fin σ.length, j < a → a.val < n → σ.get a ≠ x

theorem saved_init (σ : List α) (h : Fin σ.length → ℝ) : Saved σ h 0 (initState α) := by
  simp [Saved,initState]

theorem step_history (k : ℕ) (tb : PMState α → α) (σ : List α)
    (h : Fin σ.length → ℝ) (i : Fin σ.length) {s : PMState α}
    (hs : Saved σ h i.val s) {t : PMState α}
    (ht : t ∈ (step k tb s i.val (σ.get i) (h i)).support) : Saved σ h (i.val+1) t := by
  obtain ⟨hp,hi,hc⟩ := step_saved k tb s i.val (σ.get i) (h i) ht
  intro x hx
  by_cases hxi : x = σ.get i
  · subst x
    refine ⟨i,by omega,rfl,?_,?_,?_⟩
    · simp [hi]
    · simp [hp]
    · intro a hia han
      have := (show i.val < a.val from hia)
      omega
  · have hxs : x ∈ s.cache := (Finset.mem_insert.mp (hc hx)).resolve_left hxi
    obtain ⟨j,hjn,hjx,hidx,hpred,hlast⟩ := hs x hxs
    refine ⟨j,by omega,hjx,?_,?_,?_⟩
    · rw [hi,Function.update_of_ne hxi]; exact hidx
    · rw [hp,Function.update_of_ne hxi]; exact hpred
    · intro a hja han
      by_cases hai : a = i
      · subst a; exact Ne.symm hxi
      · apply hlast a hja
        have hav : a.val ≠ i.val := fun heq => hai (Fin.ext heq)
        omega

noncomputable def prefixRun (k : ℕ) (tb : PMState α → α) (σ : List α)
    (h : Fin σ.length → ℝ) (n : ℕ) : PMF (PMState α) :=
  ((List.finRange σ.length).take n).foldl
    (fun μ i => μ.bind (fun s => step k tb s i.val (σ.get i) (h i))) (PMF.pure (initState α))

theorem prefixRun_succ (k : ℕ) (tb : PMState α → α) (σ : List α)
    (h : Fin σ.length → ℝ) (n : ℕ) (hn : n < σ.length) :
    prefixRun k tb σ h (n+1) =
      (prefixRun k tb σ h n).bind (fun s => step k tb s n (σ.get ⟨n,hn⟩) (h ⟨n,hn⟩)) := by
  unfold prefixRun
  rw [List.take_succ_eq_append_getElem (by simpa using hn),List.foldl_append]
  simp

theorem prefix_saved (k : ℕ) (tb : PMState α → α) (σ : List α)
    (h : Fin σ.length → ℝ) (n : ℕ) (hn : n ≤ σ.length) {s : PMState α}
    (hs : s ∈ (prefixRun k tb σ h n).support) : Saved σ h n s := by
  induction n generalizing s with
  | zero =>
    have he : s = initState α := by
      simpa only [prefixRun,List.take_zero,List.foldl_nil,PMF.mem_support_pure_iff] using hs
    subst s
    exact saved_init σ h
  | succ n ih =>
    have hlt : n < σ.length := by omega
    rw [prefixRun_succ k tb σ h n hlt, PMF.mem_support_bind_iff] at hs
    obtain ⟨u,hu,hs⟩ := hs
    exact step_history k tb σ h ⟨n,hlt⟩ (ih (by omega) hu) hs

theorem run_saved (k : ℕ) (tb : PMState α → α) (σ : List α)
    (h : Fin σ.length → ℝ) {s : PMState α} (hs : s ∈ (run k tb σ h).support) :
    Saved σ h σ.length s := by
  apply prefix_saved k tb σ h σ.length le_rfl
  have htake : (List.finRange σ.length).take σ.length = List.finRange σ.length :=
    List.take_of_length_le (by simp)
  simpa only [prefixRun,run,htake] using hs

#print axioms run_saved
end CachingML.PredMarker.History

namespace CachingML.PredMarker.History
variable {α : Type*} [DecidableEq α]

/-- If no later request of this page occurs in a processed prefix, its next
arrival lies strictly beyond that prefix, including the never-again sentinel. -/
theorem nextArrival_gt_prefix (σ : List α) (j : Fin σ.length) (n : ℕ)
    (hn : n ≤ σ.length)
    (hlast : ∀ a : Fin σ.length, j < a → a.val < n → σ.get a ≠ σ.get j) :
    n < nextArrival σ j := by
  classical
  let js := (List.finRange σ.length).filter (fun a => decide (j < a ∧ σ.get a = σ.get j))
  change n < ((js.head?).map (fun a => a.val+1)).getD (σ.length+1)
  cases he : js.head? with
  | none => simp [he]; omega
  | some a =>
    have ha : a ∈ js := List.mem_of_head? he
    have hm : j < a ∧ σ.get a = σ.get j := by simpa [js] using (List.mem_filter.mp ha).2
    have hna : n ≤ a.val := by
      by_contra hnot
      exact hlast a hm.1 (by omega) hm.2
    simp [he]
    omega

theorem saved_nextArrival (σ : List α) (h : Fin σ.length → ℝ) (n : ℕ)
    (hn : n ≤ σ.length) {s : PMState α} (hs : Saved σ h n s) {x : α}
    (hx : x ∈ s.cache) :
    ∃ j : Fin σ.length, j.val < n ∧ σ.get j = x ∧ s.predIdx x = j.val ∧
      s.pred x = h j ∧ n < nextArrival σ j := by
  obtain ⟨j,hjn,hjx,hi,hp,hlast⟩ := hs x hx
  refine ⟨j,hjn,hjx,hi,hp,nextArrival_gt_prefix σ j n hn ?_⟩
  intro a hja han he
  exact hlast a hja han (he.trans hjx)

/-- A cached page different from the current request has its next arrival
strictly after the current request's one-based time. -/
theorem saved_other_nextArrival (σ : List α) (h : Fin σ.length → ℝ)
    (i : Fin σ.length) {s : PMState α} (hs : Saved σ h i.val s) {x : α}
    (hx : x ∈ s.cache) (hxi : x ≠ σ.get i) :
    ∃ j : Fin σ.length, j.val < i.val ∧ σ.get j = x ∧ s.predIdx x = j.val ∧
      s.pred x = h j ∧ i.val+1 < nextArrival σ j := by
  obtain ⟨j,hjn,hjx,hi,hp,hlast⟩ := hs x hx
  refine ⟨j,hjn,hjx,hi,hp,nextArrival_gt_prefix σ j (i.val+1) (by omega) ?_⟩
  intro a hja han
  rw [hjx]
  by_cases hai : a = i
  · subst a; exact Ne.symm hxi
  · apply hlast a hja
    have hav : a.val ≠ i.val := fun heq => hai (Fin.ext heq)
    omega

/-- The first subsequent request supplies exactly the one-based next-arrival label. -/
theorem nextArrival_eq_of_latest (σ : List α) (j i : Fin σ.length)
    (hji : j < i) (hij : σ.get i = σ.get j)
    (hlast : ∀ a : Fin σ.length, j < a → a.val < i.val → σ.get a ≠ σ.get j) :
    nextArrival σ j = i.val+1 := by
  classical
  let js := (List.finRange σ.length).filter (fun a => decide (j < a ∧ σ.get a = σ.get j))
  have hi : i ∈ js := by
    apply List.mem_filter.mpr
    exact ⟨by simp,by simpa only [decide_eq_true_eq] using And.intro hji hij⟩
  have hord : js.Pairwise (· ≤ ·) := (List.pairwise_le_finRange σ.length).filter _
  change ((js.head?).map (fun a => a.val+1)).getD (σ.length+1) = i.val+1
  cases he : js.head? with
  | none =>
    have hempty : js = [] := List.head?_eq_none_iff.mp he
    simpa [hempty] using hi
  | some a =>
    have ha : a ∈ js := List.mem_of_head? he
    have hm : j < a ∧ σ.get a = σ.get j := by simpa [js] using (List.mem_filter.mp ha).2
    have hia : i ≤ a := by
      by_contra hn
      exact hlast a hm.1 (by exact lt_of_not_ge hn) hm.2
    obtain ⟨xs,hxs⟩ := List.head?_eq_some_iff.mp he
    have hai : a ≤ i := by
      rw [hxs] at hord hi
      rcases List.mem_cons.mp hi with hei | hi
      · subst i; exact le_rfl
      · exact (List.pairwise_cons.mp hord).1 i hi
    have hai' : a = i := le_antisymm hai hia
    simp [hai']

#print axioms saved_other_nextArrival
end CachingML.PredMarker.History

namespace CachingML.PredMarker.History
variable {α : Type*} [DecidableEq α]

/-- Predictions of all previously requested pages remain meaningful, including
pages currently absent from the cache. -/
def Remembered (σ : List α) (h : Fin σ.length → ℝ) (n : ℕ) (s : PMState α) : Prop :=
  ∀ x : α, (∃ q : Fin σ.length, q.val < n ∧ σ.get q = x) →
    ∃ j : Fin σ.length, j.val < n ∧ σ.get j = x ∧ s.predIdx x = j.val ∧
      s.pred x = h j ∧ ∀ a : Fin σ.length, j < a → a.val < n → σ.get a ≠ x

theorem remembered_init (σ : List α) (h : Fin σ.length → ℝ) :
    Remembered σ h 0 (initState α) := by
  simp [Remembered]

theorem step_remembered (k : ℕ) (tb : PMState α → α) (σ : List α)
    (h : Fin σ.length → ℝ) (i : Fin σ.length) {s : PMState α}
    (hs : Remembered σ h i.val s) {t : PMState α}
    (ht : t ∈ (step k tb s i.val (σ.get i) (h i)).support) : Remembered σ h (i.val+1) t := by
  obtain ⟨hp,hi,_⟩ := step_saved k tb s i.val (σ.get i) (h i) ht
  intro x hx
  by_cases hxi : x = σ.get i
  · subst x
    refine ⟨i,by omega,rfl,?_,?_,?_⟩
    · simp [hi]
    · simp [hp]
    · intro a hia han
      have := (show i.val < a.val from hia)
      omega
  · obtain ⟨q,hqn,hqx⟩ := hx
    have hqi : q.val < i.val := by
      have hne : q.val ≠ i.val := by
        intro he
        have hqi : q = i := Fin.ext he
        subst q
        exact hxi hqx.symm
      omega
    obtain ⟨j,hjn,hjx,hidx,hpred,hlast⟩ := hs x ⟨q,hqi,hqx⟩
    refine ⟨j,by omega,hjx,?_,?_,?_⟩
    · rw [hi,Function.update_of_ne hxi]; exact hidx
    · rw [hp,Function.update_of_ne hxi]; exact hpred
    · intro a hja han
      by_cases hai : a = i
      · subst a; exact Ne.symm hxi
      · apply hlast a hja
        have hav : a.val ≠ i.val := fun heq => hai (Fin.ext heq)
        omega

/-- A time-indexed invariant for every supported finite run prefix. -/
theorem prefix_invariant (k : ℕ) (tb : PMState α → α) (σ : List α)
    (h : Fin σ.length → ℝ) (P : ℕ → PMState α → Prop)
    (hinit : P 0 (initState α))
    (hstep : ∀ i : Fin σ.length, ∀ s, P i.val s → ∀ t,
      t ∈ (step k tb s i.val (σ.get i) (h i)).support → P (i.val+1) t)
    (n : ℕ) (hn : n ≤ σ.length) {s : PMState α}
    (hs : s ∈ (prefixRun k tb σ h n).support) : P n s := by
  induction n generalizing s with
  | zero =>
    have he : s = initState α := by
      simpa only [prefixRun,List.take_zero,List.foldl_nil,PMF.mem_support_pure_iff] using hs
    subst s
    exact hinit
  | succ n ih =>
    have hlt : n < σ.length := by omega
    rw [prefixRun_succ k tb σ h n hlt, PMF.mem_support_bind_iff] at hs
    obtain ⟨u,hu,hs⟩ := hs
    exact hstep ⟨n,hlt⟩ u (ih (by omega) hu) s hs

theorem prefix_remembered (k : ℕ) (tb : PMState α → α) (σ : List α)
    (h : Fin σ.length → ℝ) (n : ℕ) (hn : n ≤ σ.length) {s : PMState α}
    (hs : s ∈ (prefixRun k tb σ h n).support) : Remembered σ h n s :=
  prefix_invariant k tb σ h (Remembered σ h) (remembered_init σ h)
    (fun i _ hp _ ht => step_remembered k tb σ h i hp ht) n hn hs

theorem run_remembered (k : ℕ) (tb : PMState α → α) (σ : List α)
    (h : Fin σ.length → ℝ) {s : PMState α} (hs : s ∈ (run k tb σ h).support) :
    Remembered σ h σ.length s := by
  apply prefix_remembered k tb σ h σ.length le_rfl
  have htake : (List.finRange σ.length).take σ.length = List.finRange σ.length :=
    List.take_of_length_le (by simp)
  simpa only [prefixRun,run,htake] using hs

/-- A re-requested page's remembered index has exactly the current next-arrival
label, whether or not the page is currently cached. -/
theorem remembered_rerequest (σ : List α) (h : Fin σ.length → ℝ)
    (i : Fin σ.length) {s : PMState α} (hs : Remembered σ h i.val s)
    (hseen : ∃ q : Fin σ.length, q.val < i.val ∧ σ.get q = σ.get i) :
    ∃ j : Fin σ.length, j.val < i.val ∧ σ.get j = σ.get i ∧ s.predIdx (σ.get i) = j.val ∧
      s.pred (σ.get i) = h j ∧ nextArrival σ j = i.val+1 := by
  obtain ⟨j,hjn,hjx,hi,hp,hlast⟩ := hs (σ.get i) hseen
  refine ⟨j,hjn,hjx,hi,hp,nextArrival_eq_of_latest σ j i hjn hjx.symm ?_⟩
  intro a hja han he
  exact hlast a hja han (he.trans hjx)

#print axioms remembered_rerequest
#print axioms run_remembered
end CachingML.PredMarker.History

namespace CachingML.PredMarker.Representatives
variable {α : Type*} [DecidableEq α]

/-- Every absent stale page represents a distinct chain, whose last saved request
is that page's latest request. During preparation, the current request is exempt. -/
structure Coherent (s : PMState α) (except : Option α := none) : Prop where
  unmarked : s.cache \ s.marked ⊆ s.stale
  unique : ∀ x ∈ s.stale \ s.cache, ∀ y ∈ s.stale \ s.cache,
    s.chainOf x = s.chainOf y → x = y
  last : ∀ x ∈ s.stale \ s.cache, except ≠ some x →
    (s.chainIdx s.phase (s.chainOf x)).getLast? = some (s.predIdx x)

theorem prepare {s : PMState α} (hs : Coherent s) (z : α) (i : ℕ) (hz : ℝ) :
    Coherent {s with pred := Function.update s.pred z hz, predIdx := Function.update s.predIdx z i} (some z) := by
  refine ⟨hs.unmarked,hs.unique,?_⟩
  intro x hx hne
  have hzx : x ≠ z := by intro h; subst x; exact hne rfl
  simpa [Function.update_of_ne hzx] using hs.last x hx (by simp)

theorem reset (s : PMState α) (z : Option α) :
    Coherent {s with phase := s.phase+1, clean := 0, stale := s.cache, marked := ∅} z := by
  constructor
  · simp
  · simp
  · simp

theorem load {s : PMState α} {z : α} (hs : Coherent s (some z)) (m : ℕ) :
    Coherent {s with cache := insert z s.cache, marked := insert z s.marked, misses := m} := by
  have old : ∀ x ∈ s.stale \ insert z s.cache,
      x ∈ s.stale \ s.cache ∧ x ≠ z := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_insert, not_or] at hx ⊢
    exact ⟨⟨hx.1,hx.2.2⟩,hx.2.1⟩
  constructor
  · intro x hx
    change x ∈ insert z s.cache \ insert z s.marked at hx
    have h := Finset.mem_sdiff.mp hx
    have hne : x ≠ z := by intro he; subst x; exact h.2 (Finset.mem_insert_self _ _)
    exact hs.unmarked (Finset.mem_sdiff.mpr
      ⟨(Finset.mem_insert.mp h.1).resolve_left hne,
       fun hm => h.2 (Finset.mem_insert_of_mem hm)⟩)
  · intro x hx y hy he
    exact hs.unique x (old x hx).1 y (old y hy).1 he
  · intro x hx _
    exact hs.last x (old x hx).1 (by simpa [eq_comm] using (old x hx).2)

theorem evict {s : PMState α} {z : α} (hs : Coherent s (some z))
    (c : ℕ) {e : α} (he : e ∈ s.cache \ s.marked)
    (separate : ∀ x ∈ s.stale \ s.cache, x ≠ z → s.chainOf x ≠ c) :
    Coherent (evictInto s z c e) := by
  have old : ∀ x ∈ s.stale \ insert z (s.cache.erase e), x ≠ e →
      x ∈ s.stale \ s.cache ∧ x ≠ z := by
    intro x hx hxe
    obtain ⟨hxs,hxc⟩ := Finset.mem_sdiff.mp hx
    have hn : x ≠ z ∧ x ∉ s.cache.erase e := by
      simpa only [Finset.mem_insert, not_or] using hxc
    refine ⟨Finset.mem_sdiff.mpr ⟨hxs,?_⟩,hn.1⟩
    intro hc
    exact hn.2 (Finset.mem_erase.mpr ⟨hxe,hc⟩)
  constructor
  · intro x hx
    change x ∈ insert z (s.cache.erase e) \ insert z s.marked at hx
    obtain ⟨hxc,hxm⟩ := Finset.mem_sdiff.mp hx
    have hxz : x ≠ z := by intro h; subst x; exact hxm (Finset.mem_insert_self _ _)
    apply hs.unmarked
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_of_mem_erase ((Finset.mem_insert.mp hxc).resolve_left hxz),
       fun hm => hxm (Finset.mem_insert_of_mem hm)⟩
  · intro x hx y hy hxy
    change Function.update s.chainOf e c x = Function.update s.chainOf e c y at hxy
    by_cases hxe : x = e
    · subst x
      by_cases hye : y = e
      · exact hye.symm
      · have ho := old y hy hye
        have hn := separate y ho.1 ho.2
        simp only [Function.update_self,Function.update_of_ne hye] at hxy
        exact (hn hxy.symm).elim
    · by_cases hye : y = e
      · subst y
        have ho := old x hx hxe
        have hn := separate x ho.1 ho.2
        simp only [Function.update_self,Function.update_of_ne hxe] at hxy
        exact (hn hxy).elim
      · exact hs.unique x (old x hx hxe).1 y (old y hy hye).1
          (by simpa [Function.update_of_ne hxe,Function.update_of_ne hye] using hxy)
  · intro x hx _
    by_cases hxe : x = e
    · subst x
      simp [evictInto]
    · have ho := old x hx hxe
      have hc := separate x ho.1 ho.2
      simpa [evictInto,Function.update_of_ne hxe,Function.update_of_ne hc]
        using hs.last x ho.1 (by simpa [eq_comm] using ho.2)


theorem step_coherent (k : ℕ) (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) {s : PMState α} (hs : Coherent s)
    (hb : Bookkeeping.Coherent s) (hbound : RunBounds.Bounded k s)
    (i : ℕ) (z : α) (hz : ℝ) {t : PMState α}
    (ht : t ∈ (step k tb s i z hz).support) : Coherent t := by
  classical
  let u : PMState α := {s with pred := Function.update s.pred z hz, predIdx := Function.update s.predIdx z i}
  have hu : Coherent u (some z) := prepare hs z i hz
  have hub : Bookkeeping.Coherent u := ⟨hb.lengths,hb.fresh,hb.missing⟩
  have hud : RunBounds.Bounded k u := hbound
  let v : PMState α := if u.marked.card = k then
    {u with phase := u.phase+1, clean := 0, stale := u.cache, marked := ∅} else u
  have hv : Coherent v (some z) := by
    dsimp [v]; split; exact reset _ _; exact hu
  have hvb : Bookkeeping.Coherent v := by
    dsimp [v]; split; exact Bookkeeping.reset_coherent hub; exact hub
  have hvd : RunBounds.Bounded k v := by
    dsimp [v]; split; exact ⟨Finset.empty_subset _,hud.2⟩; exact hud
  have hvc : v.cache = u.cache := by dsimp [v]; split <;> rfl
  unfold step at ht
  change t ∈ (if z ∈ u.cache ∨ u.cache.card < k then _ else _ : PMF (PMState α)).support at ht
  by_cases hf : z ∈ u.cache ∨ u.cache.card < k
  · rw [if_pos hf,PMF.mem_support_pure_iff] at ht
    subst t
    exact load hu _
  · rw [if_neg hf] at ht
    have hzc : z ∉ v.cache := by rw [hvc]; exact (not_or.mp hf).1
    have hfull : k ≤ v.cache.card := by rw [hvc]; exact Nat.le_of_not_gt (not_or.mp hf).2
    have hm : v.marked.card < k := by
      dsimp [v]; split
      · simpa using (show 0 < k by omega)
      · rename_i hne
        have hle := (Finset.card_le_card hud.1).trans hud.2
        omega
    have hne := RunBounds.unmarked_nonempty hvd hfull hm
    change t ∈ (if z ∉ v.stale then _ else _ : PMF (PMState α)).support at ht
    by_cases hclean : z ∉ v.stale
    · rw [if_pos hclean,PMF.mem_support_pure_iff] at ht
      subst t
      let w : PMState α := {v with clean := v.clean+1, chainLen := Function.update v.chainLen v.phase (Function.update (v.chainLen v.phase) (v.clean+1) 1)}
      apply evict (s := w) ⟨hv.unmarked,hv.unique,hv.last⟩ (v.clean+1) (htb w hne).1
      intro x hx _
      have hxc := Finset.mem_sdiff.mp hx
      have hbnd := hvb.missing x hxc.1 hxc.2
      change v.chainOf x ≠ v.clean+1
      omega
    · rw [if_neg hclean] at ht
      have hzs : z ∈ v.stale \ v.cache := Finset.mem_sdiff.mpr ⟨not_not.mp hclean,hzc⟩
      have sep : ∀ x ∈ v.stale \ v.cache, x ≠ z → v.chainOf x ≠ v.chainOf z := by
        intro x hx hxz he
        exact hxz (hv.unique x hx z hzs he)
      let w := Bookkeeping.bump v (v.chainOf z)
      have hw : Coherent w (some z) := ⟨hv.unmarked,hv.unique,hv.last⟩
      change t ∈ (if ((v.chainLen v.phase (v.chainOf z) + 1 : ℕ) : ℝ) ≤
        (harmonic k : ℝ) then _ else _ : PMF (PMState α)).support at ht
      by_cases hp : ((v.chainLen v.phase (v.chainOf z)+1 : ℕ) : ℝ) ≤ (harmonic k : ℝ)
      · rw [if_pos hp,PMF.mem_support_pure_iff] at ht
        subst t
        exact evict hw (v.chainOf z) (htb w hne).1 sep
      · rw [if_neg hp,dif_pos hne,PMF.mem_support_map_iff] at ht
        obtain ⟨e,he,rfl⟩ := ht
        rw [PMF.mem_support_uniformOfFinset_iff] at he
        exact evict (s := {w with randomChains := insert (v.phase,v.chainOf z) w.randomChains})
          ⟨hv.unmarked,hv.unique,hv.last⟩ (v.chainOf z) he sep

theorem run_coherent (k : ℕ) (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {s : PMState α} (hs : s ∈ (run k tb σ h).support) : Coherent s := by
  let P := fun s : PMState α => Coherent s ∧ Bookkeeping.Coherent s ∧ RunBounds.Bounded k s
  have hi : P (initState α) := by
    refine ⟨?_,?_,?_⟩
    · constructor <;> simp [initState]
    · constructor <;> simp [initState]
    · simp [RunBounds.Bounded,initState]
  have hstep : ∀ s, P s → ∀ i z hz t, t ∈ (step k tb s i z hz).support → P t := by
    intro s hs i z hz t ht
    exact ⟨step_coherent k hk tb htb hs.1 hs.2.1 hs.2.2 i z hz ht,
      Bookkeeping.step_coherent k tb hs.2.1 i z hz ht,
      RunBounds.step_bounded k hk tb htb hs.2.2 i z hz ht⟩
  exact (RunBounds.run_invariant P k tb hi hstep σ h hs).1

#print axioms run_coherent
end CachingML.PredMarker.Representatives

namespace CachingML.PredMarker.Representatives
variable {α : Type*} [DecidableEq α]

/-- Stale pages either remain from the phase or are reset to the preceding cache. -/
theorem step_stale (k : ℕ) (tb : PMState α → α) (s : PMState α)
    (i : ℕ) (z : α) (hz : ℝ) {t : PMState α}
    (ht : t ∈ (step k tb s i z hz).support) :
    t.stale = s.stale ∨ t.stale = s.cache := by
  classical
  let u : PMState α := {s with pred := Function.update s.pred z hz, predIdx := Function.update s.predIdx z i}
  let v : PMState α := if u.marked.card = k then
    {u with phase := u.phase+1, clean := 0, stale := u.cache, marked := ∅} else u
  have hv : v.stale = s.stale ∨ v.stale = s.cache := by
    dsimp [v]; split; exact Or.inr rfl; exact Or.inl rfl
  unfold step at ht
  change t ∈ (if z ∈ u.cache ∨ u.cache.card < k then _ else _ : PMF (PMState α)).support at ht
  split at ht
  · rw [PMF.mem_support_pure_iff] at ht
    subst t
    exact Or.inl rfl
  · change t ∈ (if z ∉ v.stale then _ else _ : PMF (PMState α)).support at ht
    split at ht
    · rw [PMF.mem_support_pure_iff] at ht
      subst t
      exact hv
    · change t ∈ (if ((v.chainLen v.phase (v.chainOf z)+1 : ℕ) : ℝ) ≤ (harmonic k : ℝ)
        then _ else _ : PMF (PMState α)).support at ht
      split at ht
      · rw [PMF.mem_support_pure_iff] at ht
        subst t
        exact hv
      · by_cases hne : (v.cache \ v.marked).Nonempty
        · rw [dif_pos hne,PMF.mem_support_map_iff] at ht
          obtain ⟨e,_,rfl⟩ := ht
          exact hv
        · rw [dif_neg hne,PMF.mem_support_pure_iff] at ht
          subst t
          exact hv

def Seen (σ : List α) (n : ℕ) (s : PMState α) : Prop :=
  ∀ x ∈ s.stale, ∃ j : Fin σ.length, j.val < n ∧ σ.get j = x

theorem step_seen (k : ℕ) (tb : PMState α → α) (σ : List α)
    (h : Fin σ.length → ℝ) (i : Fin σ.length) {s : PMState α}
    (hs : Seen σ i.val s) (hc : History.Saved σ h i.val s) {t : PMState α}
    (ht : t ∈ (step k tb s i.val (σ.get i) (h i)).support) : Seen σ (i.val+1) t := by
  intro x hx
  rcases step_stale k tb s i.val (σ.get i) (h i) ht with he | he
  · obtain ⟨j,hjn,hjx⟩ := hs x (he ▸ hx)
    exact ⟨j,by omega,hjx⟩
  · obtain ⟨j,hjn,hjx,_⟩ := hc x (he ▸ hx)
    exact ⟨j,by omega,hjx⟩

theorem prefix_seen (k : ℕ) (tb : PMState α → α) (σ : List α)
    (h : Fin σ.length → ℝ) (n : ℕ) (hn : n ≤ σ.length) {s : PMState α}
    (hs : s ∈ (History.prefixRun k tb σ h n).support) : Seen σ n s := by
  have hh := History.prefix_invariant k tb σ h
    (fun n s => Seen σ n s ∧ History.Saved σ h n s)
    (show Seen σ 0 (initState α) ∧ History.Saved σ h 0 (initState α) from
      ⟨by simp [Seen,initState],History.saved_init σ h⟩)
    (fun i s hs t ht => ⟨step_seen k tb σ h i hs.1 hs.2 ht,
      History.step_history k tb σ h i hs.2 ht⟩) n hn hs
  exact hh.1

theorem prefix_invariants (k : ℕ) (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    (n : ℕ) (hn : n ≤ σ.length) {s : PMState α}
    (hs : s ∈ (History.prefixRun k tb σ h n).support) :
    Coherent s ∧ Bookkeeping.Coherent s ∧ RunBounds.Bounded k s := by
  let P := fun (_ : ℕ) (s : PMState α) => Coherent s ∧ Bookkeeping.Coherent s ∧ RunBounds.Bounded k s
  have hi : P 0 (initState α) := by
    refine ⟨?_,?_,?_⟩
    · constructor <;> simp [initState]
    · constructor <;> simp [initState]
    · simp [RunBounds.Bounded,initState]
  have hstep : ∀ i : Fin σ.length, ∀ s, P i.val s → ∀ t,
      t ∈ (step k tb s i.val (σ.get i) (h i)).support → P (i.val+1) t := by
    intro i s hs t ht
    exact ⟨step_coherent k hk tb htb hs.1 hs.2.1 hs.2.2 i.val (σ.get i) (h i) ht,
      Bookkeeping.step_coherent k tb hs.2.1 i.val (σ.get i) (h i) ht,
      RunBounds.step_bounded k hk tb htb hs.2.2 i.val (σ.get i) (h i) ht⟩
  exact History.prefix_invariant k tb σ h P hi hstep n hn hs

/-- An actual absent stale request continues the chain whose tail is its previous
request, with the exact next-arrival label of the current request. -/
theorem rerequest_chain_tail (k : ℕ) (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    (i : Fin σ.length) {s : PMState α}
    (hs : s ∈ (History.prefixRun k tb σ h i.val).support)
    (hz : σ.get i ∈ s.stale \ s.cache) :
    ∃ j : Fin σ.length, j.val < i.val ∧ σ.get j = σ.get i ∧
      (s.chainIdx s.phase (s.chainOf (σ.get i))).getLast? = some j.val ∧
      s.pred (σ.get i) = h j ∧ nextArrival σ j = i.val+1 := by
  have hn : i.val ≤ σ.length := Nat.le_of_lt i.isLt
  have hr := (prefix_invariants k hk tb htb σ h i.val hn hs).1
  have hm := History.prefix_remembered k tb σ h i.val hn hs
  have hv := prefix_seen k tb σ h i.val hn hs
  obtain ⟨j,hji,hjz,hidx,hpred,hnxt⟩ := History.remembered_rerequest σ h i hm
    (hv (σ.get i) (Finset.mem_sdiff.mp hz).1)
  refine ⟨j,hji,hjz,?_,hpred,hnxt⟩
  exact (hr.last (σ.get i) hz (by simp)).trans (congrArg some hidx)

/-- At a stale miss, any different cached page's saved request has a strictly
later actual arrival than the existing chain tail. -/
theorem rerequest_eviction_order (k : ℕ) (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    (i : Fin σ.length) {s : PMState α}
    (hs : s ∈ (History.prefixRun k tb σ h i.val).support)
    (hz : σ.get i ∈ s.stale \ s.cache) {e : α} (he : e ∈ s.cache) :
    ∃ a b : Fin σ.length,
      (s.chainIdx s.phase (s.chainOf (σ.get i))).getLast? = some a.val ∧
      s.predIdx e = b.val ∧ s.pred (σ.get i) = h a ∧ s.pred e = h b ∧
      nextArrival σ a < nextArrival σ b := by
  obtain ⟨a,_,_,ha,hpa,hna⟩ := rerequest_chain_tail k hk tb htb σ h i hs hz
  have hen : e ≠ σ.get i := by
    intro h; subst e; exact (Finset.mem_sdiff.mp hz).2 he
  obtain ⟨b,_,_,hb,hpb,hnb⟩ := History.saved_other_nextArrival σ h i
    (History.prefix_saved k tb σ h i.val (Nat.le_of_lt i.isLt) hs) he hen
  exact ⟨a,b,ha,hb,hpa,hpb,by omega⟩

#print axioms rerequest_eviction_order
end CachingML.PredMarker.Representatives

namespace CachingML.PredMarker.Representatives
variable {α : Type*} [DecidableEq α]

noncomputable def arrivalAt (σ : List α) (n : ℕ) : ℕ :=
  if hn : n < σ.length then nextArrival σ ⟨n,hn⟩ else 0

theorem arrivalAt_fin (σ : List α) (j : Fin σ.length) :
    arrivalAt σ j.val = nextArrival σ j := by simp [arrivalAt,j.isLt]

def EntryOrdered (σ : List α) (L : List ℕ) : Prop :=
  (∀ j ∈ L, j < σ.length) ∧ L.Pairwise (fun a b => arrivalAt σ a < arrivalAt σ b)

def ChainOrdered (σ : List α) (s : PMState α) : Prop :=
  ∀ r c, EntryOrdered σ (s.chainIdx r c)

theorem before_of_last {L : List ℕ} {f : ℕ → ℕ}
    (ho : L.Pairwise (fun a b => f a < f b)) {a b : ℕ}
    (hl : L.getLast? = some a) (hab : f a < f b) : ∀ x ∈ L, f x < f b := by
  obtain ⟨xs,rfl⟩ := List.getLast?_eq_some_iff.mp hl
  have hall := (List.pairwise_append.mp ho).2.2
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact (hall x hx a (by simp)).trans hab
  · simpa using (show f x < f b from (List.mem_singleton.mp hx) ▸ hab)

theorem append_ordered {σ : List α} {L : List ℕ} (ho : EntryOrdered σ L)
    {b : ℕ} (hb : b < σ.length) (hall : ∀ a ∈ L, arrivalAt σ a < arrivalAt σ b) :
    EntryOrdered σ (L ++ [b]) := by
  constructor
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact ho.1 a ha
    · have hab : a = b := List.mem_singleton.mp ha
      simpa [hab] using hb
  · rw [List.pairwise_append]
    exact ⟨ho.2,by simp,by simpa using hall⟩

theorem evict_ordered {σ : List α} {s : PMState α} (hs : ChainOrdered σ s)
    (z : α) (c : ℕ) (e : α)
    (hnew : EntryOrdered σ (s.chainIdx s.phase c ++ [s.predIdx e])) :
    ChainOrdered σ (evictInto s z c e) := by
  intro r d
  by_cases hr : r = s.phase <;> by_cases hd : d = c
  · simpa [evictInto,hr,hd] using hnew
  · simpa [evictInto,Function.update_apply,hr,hd] using hs r d
  · simpa [evictInto,Function.update_apply,hr,hd] using hs r d
  · simpa [evictInto,Function.update_apply,hr,hd] using hs r d

theorem step_arrival_order (k : ℕ) (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    (i : Fin σ.length) {s : PMState α}
    (hs : s ∈ (History.prefixRun k tb σ h i.val).support)
    (ho : ChainOrdered σ s) {t : PMState α}
    (ht : t ∈ (step k tb s i.val (σ.get i) (h i)).support) : ChainOrdered σ t := by
  classical
  let z := σ.get i
  have hb := (prefix_invariants k hk tb htb σ h i.val (Nat.le_of_lt i.isLt) hs).2.1
  have hbound := (prefix_invariants k hk tb htb σ h i.val (Nat.le_of_lt i.isLt) hs).2.2
  let u : PMState α := {s with pred := Function.update s.pred z (h i), predIdx := Function.update s.predIdx z i.val}
  have hub : Bookkeeping.Coherent u := ⟨hb.lengths,hb.fresh,hb.missing⟩
  have hud : RunBounds.Bounded k u := hbound
  let v : PMState α := if u.marked.card = k then
    {u with phase := u.phase+1, clean := 0, stale := u.cache, marked := ∅} else u
  have hvb : Bookkeeping.Coherent v := by
    dsimp [v]; split; exact Bookkeeping.reset_coherent hub; exact hub
  have hvd : RunBounds.Bounded k v := by
    dsimp [v]; split; exact ⟨Finset.empty_subset _,hud.2⟩; exact hud
  have hvc : v.cache = s.cache := by dsimp [v]; split <;> rfl
  have hvi : v.predIdx = Function.update s.predIdx z i.val := by dsimp [v]; split <;> rfl
  have hvchain : v.chainIdx = s.chainIdx := by dsimp [v]; split <;> rfl
  have hov : ChainOrdered σ v := by intro r c; simpa [hvchain] using ho r c
  unfold step at ht
  change t ∈ (if z ∈ u.cache ∨ u.cache.card < k then _ else _ : PMF (PMState α)).support at ht
  by_cases hf : z ∈ u.cache ∨ u.cache.card < k
  · rw [if_pos hf,PMF.mem_support_pure_iff] at ht
    subst t
    exact ho
  · rw [if_neg hf] at ht
    have hzc : z ∉ v.cache := by rw [hvc]; exact (not_or.mp hf).1
    have hfull : k ≤ v.cache.card := by rw [hvc]; exact Nat.le_of_not_gt (not_or.mp hf).2
    have hm : v.marked.card < k := by
      dsimp [v]; split
      · simpa using (show 0 < k by omega)
      · rename_i hne
        have hle := (Finset.card_le_card hud.1).trans hud.2
        omega
    have hne := RunBounds.unmarked_nonempty hvd hfull hm
    have hidx : ∀ e ∈ v.cache, v.predIdx e = s.predIdx e ∧ v.predIdx e < σ.length := by
      intro e he
      have hez : e ≠ z := by intro hez; subst e; exact hzc he
      have hec : e ∈ s.cache := by simpa [hvc] using he
      obtain ⟨j,_,_,hij,_⟩ := History.prefix_saved k tb σ h i.val (Nat.le_of_lt i.isLt) hs e hec
      have hie : v.predIdx e = s.predIdx e := by rw [hvi,Function.update_of_ne hez]
      exact ⟨hie,by rw [hie,hij]; exact j.isLt⟩
    change t ∈ (if z ∉ v.stale then _ else _ : PMF (PMState α)).support at ht
    by_cases hclean : z ∉ v.stale
    · rw [if_pos hclean,PMF.mem_support_pure_iff] at ht
      subst t
      let w : PMState α := {v with clean := v.clean+1, chainLen := Function.update v.chainLen v.phase (Function.update (v.chainLen v.phase) (v.clean+1) 1)}
      have he := (htb w hne).1
      have hec : tb w ∈ v.cache := (Finset.mem_sdiff.mp he).1
      apply evict_ordered (s := w) hov z (v.clean+1) (tb w)
      change EntryOrdered σ (v.chainIdx v.phase (v.clean+1) ++ [v.predIdx (tb w)])
      rw [hvb.fresh _ _ (Or.inr ⟨rfl,by omega⟩)]
      exact append_ordered (by simp [EntryOrdered]) (hidx _ hec).2 (by simp)
    · rw [if_neg hclean] at ht
      have hreset : u.marked.card ≠ k := by
        intro he
        have hvs : v.stale = v.cache := by simp [v,he]
        exact hzc (hvs ▸ not_not.mp hclean)
      have hvu : v = u := by simp [v,hreset]
      have hzs : σ.get i ∈ s.stale \ s.cache := by
        apply Finset.mem_sdiff.mpr
        exact ⟨by simpa [hvu,u,z] using not_not.mp hclean,(not_or.mp hf).1⟩
      have hnew : ∀ e ∈ v.cache, EntryOrdered σ
          (v.chainIdx v.phase (v.chainOf z) ++ [v.predIdx e]) := by
        intro e he
        have hec : e ∈ s.cache := by simpa [hvc] using he
        obtain ⟨a,b,ha,hbi,_,_,hab⟩ := rerequest_eviction_order k hk tb htb σ h i hs hzs hec
        apply append_ordered (hov _ _) (hidx e he).2
        have htail : (v.chainIdx v.phase (v.chainOf z)).getLast? = some a.val := by
          simpa [hvu,u,z] using ha
        apply before_of_last (hov _ _).2 htail
        rw [arrivalAt_fin,(hidx e he).1,hbi,arrivalAt_fin]
        exact hab
      let w := Bookkeeping.bump v (v.chainOf z)
      change t ∈ (if ((v.chainLen v.phase (v.chainOf z) + 1 : ℕ) : ℝ) ≤
        (harmonic k : ℝ) then _ else _ : PMF (PMState α)).support at ht
      by_cases hp : ((v.chainLen v.phase (v.chainOf z)+1 : ℕ) : ℝ) ≤ (harmonic k : ℝ)
      · rw [if_pos hp,PMF.mem_support_pure_iff] at ht
        subst t
        exact evict_ordered (s := w) hov z (v.chainOf z) (tb w)
          (hnew _ (Finset.mem_sdiff.mp (htb w hne).1).1)
      · rw [if_neg hp,dif_pos hne,PMF.mem_support_map_iff] at ht
        obtain ⟨e,he,rfl⟩ := ht
        rw [PMF.mem_support_uniformOfFinset_iff] at he
        exact evict_ordered (s := {w with randomChains := insert (v.phase,v.chainOf z) w.randomChains})
          hov z (v.chainOf z) e (hnew _ (Finset.mem_sdiff.mp he).1)

theorem prefix_arrival_order (k : ℕ) (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    (n : ℕ) (hn : n ≤ σ.length) {s : PMState α}
    (hs : s ∈ (History.prefixRun k tb σ h n).support) : ChainOrdered σ s := by
  induction n generalizing s with
  | zero =>
    have he : s = initState α := by
      simpa only [History.prefixRun,List.take_zero,List.foldl_nil,PMF.mem_support_pure_iff] using hs
    subst s
    simp [ChainOrdered,EntryOrdered,initState]
  | succ n ih =>
    have hlt : n < σ.length := by omega
    rw [History.prefixRun_succ k tb σ h n hlt,PMF.mem_support_bind_iff] at hs
    obtain ⟨u,hu,ht⟩ := hs
    exact step_arrival_order k hk tb htb σ h ⟨n,hlt⟩ hu (ih (by omega) hu) ht

theorem run_arrival_order (k : ℕ) (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {s : PMState α} (hs : s ∈ (run k tb σ h).support) : ChainOrdered σ s := by
  apply prefix_arrival_order k hk tb htb σ h σ.length le_rfl
  have htake : (List.finRange σ.length).take σ.length = List.finRange σ.length :=
    List.take_of_length_le (by simp)
  simpa only [History.prefixRun,run,htake] using hs

#print axioms run_arrival_order

/-- Convert the stored natural indices into valid request indices without changing
any chain entry, retaining strict order of actual arrivals. -/
theorem ordered_indices (σ : List α) (L : List ℕ) (ho : EntryOrdered σ L) :
    ∃ j : Fin L.length → Fin σ.length,
      List.ofFn (fun i => (j i).val) = L ∧ StrictMono (fun i => nextArrival σ (j i)) := by
  let j : Fin L.length → Fin σ.length := fun i => ⟨L.get i,ho.1 _ (List.get_mem L i)⟩
  refine ⟨j,?_,?_⟩
  · exact List.ofFn_get L
  · intro a b hab
    have hh := (List.pairwise_iff_get.mp ho.2) a b hab
    change arrivalAt σ (j a).val < arrivalAt σ (j b).val at hh
    simpa only [arrivalAt_fin] using hh

theorem run_arrival_certificate (k : ℕ) (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {s : PMState α} (hs : s ∈ (run k tb σ h).support) (r c : ℕ) :
    ∃ j : Fin (s.chainLen r c) → Fin σ.length,
      List.ofFn (fun i => (j i).val) = s.chainIdx r c ∧
      StrictMono (fun i => nextArrival σ (j i)) := by
  rw [← Bookkeeping.run_chain_length k tb σ h hs r c]
  exact ordered_indices σ (s.chainIdx r c) (run_arrival_order k hk tb htb σ h hs r c)

#print axioms run_arrival_certificate
end CachingML.PredMarker.Representatives

namespace CachingML.PredMarker.SpreadCertificate
open Finset Set
variable (ℓ : ℝ → ℝ → ℝ)

theorem attained {m : ℝ} {t : ℕ} (ht : spread ℓ m = t) :
    1 ≤ t ∧ ∀ a : Fin t → ℤ, StrictMono a → ∀ b : Fin t → ℝ, Antitone b →
      m ≤ ∑ i, ℓ (a i) (b i) := by
  let U : Set ℕ∞ := {T | ∃ j : ℕ, T = j ∧ 1 ≤ j ∧
    ∀ a : Fin j → ℤ, StrictMono a → ∀ b : Fin j → ℝ, Antitone b →
      m ≤ ∑ i, ℓ (a i) (b i)}
  have hu : U.Nonempty := by
    by_contra hn
    have he : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have : (⊤ : ℕ∞) = t := by simpa [spread, U, he] using ht
    simpa using this
  have hm : (t : ℕ∞) ∈ U := by rw [← ht]; exact csInf_mem hu
  obtain ⟨j,hj,hpos,hall⟩ := hm
  have : t = j := by exact_mod_cast hj
  subst j
  exact ⟨hpos,hall⟩

theorem prefix_cost_le (hℓ : ∀ a b, 0 ≤ ℓ a b) {n t : ℕ} (ht : t ≤ n)
    (a : Fin n → ℤ) (b : Fin n → ℝ) :
    (∑ i : Fin t, ℓ (a (Fin.castLE ht i)) (b (Fin.castLE ht i))) ≤
      ∑ i : Fin n, ℓ (a i) (b i) := by
  classical
  let e : Fin t → Fin n := Fin.castLE ht
  calc
    _ = ∑ i ∈ (Finset.univ.image e), ℓ (a i) (b i) := by
      rw [Finset.sum_image]
      intro i hi j hj he
      exact Fin.ext (congrArg (fun x : Fin n => x.val) he)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => hℓ _ _)

theorem length_lt_of_cost_lt (hℓ : ∀ a b, 0 ≤ ℓ a b) {n t : ℕ}
    (a : Fin n → ℤ) (ha : StrictMono a) (b : Fin n → ℝ) (hb : Antitone b)
    {m : ℝ} (hm : (∑ i, ℓ (a i) (b i)) < m) (ht : spread ℓ m = t) : n < t := by
  by_contra hn
  have htn : t ≤ n := Nat.le_of_not_gt hn
  have h := (attained ℓ ht).2 (fun i => a (Fin.castLE htn i))
    (fun _ _ hij => ha hij) (fun i => b (Fin.castLE htn i)) (fun _ _ hij => hb hij)
  exact (hm.trans_le h).not_ge (prefix_cost_le ℓ hℓ htn a b)

theorem length_add_one_le_majorant (hℓ : ∀ a b, 0 ≤ ℓ a b)
    (S : ℝ → ℝ) (hcont : ContinuousOn S (Ici 0))
    (hspread : ∀ m : ℝ, 0 ≤ m → ∃ t : ℕ, spread ℓ m = t ∧ (t : ℝ) ≤ S m)
    {n : ℕ} (a : Fin n → ℤ) (ha : StrictMono a) (b : Fin n → ℝ) (hb : Antitone b)
    (E : ℝ) (hE : (∑ i, ℓ (a i) (b i)) ≤ E) : (n : ℝ) + 1 ≤ S E := by
  have hE0 : 0 ≤ E := (Finset.sum_nonneg (fun i _ => hℓ _ _)).trans hE
  apply ContinuousWithinAt.closure_le (s := Ioi E)
    (by simp [closure_Ioi]) continuousWithinAt_const
    ((hcont E hE0).mono (fun x hx => hE0.trans hx.le))
  intro m hm
  obtain ⟨t,ht,hbound⟩ := hspread m (hE0.trans hm.le)
  have hn := length_lt_of_cost_lt ℓ hℓ a ha b hb (hE.trans_lt hm) ht
  have : (n : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast hn
  exact this.trans hbound

theorem length_add_one_le_concave_majorant (hℓ : ∀ a b, 0 ≤ ℓ a b)
    (S : ℝ → ℝ) (hconc : ConcaveOn ℝ (Ici 0) S)
    (hcont : ContinuousWithinAt S (Ici 0) 0)
    (hspread : ∀ m : ℝ, 0 ≤ m → ∃ t : ℕ, spread ℓ m = t ∧ (t : ℝ) ≤ S m)
    {n : ℕ} (a : Fin n → ℤ) (ha : StrictMono a) (b : Fin n → ℝ) (hb : Antitone b)
    (E : ℝ) (hE : (∑ i, ℓ (a i) (b i)) ≤ E) : (n : ℝ) + 1 ≤ S E :=
  length_add_one_le_majorant ℓ hℓ S (hconc.continuousOn_Ici hcont) hspread a ha b hb E hE

#print axioms length_add_one_le_concave_majorant
end CachingML.PredMarker.SpreadCertificate

namespace CachingML.PredMarker.ChainCertificate
variable {α : Type*} [DecidableEq α]
/-- A concrete ordering certificate for the actual saved request indices.
Proving this certificate for supported algorithm runs remains a separate obligation. -/
def Ordered (σ : List α) (h : Fin σ.length → ℝ) (s : PMState α) (r c : ℕ) : Prop :=
  ∃ j : Fin (s.chainLen r c) → Fin σ.length,
    List.ofFn (fun i => (j i).val) = s.chainIdx r c ∧
    StrictMono (fun i => nextArrival σ (j i)) ∧ Antitone (fun i => h (j i))

theorem chainError_nonneg (ℓ : ℝ → ℝ → ℝ) (hℓ : ∀ a b, 0 ≤ ℓ a b)
    (σ : List α) (h : Fin σ.length → ℝ) (s : PMState α) (r c : ℕ) :
    0 ≤ chainError ℓ σ h s r c := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
  unfold lossAt
  split
  · exact hℓ _ _
  · exact le_rfl

theorem bound_of_ordered (ℓ : ℝ → ℝ → ℝ) (hℓ : ∀ a b, 0 ≤ ℓ a b)
    (S : ℝ → ℝ) (hconc : ConcaveOn ℝ (Set.Ici 0) S)
    (hcont : ContinuousWithinAt S (Set.Ici 0) 0)
    (hspread : ∀ m : ℝ, 0 ≤ m → ∃ t : ℕ, spread ℓ m = t ∧ (t : ℝ) ≤ S m)
    (σ : List α) (h : Fin σ.length → ℝ) (s : PMState α) (r c : ℕ)
    (hc : Ordered σ h s r c) : (s.chainLen r c : ℝ) + 1 ≤ S (chainError ℓ σ h s r c) := by
  obtain ⟨j,hj,ha,hb⟩ := hc
  have hsum : (∑ i, ℓ (nextArrival σ (j i)) (h (j i))) = chainError ℓ σ h s r c := by
    unfold chainError
    rw [← hj,List.map_ofFn,List.sum_ofFn]
    congr 1
    funext i
    simp [lossAt,(j i).isLt]
  apply SpreadCertificate.length_add_one_le_concave_majorant ℓ hℓ S hconc hcont hspread
    (fun i => (nextArrival σ (j i) : ℤ)) (fun i l hil => by
      change (nextArrival σ (j i) : ℤ) < (nextArrival σ (j l) : ℤ)
      exact_mod_cast (show nextArrival σ (j i) < nextArrival σ (j l) from ha hil))
    (fun i => h (j i)) hb
  simpa using hsum.le

theorem platform_bound_of_ordered (ℓ : ℝ → ℝ → ℝ) (hℓ : ∀ a b, 0 ≤ ℓ a b)
    (S : ℝ → ℝ) (hconc : ConcaveOn ℝ (Set.Ici 0) S)
    (hcont : ContinuousWithinAt S (Set.Ici 0) 0)
    (hspread : ∀ m : ℝ, 0 ≤ m → ∃ t : ℕ, spread ℓ m = t ∧ (t : ℝ) ≤ S m)
    (σ : List α) (h : Fin σ.length → ℝ) (s : PMState α) (r c : ℕ)
    (hc : Ordered σ h s r c) : (s.chainLen r c : ℝ) ≤ 1 + S (chainError ℓ σ h s r c) := by
  have hb := bound_of_ordered ℓ hℓ S hconc hcont hspread σ h s r c hc
  linarith
#print axioms platform_bound_of_ordered
end CachingML.PredMarker.ChainCertificate

namespace CachingML.PredMarker.Predictions
variable {α : Type*} [DecidableEq α]
set_option maxHeartbeats 1000000

noncomputable def predAt (σ : List α) (h : Fin σ.length → ℝ) (n : ℕ) : ℝ :=
  if hn : n < σ.length then h ⟨n,hn⟩ else 0

theorem predAt_fin (σ : List α) (h : Fin σ.length → ℝ) (j : Fin σ.length) :
    predAt σ h j.val = h j := by simp [predAt,j.isLt]

structure Coherent (σ : List α) (h : Fin σ.length → ℝ)
    (s : PMState α) (except : Option α := none) : Prop where
  ordered : ∀ r c, (r,c) ∉ s.randomChains →
    (s.chainIdx r c).Pairwise (fun a b => predAt σ h b ≤ predAt σ h a)
  cap : ∀ c, (s.phase,c) ∉ s.randomChains → ∀ a ∈ s.chainIdx s.phase c,
    ∀ e ∈ s.cache \ s.marked, except ≠ some e → s.pred e ≤ predAt σ h a

theorem prepare {σ : List α} {h : Fin σ.length → ℝ} {s : PMState α}
    (hs : Coherent σ h s) (z : α) (i : ℕ) (hz : ℝ) :
    Coherent σ h {s with pred := Function.update s.pred z hz, predIdx := Function.update s.predIdx z i} (some z) := by
  refine ⟨hs.ordered,?_⟩
  intro c hc a ha e he hne
  have hez : e ≠ z := by intro hh; subst e; exact hne rfl
  simpa [Function.update_of_ne hez] using hs.cap c hc a ha e he (by simp)

theorem reset {σ : List α} {h : Fin σ.length → ℝ} {s : PMState α} {except : Option α}
    (hs : Coherent σ h s except) (hb : Bookkeeping.Coherent s) :
    Coherent σ h {s with phase := s.phase+1, clean := 0, stale := s.cache, marked := ∅} except := by
  refine ⟨hs.ordered,?_⟩
  intro c hc a ha
  change a ∈ s.chainIdx (s.phase+1) c at ha
  rw [hb.fresh _ _ (Or.inl (by omega))] at ha
  simp at ha

theorem load {σ : List α} {h : Fin σ.length → ℝ} {s : PMState α} {z : α}
    (hs : Coherent σ h s (some z)) (m : ℕ) :
    Coherent σ h {s with cache := insert z s.cache, marked := insert z s.marked, misses := m} := by
  refine ⟨hs.ordered,?_⟩
  intro c hc a ha e he _
  change e ∈ insert z s.cache \ insert z s.marked at he
  obtain ⟨hec,hem⟩ := Finset.mem_sdiff.mp he
  have hez : e ≠ z := by intro hh; subst e; exact hem (Finset.mem_insert_self _ _)
  have hold : e ∈ s.cache \ s.marked := Finset.mem_sdiff.mpr
    ⟨(Finset.mem_insert.mp hec).resolve_left hez,fun hm => hem (Finset.mem_insert_of_mem hm)⟩
  exact hs.cap c hc a ha e hold (by simpa [eq_comm] using hez)

theorem mark_random {σ : List α} {h : Fin σ.length → ℝ} {s : PMState α} {except : Option α}
    (hs : Coherent σ h s except) (r c : ℕ) :
    Coherent σ h {s with randomChains := insert (r,c) s.randomChains} except := by
  constructor
  · intro a b hn
    exact hs.ordered a b (fun hh => hn (Set.mem_insert_of_mem _ hh))
  · intro b hn
    exact hs.cap b (fun hh => hn (Set.mem_insert_of_mem _ hh))

theorem evict {σ : List α} {h : Fin σ.length → ℝ} {s : PMState α} {z e : α}
    (hs : Coherent σ h s (some z)) (c : ℕ) (hz : z ∉ s.cache)
    (he : e ∈ s.cache \ s.marked) (hp : predAt σ h (s.predIdx e) = s.pred e)
    (hmax : (s.phase,c) ∉ s.randomChains → ∀ x ∈ s.cache \ s.marked, s.pred x ≤ s.pred e) :
    Coherent σ h (evictInto s z c e) := by
  have hez : e ≠ z := by intro hh; subst e; exact hz (Finset.mem_sdiff.mp he).1
  have old : ∀ x ∈ (evictInto s z c e).cache \ (evictInto s z c e).marked,
      x ∈ s.cache \ s.marked ∧ x ≠ z := by
    intro x hx
    change x ∈ insert z (s.cache.erase e) \ insert z s.marked at hx
    obtain ⟨hxc,hxm⟩ := Finset.mem_sdiff.mp hx
    have hxz : x ≠ z := by intro hh; subst x; exact hxm (Finset.mem_insert_self _ _)
    exact ⟨Finset.mem_sdiff.mpr
      ⟨Finset.mem_of_mem_erase ((Finset.mem_insert.mp hxc).resolve_left hxz),
        fun hh => hxm (Finset.mem_insert_of_mem hh)⟩,hxz⟩
  constructor
  · intro r d hc
    change (r,d) ∉ s.randomChains at hc
    by_cases hr : r=s.phase
    · subst r
      by_cases hd : d=c
      · subst d
        simp only [evictInto,Function.update_self]
        rw [List.pairwise_append]
        refine ⟨hs.ordered _ _ hc,by simp,?_⟩
        intro a ha b hb
        have hb' : b=s.predIdx e := List.mem_singleton.mp hb
        subst b
        rw [hp]
        exact hs.cap c hc a ha e he (by simpa [eq_comm] using hez)
      · simpa [evictInto,Function.update_of_ne hd] using hs.ordered s.phase d hc
    · simpa [evictInto,Function.update_of_ne hr] using hs.ordered r d hc
  · intro d hc a ha x hx _
    have hxc := old x hx
    have hne : some z ≠ some x := by simpa [eq_comm] using hxc.2
    change (s.phase,d) ∉ s.randomChains at hc
    change s.pred x ≤ predAt σ h a
    by_cases hd : d=c
    · subst d
      simp only [evictInto,Function.update_self] at ha
      rcases List.mem_append.mp ha with ha|ha
      · exact hs.cap c hc a ha x hxc.1 hne
      · have ha' : a=s.predIdx e := List.mem_singleton.mp ha
        rw [ha',hp]
        exact hmax hc x hxc.1
    · have ha' : a ∈ s.chainIdx s.phase d := by
        simpa [evictInto,Function.update_of_ne hd] using ha
      exact hs.cap d hc a ha' x hxc.1 hne

end CachingML.PredMarker.Predictions

namespace CachingML.PredMarker.Predictions
variable {α : Type*} [DecidableEq α]
set_option maxHeartbeats 2000000

theorem step_coherent (k : ℕ) (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    (i : Fin σ.length) {s : PMState α}
    (hs : s ∈ (History.prefixRun k tb σ h i.val).support)
    (ho : Coherent σ h s) {t : PMState α}
    (ht : t ∈ (step k tb s i.val (σ.get i) (h i)).support) : Coherent σ h t := by
  classical
  let z := σ.get i
  have hb := (Representatives.prefix_invariants k hk tb htb σ h i.val (Nat.le_of_lt i.isLt) hs).2.1
  have hbound := (Representatives.prefix_invariants k hk tb htb σ h i.val (Nat.le_of_lt i.isLt) hs).2.2
  let u : PMState α := {s with pred := Function.update s.pred z (h i), predIdx := Function.update s.predIdx z i.val}
  have hu : Coherent σ h u (some z) := prepare ho z i.val (h i)
  have hub : Bookkeeping.Coherent u := ⟨hb.lengths,hb.fresh,hb.missing⟩
  have hud : RunBounds.Bounded k u := hbound
  let v : PMState α := if u.marked.card = k then
    {u with phase := u.phase+1, clean := 0, stale := u.cache, marked := ∅} else u
  have hv : Coherent σ h v (some z) := by
    dsimp [v]; split; exact reset hu hub; exact hu
  have hvd : RunBounds.Bounded k v := by
    dsimp [v]; split; exact ⟨Finset.empty_subset _,hud.2⟩; exact hud
  have hvc : v.cache = s.cache := by dsimp [v]; split <;> rfl
  have hvi : v.predIdx = Function.update s.predIdx z i.val := by dsimp [v]; split <;> rfl
  have hvp : v.pred = Function.update s.pred z (h i) := by dsimp [v]; split <;> rfl
  unfold step at ht
  change t ∈ (if z ∈ u.cache ∨ u.cache.card < k then _ else _ : PMF (PMState α)).support at ht
  by_cases hf : z ∈ u.cache ∨ u.cache.card < k
  · rw [if_pos hf,PMF.mem_support_pure_iff] at ht
    subst t
    exact load hu _
  · rw [if_neg hf] at ht
    have hzc : z ∉ v.cache := by rw [hvc]; exact (not_or.mp hf).1
    have hfull : k ≤ v.cache.card := by rw [hvc]; exact Nat.le_of_not_gt (not_or.mp hf).2
    have hm : v.marked.card < k := by
      dsimp [v]; split
      · simpa using (show 0 < k by omega)
      · rename_i hne
        have hle := (Finset.card_le_card hud.1).trans hud.2
        omega
    have hne := RunBounds.unmarked_nonempty hvd hfull hm
    have hidx (e : α) (he : e ∈ v.cache) : predAt σ h (v.predIdx e) = v.pred e := by
      have hez : e ≠ z := by intro hez; subst e; exact hzc he
      have hec : e ∈ s.cache := by simpa [hvc] using he
      obtain ⟨j,_,_,hij,hpj,_⟩ := History.prefix_saved k tb σ h i.val (Nat.le_of_lt i.isLt) hs e hec
      rw [hvi,hvp,Function.update_of_ne hez,Function.update_of_ne hez,hij,predAt_fin,hpj]
    change t ∈ (if z ∉ v.stale then _ else _ : PMF (PMState α)).support at ht
    by_cases hclean : z ∉ v.stale
    · rw [if_pos hclean,PMF.mem_support_pure_iff] at ht
      subst t
      let w : PMState α := {v with clean := v.clean+1, chainLen := Function.update v.chainLen v.phase (Function.update (v.chainLen v.phase) (v.clean+1) 1)}
      have hw : Coherent σ h w (some z) := ⟨hv.ordered,hv.cap⟩
      have he := (htb w hne).1
      exact evict hw (v.clean+1) hzc he (hidx _ (Finset.mem_sdiff.mp he).1)
        (fun _ => (htb w hne).2)
    · rw [if_neg hclean] at ht
      let w := Bookkeeping.bump v (v.chainOf z)
      have hw : Coherent σ h w (some z) := ⟨hv.ordered,hv.cap⟩
      change t ∈ (if ((v.chainLen v.phase (v.chainOf z)+1 : ℕ) : ℝ) ≤ (harmonic k : ℝ)
        then _ else _ : PMF (PMState α)).support at ht
      by_cases hp : ((v.chainLen v.phase (v.chainOf z)+1 : ℕ) : ℝ) ≤ (harmonic k : ℝ)
      · rw [if_pos hp,PMF.mem_support_pure_iff] at ht
        subst t
        have he := (htb w hne).1
        exact evict hw (v.chainOf z) hzc he (hidx _ (Finset.mem_sdiff.mp he).1)
          (fun _ => (htb w hne).2)
      · rw [if_neg hp,dif_pos hne,PMF.mem_support_map_iff] at ht
        obtain ⟨e,he,rfl⟩ := ht
        rw [PMF.mem_support_uniformOfFinset_iff] at he
        exact evict (mark_random hw v.phase (v.chainOf z)) (v.chainOf z) hzc he
          (hidx e (Finset.mem_sdiff.mp he).1) (by intro hn; exact (hn (by simp [w,Bookkeeping.bump])).elim)

theorem prefix_coherent (k : ℕ) (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    (n : ℕ) (hn : n ≤ σ.length) {s : PMState α}
    (hs : s ∈ (History.prefixRun k tb σ h n).support) : Coherent σ h s := by
  induction n generalizing s with
  | zero =>
    have he : s = initState α := by
      simpa only [History.prefixRun,List.take_zero,List.foldl_nil,PMF.mem_support_pure_iff] using hs
    subst s
    constructor <;> simp [initState]
  | succ n ih =>
    have hlt : n < σ.length := by omega
    rw [History.prefixRun_succ k tb σ h n hlt,PMF.mem_support_bind_iff] at hs
    obtain ⟨u,hu,ht⟩ := hs
    exact step_coherent k hk tb htb σ h ⟨n,hlt⟩ hu (ih (by omega) hu) ht

theorem run_coherent (k : ℕ) (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {s : PMState α} (hs : s ∈ (run k tb σ h).support) : Coherent σ h s := by
  apply prefix_coherent k hk tb htb σ h σ.length le_rfl
  have htake : (List.finRange σ.length).take σ.length = List.finRange σ.length := List.take_of_length_le (by simp)
  simpa only [History.prefixRun,run,htake] using hs

theorem ordered_certificate (k : ℕ) (hk : 1 ≤ k) (tb : PMState α → α)
    (htb : IsMaxTieBreak tb) (σ : List α) (h : Fin σ.length → ℝ)
    {s : PMState α} (hs : s ∈ (run k tb σ h).support) (r c : ℕ)
    (hc : (r,c) ∉ s.randomChains) : ChainCertificate.Ordered σ h s r c := by
  obtain ⟨j,hj,ha⟩ := Representatives.run_arrival_certificate k hk tb htb σ h hs r c
  refine ⟨j,hj,ha,?_⟩
  have ho := (run_coherent k hk tb htb σ h hs).ordered r c hc
  rw [← hj,List.pairwise_ofFn] at ho
  intro a b hab
  rcases lt_or_eq_of_le hab with hab|hab
  · simpa only [predAt_fin] using ho hab
  · subst b
    exact le_rfl

end CachingML.PredMarker.Predictions

open CachingML.PredMarker

theorem solution {α : Type*} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k)
    (ℓ : ℝ → ℝ → ℝ) (hℓ : ∀ a b, 0 ≤ ℓ a b)
    (S : ℝ → ℝ) (hSconc : ConcaveOn ℝ (Set.Ici 0) S)
    (hScont : ContinuousWithinAt S (Set.Ici 0) 0)
    (hspread : ∀ m : ℝ, 0 ≤ m → ∃ t : ℕ, spread ℓ m = t ∧ (t : ℝ) ≤ S m)
    (tb : PMState α → α) (htb : IsMaxTieBreak tb)
    (σ : List α) (h : Fin σ.length → ℝ)
    (s : PMState α) (hs : s ∈ (run k tb σ h).support) (r c : ℕ) (hc : (r, c) ∉ s.randomChains) :
    (s.chainLen r c : ℝ) ≤ 1 + S (chainError ℓ σ h s r c) := by
  exact ChainCertificate.platform_bound_of_ordered ℓ hℓ S hSconc hScont hspread σ h s r c
    (Predictions.ordered_certificate k hk tb htb σ h hs r c hc)
