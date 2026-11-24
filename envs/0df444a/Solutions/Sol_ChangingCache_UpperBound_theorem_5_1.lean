-- Prove2me | solution 1 for ChangingCache.UpperBound.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T19:38:25.998664+00:00
-- url     : https://prove2.me/submissions/b67d4673-215b-439a-894b-ed703fb8ca97

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_Bank
import Theorems.Thm_ChangingCache_UpperBound_lemma_5_2
import Theorems.Thm_ChangingCache_UpperBound_lemma_5_3
import Theorems.Thm_ChangingCache_UpperBound_lemma_5_4
import Theorems.Thm_ChangingCache_UpperBound_lemma_5_5
import Theorems.Thm_ChangingCache_UpperBound_lemma_5_6
import Theorems.Thm_ChangingCache_UpperBound_lemma_5_7

open ChangingCache.UpperBound

namespace Thm51Aux

variable {α : Type*} [DecidableEq α]

theorem lruRun_succ (C : ℕ → ℕ) (σ : List α) (k : ℕ) (hk : k < σ.length) :
    lruRun C (σ.take (k + 1)) = lruStep C (lruRun C (σ.take k)) σ[k] := by
  unfold lruRun
  rw [List.take_add_one, List.getElem?_eq_getElem hk, List.foldl_append]
  rfl

theorem lru_misses (C : ℕ → ℕ) (σ : List α) (h1 : LRUAlwaysMisses C σ) :
    ∀ k ≤ σ.length, (lruRun C (σ.take k)).misses = k := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [lruRun]
  | succ k ih =>
    intro hk
    have hk' : k < σ.length := by omega
    have hm := ih (by omega)
    rw [lruRun_succ C σ k hk']
    unfold lruStep
    rw [if_neg (h1 k hk')]
    simp [hm]

theorem policyMisses_succ (σ : List α) (S : ℕ → Finset α) (k : ℕ) :
    policyMisses σ S (k + 1) = policyMisses σ S k + if missB σ S k then 1 else 0 := by
  cases h : missB σ S k <;> simp [policyMisses, List.range_succ, List.filter_append, h]

theorem policyMisses_mono (σ : List α) (S : ℕ → Finset α) {a b : ℕ} (hab : a ≤ b) :
    policyMisses σ S a ≤ policyMisses σ S b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih =>
    rw [policyMisses_succ]
    omega

theorem missB_iff (σ : List α) (T : ℕ → Finset α) {i : ℕ} (hi : i < σ.length) :
    missB σ T i = true ↔ σ[i] ∉ T i := by
  unfold missB
  rw [List.getElem?_eq_getElem hi]
  simp

omit [DecidableEq α] in
theorem getElem_mem_take (σ : List α) {i' i : ℕ} (h : i' < i) (hi : i ≤ σ.length) :
    σ[i'] ∈ σ.take i := by
  have hlt : i' < (σ.take i).length := by rw [List.length_take]; omega
  have : (σ.take i)[i'] = σ[i'] := List.getElem_take
  rw [← this]
  exact List.getElem_mem _

omit [DecidableEq α] in
theorem mem_take_mono (σ : List α) {x : α} {a b : ℕ} (hx : x ∈ σ.take a) (hab : a ≤ b) :
    x ∈ σ.take b := by
  have : σ.take a = (σ.take b).take a := by
    rw [List.take_take, Nat.min_eq_left hab]
  rw [this] at hx
  exact List.mem_of_mem_take hx

theorem seen (m : ℕ → ℕ) (σ : List α) (T : ℕ → Finset α) (hT : IsLegal m σ T) :
    ∀ i ≤ σ.length, ∀ x ∈ T i, x ∈ σ.take i := by
  intro i
  induction i with
  | zero =>
    intro _ x hx
    rw [hT.1] at hx
    simp at hx
  | succ i ih =>
    intro hi x hx
    have hi' : i < σ.length := by omega
    have h1 := (hT.2 i hi').1 hx
    rw [Finset.mem_insert] at h1
    rw [List.take_add_one, List.getElem?_eq_getElem hi']
    simp only [List.mem_append, Option.toList_some, List.mem_singleton]
    rcases h1 with h | h
    · exact Or.inr h
    · exact Or.inl (ih (by omega) x h)

theorem mem_loadedIn (σ : List α) (S : ℕ → Finset α) (r' u : ℕ) (x : α) :
    x ∈ loadedIn σ S r' u ↔
      ∃ i, r' ≤ i ∧ i < u ∧ missB σ S i = true ∧ σ[i]? = some x := by
  unfold loadedIn
  rw [List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨i, hi, h⟩
    rw [List.mem_range] at hi
    split_ifs at h with hc
    exact ⟨i, hc.1, hi, hc.2, h⟩
  · rintro ⟨i, h1, h2, h3, h4⟩
    exact ⟨i, List.mem_range.2 h2, by rw [if_pos ⟨h1, h3⟩]; exact h4⟩

theorem loadedIn_self (σ : List α) (S : ℕ → Finset α) (r' : ℕ) : loadedIn σ S r' r' = ∅ := by
  ext x
  rw [mem_loadedIn]
  simp only [Finset.notMem_empty, iff_false]
  rintro ⟨i, h1, h2, _⟩
  omega

theorem loadedIn_card (σ : List α) (S : ℕ → Finset α) (hcold : AllMissesCold σ S) (r' : ℕ) :
    ∀ u, r' ≤ u → u ≤ σ.length →
      (loadedIn σ S r' u).card + policyMisses σ S r' = policyMisses σ S u := by
  intro u hu
  induction u, hu using Nat.le_induction with
  | base =>
    intro _
    rw [loadedIn_self]
    simp
  | succ u hu ih =>
    intro hlen
    have hu' : u < σ.length := by omega
    have ih := ih (by omega)
    rw [policyMisses_succ]
    by_cases hmiss : missB σ S u = true
    · have heq : loadedIn σ S r' (u + 1) = insert σ[u] (loadedIn σ S r' u) := by
        ext x
        rw [Finset.mem_insert, mem_loadedIn, mem_loadedIn]
        constructor
        · rintro ⟨i, h1, h2, h3, h4⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h | h
          · exact Or.inr ⟨i, h1, h, h3, h4⟩
          · subst h
            rw [List.getElem?_eq_getElem hu', Option.some.injEq] at h4
            exact Or.inl h4.symm
        · rintro (h | ⟨i, h1, h2, h3, h4⟩)
          · exact ⟨u, hu, by omega, hmiss, by rw [h, List.getElem?_eq_getElem hu']⟩
          · exact ⟨i, h1, by omega, h3, h4⟩
      have hnot : σ[u] ∉ loadedIn σ S r' u := by
        rw [mem_loadedIn]
        rintro ⟨i, _, h2, _, h4⟩
        obtain ⟨_, hc⟩ := hcold u hu' hmiss
        have hi : i < σ.length := by omega
        rw [List.getElem?_eq_getElem hi, Option.some.injEq] at h4
        apply hc
        rw [← h4]
        exact getElem_mem_take σ h2 (le_of_lt hu')
      rw [heq, Finset.card_insert_of_notMem hnot, if_pos hmiss]
      omega
    · have heq : loadedIn σ S r' (u + 1) = loadedIn σ S r' u := by
        ext x
        rw [mem_loadedIn, mem_loadedIn]
        constructor
        · rintro ⟨i, h1, h2, h3, h4⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h | h
          · exact ⟨i, h1, h, h3, h4⟩
          · subst h; exact absurd h3 hmiss
        · rintro ⟨i, h1, h2, h3, h4⟩
          exact ⟨i, h1, by omega, h3, h4⟩
      rw [heq, if_neg hmiss]
      omega

theorem disj_loaded (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α) (hS : IsLegal m σ S)
    (hcold : AllMissesCold σ S) (b u : ℕ) (hb : b ≤ σ.length) :
    Disjoint (S b) (loadedIn σ S b u) := by
  rw [Finset.disjoint_left]
  intro x hx hl
  rw [mem_loadedIn] at hl
  obtain ⟨t, h1, h2, h3, h4⟩ := hl
  have ht : t < σ.length := by
    by_contra hcon
    rw [List.getElem?_eq_none (by omega)] at h4
    simp at h4
  rw [List.getElem?_eq_getElem ht, Option.some.injEq] at h4
  obtain ⟨_, hc⟩ := hcold t ht h3
  apply hc
  rw [h4]
  exact mem_take_mono σ (seen m σ S hS b hb x hx) h1

theorem bank_eq (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α)
    (h1 : LRUAlwaysMisses (augCap 2 3 m) σ) (r : ℕ) (hr : r ≤ σ.length) :
    bank3 m σ S r = 3 * (policyMisses σ S r : ℤ) - (r : ℤ) := by
  unfold bank3 lruMissCount
  rw [lru_misses _ σ h1 r hr]

/-- The contradiction at the globally earliest failure `y = 3x + 1` of Equation (4), in a run where
OPT discards nothing after its `x`-th miss (request `b + 1`). -/
theorem core (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α) (hred : IsReduced 2 3 m σ S)
    (y x b : ℕ) (hyx : y = 3 * x + 1) (hx : 1 ≤ x) (hy : y ≤ σ.length)
    (hfail : ¬ Eq4At m σ S y) (hb : b < y) (hFb : policyMisses σ S b + 1 = x)
    (hFb1 : policyMisses σ S (b + 1) = x)
    (hkeep : ∀ u, b ≤ u → u ≤ y → S u = S b ∪ loadedIn σ S b u)
    (hslackAll : ∀ (m2 : ℕ → ℕ) (σ2 : List α) (S2 : ℕ → Finset α), IsReduced 2 3 m2 σ2 S2 →
      ∀ w' < y, w' ≤ σ2.length → -1 ≤ slack3 m2 σ2 S2 w') : False := by
  have hred0 := hred
  obtain ⟨hm, hopt, hR1, hR2, hR3⟩ := hred0
  have hS := hopt.1
  -- LRU's window at y
  have hfull := (ChangingCache.UpperBound.lemma_5_3 m σ S hred x hx (by omega)).1
  rw [← hyx] at hfull
  have hwin := (ChangingCache.UpperBound.lemma_5_2 m σ S hred).1 y hy
  rw [hfull] at hwin
  obtain ⟨hcle, hnd, hLeq⟩ := hwin
  set a := y - 2 * m x with hadef
  have hmx : 1 ≤ m x := hm.1 x
  -- the failure
  have hbank := bank_eq m σ S hR1
  have hfail' : 3 * (policyMisses σ S y : ℤ) - (y : ℤ) < ((S y).card : ℤ) + (mu m σ S y : ℤ) := by
    unfold Eq4At at hfail
    rw [hbank y hy] at hfail
    push_cast at hfail
    exact lt_of_not_ge hfail
  -- OPT's x-th miss at b
  have hmissb : missB σ S b = true := by
    have := policyMisses_succ σ S b
    by_contra hcon
    rw [if_neg hcon] at this
    omega
  have hSb : (S b).card + 1 = m x := by
    have := hR3 b (by omega) hmissb
    rw [show policyMisses σ S b + 1 = x by omega] at this
    exact this
  have hFy : x ≤ policyMisses σ S y := by
    have := policyMisses_mono σ S (show b + 1 ≤ y by omega)
    omega
  -- cardinalities in the kept run
  have hkcard : ∀ u, b ≤ u → u ≤ y → (S u).card + policyMisses σ S b = (S b).card + policyMisses σ S u := by
    intro u h1 h2
    rw [hkeep u h1 h2, Finset.card_union_of_disjoint
      (disj_loaded m σ S hS hR2 b u (by omega))]
    have := loadedIn_card σ S hR2 b u h1 (by omega)
    omega
  have hSy := hkcard y (by omega) le_rfl
  -- Step 1: a < b
  have hab : a < b := by
    by_contra hcon
    have h56 := ChangingCache.UpperBound.lemma_5_6 m σ S hred y hy b
      (by rw [hfull]; omega)
    rw [hfull] at h56
    push_cast at hfail'
    omega
  -- Step 2: (6), (7), (8)
  -- (7): the requests in (b, y] are distinct pages held by both LRU and OPT
  have hya : y - 2 * m x = a := rfl
  have hdrop : (σ.take y).drop b = ((σ.take y).drop a).drop (b - a) := by
    rw [List.drop_drop, show a + (b - a) = b by omega]
  have hndb : ((σ.take y).drop b).Nodup := by
    rw [hdrop]; exact hnd.sublist (List.drop_sublist _ _)
  set W := ((σ.take y).drop b).toFinset with hW
  have hWcard : W.card = y - b := by
    rw [hW, List.toFinset_card_of_nodup hndb, List.length_drop, List.length_take]
    omega
  have hWL : W ⊆ lruCache (augCap 2 3 m) σ y := by
    intro z hz
    rw [hLeq, List.mem_toFinset]
    rw [hW, List.mem_toFinset, hdrop] at hz
    exact List.mem_of_mem_drop hz
  have hWS : W ⊆ S y := by
    intro z hz
    rw [hW, List.mem_toFinset, List.mem_drop_iff_getElem] at hz
    obtain ⟨j, hj, hjz⟩ := hz
    rw [List.length_take] at hj
    rw [List.getElem_take] at hjz
    have ht : b + j < σ.length := by omega
    rw [hkeep y (by omega) le_rfl]
    by_cases hmt : missB σ S (b + j) = true
    · apply Finset.mem_union_right
      rw [mem_loadedIn]
      exact ⟨b + j, by omega, by omega, hmt, by rw [List.getElem?_eq_getElem ht, hjz]⟩
    · have hin : σ[b + j] ∈ S (b + j) := by
        by_contra hcon
        exact hmt ((missB_iff σ S ht).2 hcon)
      rw [hjz] at hin
      rw [hkeep (b + j) (by omega) (by omega)] at hin
      rw [Finset.mem_union] at hin ⊢
      rcases hin with h | h
      · exact Or.inl h
      · right
        rw [mem_loadedIn] at h ⊢
        obtain ⟨i, a1, a2, a3, a4⟩ := h
        exact ⟨i, a1, by omega, a3, a4⟩
  have h7 : y - b + mu m σ S y ≤ (S y).card := by
    have hsub : W ⊆ S y ∩ lruCache (augCap 2 3 m) σ y := Finset.subset_inter hWS hWL
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_sdiff_add_card_inter (S y) (lruCache (augCap 2 3 m) σ y)
    have : mu m σ S y = (S y \ lruCache (augCap 2 3 m) σ y).card := rfl
    omega
  -- (8): slack at b
  have h8 := hslackAll m σ S hred b hb (by omega)
  unfold slack3 at h8
  rw [hbank b (by omega)] at h8
  -- Step 3
  have hFa : policyMisses σ S a ≤ policyMisses σ S b := policyMisses_mono σ S (le_of_lt hab)
  have h56a := ChangingCache.UpperBound.lemma_5_6 m σ S hred y hy a
    (by rw [hfull]; omega)
  rw [hfull] at h56a
  have hsa := hslackAll m σ S hred a (by omega) (by omega)
  unfold slack3 at hsa
  rw [hbank a (by omega)] at hsa
  have hFa1 : policyMisses σ S a ≤ policyMisses σ S (a + 1) := policyMisses_mono σ S (by omega)
  have hcond : b ≤ 3 * policyMisses σ S (a + 1) + 2 := by
    push_cast at hfail' h8 hsa
    omega
  obtain ⟨m'', S'', hred'', _, _, _, _, hlast⟩ :=
    ChangingCache.UpperBound.lemma_5_7 m σ S hred a b hab (by omega) hcond
  obtain ⟨hbank'', _, hcard''⟩ := hlast b (le_of_lt hab) le_rfl
  have hs'' := hslackAll m'' (σ.take b) S'' hred'' b hb
    (by rw [List.length_take]; omega)
  unfold slack3 at hs''
  rw [hbank'', hbank b (by omega)] at hs''
  push_cast at hfail' h8 hsa hs''
  omega

/-- Equation (4) holds at every position `≡ 1 (mod 3)` of every reduced run. -/
theorem eq4_all : ∀ y : ℕ, ∀ (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α),
    IsReduced 2 3 m σ S → 1 ≤ y → y ≤ σ.length → y % 3 = 1 → Eq4At m σ S y := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y IH =>
  intro m σ S hred h1 hyn hy3
  have hslackAll : ∀ (m2 : ℕ → ℕ) (σ2 : List α) (S2 : ℕ → Finset α),
      IsReduced 2 3 m2 σ2 S2 → ∀ w' < y, w' ≤ σ2.length → -1 ≤ slack3 m2 σ2 S2 w' := by
    intro m2 σ2 S2 hred2 w' hw' hw'n
    apply ChangingCache.UpperBound.lemma_5_5 m2 σ2 S2 hred2 w'
    classical
    unfold eq4FirstFailure
    split_ifs with h
    · have hs := Nat.find_spec h
      by_contra hcon
      have := IH (Nat.find h) (by omega) m2 σ2 S2 hred2 hs.1 hs.2.1 hs.2.2.1
      exact hs.2.2.2 this
    · omega
  have hred0 := hred
  obtain ⟨hm, hopt, hR1, hR2, hR3⟩ := hred0
  have hS := hopt.1
  have hbank := bank_eq m σ S hR1
  by_contra hfail
  rcases Nat.lt_or_ge y 4 with hy4 | hy4
  · -- y = 1
    have hy : y = 1 := by omega
    subst hy
    apply hfail
    unfold Eq4At
    rw [hbank 1 hyn]
    have h0 : 0 < σ.length := by omega
    have hmiss0 : missB σ S 0 = true := by
      rw [missB_iff σ S h0, hS.1]
      exact Finset.notMem_empty _
    have hF1 : policyMisses σ S 1 = 1 := by
      rw [policyMisses_succ, if_pos hmiss0]; simp [policyMisses]
    have hS1 : (S 1).card ≤ 1 := by
      have := (hS.2 0 h0).1
      rw [hS.1] at this
      have := Finset.card_le_card this
      simpa using this
    have hmu : mu m σ S 1 ≤ (S 1).card := by
      unfold mu
      exact Finset.card_le_card Finset.sdiff_subset
    rw [hF1]
    push_cast
    omega
  · set x := y / 3 with hxdef
    have hyx : y = 3 * x + 1 := by omega
    have hx1 : 1 ≤ x := by omega
    -- the bank is nonnegative at y - 1
    have hBy : 0 ≤ bank3 m σ S (y - 1) := by
      by_contra hneg
      have hex : ∃ r ≤ σ.length, bank3 m σ S r < 0 := ⟨y - 1, by omega, lt_of_not_ge hneg⟩
      obtain ⟨h3, _, hnot⟩ := ChangingCache.UpperBound.lemma_5_4 m σ S hred hex
      have hle : sInf {r | r ≤ σ.length ∧ bank3 m σ S r < 0} ≤ y - 1 :=
        Nat.sInf_le ⟨by omega, lt_of_not_ge hneg⟩
      exact hnot (IH _ (by omega) m σ S hred (by omega) (by omega) h3)
    rw [hbank (y - 1) (by omega)] at hBy
    have hFy1 : x ≤ policyMisses σ S (y - 1) := by
      have : ((y - 1 : ℕ) : ℤ) = 3 * (x : ℤ) := by omega
      omega
    -- OPT's x-th miss
    have hexb : ∃ b, x ≤ policyMisses σ S (b + 1) := ⟨y - 1, by
      have := policyMisses_mono σ S (show y - 1 ≤ y - 1 + 1 by omega); omega⟩
    classical
    set b := Nat.find hexb with hbdef
    have hb1 : x ≤ policyMisses σ S (b + 1) := Nat.find_spec hexb
    have hble : b ≤ y - 2 := by
      have : y - 1 = (y - 2) + 1 := by omega
      exact Nat.find_le (h := hexb) (by rw [← this]; exact hFy1)
    have hbmin : policyMisses σ S b < x := by
      rcases Nat.eq_zero_or_pos b with h0 | hpos
      · rw [h0]; simp [policyMisses]; omega
      · have := Nat.find_min hexb (show b - 1 < b by omega)
        rw [show b - 1 + 1 = b by omega] at this
        omega
    have hsucc := policyMisses_succ σ S b
    have hFb : policyMisses σ S b + 1 = x := by split_ifs at hsucc <;> omega
    have hFb1 : policyMisses σ S (b + 1) = x := by split_ifs at hsucc <;> omega
    -- keep pages after b
    obtain ⟨m', S', hred', _, hcache, hmissEq, hS'eq, hlast⟩ :=
      ChangingCache.UpperBound.lemma_5_7 m σ S hred b y (by omega) hyn (by omega)
    have hlen : (σ.take y).length = y := by rw [List.length_take]; omega
    have hPM : ∀ i ≤ y, policyMisses (σ.take y) S' i = policyMisses σ S i := by
      intro i hi
      unfold policyMisses
      congr 1
      apply List.filter_congr
      intro z hz
      rw [List.mem_range] at hz
      exact hmissEq z (by omega)
    have hloaded : ∀ u ≤ y, loadedIn (σ.take y) S' b u = loadedIn σ S b u := by
      intro u hu
      ext z
      rw [mem_loadedIn, mem_loadedIn]
      constructor
      · rintro ⟨i, a1, a2, a3, a4⟩
        refine ⟨i, a1, a2, by rw [← hmissEq i (by omega)]; exact a3, ?_⟩
        rw [List.getElem?_take, if_pos (by omega)] at a4
        exact a4
      · rintro ⟨i, a1, a2, a3, a4⟩
        refine ⟨i, a1, a2, by rw [hmissEq i (by omega)]; exact a3, ?_⟩
        rw [List.getElem?_take, if_pos (by omega)]
        exact a4
    have hS'b : S' b = S b := by
      rw [hS'eq b le_rfl (by omega), loadedIn_self, Finset.union_empty]
    have hfail' : ¬ Eq4At m' (σ.take y) S' y := by
      intro h4
      apply hfail
      obtain ⟨hb', hsub, _⟩ := hlast y (by omega) le_rfl
      have hL : lruCache (augCap 2 3 m') (σ.take y) y = lruCache (augCap 2 3 m) σ y := by
        unfold lruCache
        rw [List.take_take, Nat.min_self, hcache y le_rfl]
      have hmu : mu m σ S y ≤ mu m' (σ.take y) S' y := by
        unfold mu
        rw [hL]
        exact Finset.card_le_card (Finset.sdiff_subset_sdiff hsub le_rfl)
      have hc := Finset.card_le_card hsub
      unfold Eq4At at h4 ⊢
      rw [← hb']
      push_cast at h4 ⊢
      omega
    apply core m' (σ.take y) S' hred' y x b hyx hx1 (by rw [hlen]) hfail'
      (by omega) (by rw [hPM b (by omega)]; exact hFb) (by rw [hPM (b + 1) (by omega)]; exact hFb1)
    · intro u h1 h2
      rw [hS'b, hloaded u h2]
      exact hS'eq u h1 (by omega)
    · exact hslackAll

end Thm51Aux

open Thm51Aux in
theorem solution {α : Type*} [DecidableEq α] (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α)
    (hred : IsReduced 2 3 m σ S) :
    lruMissCount (augCap 2 3 m) σ σ.length = σ.length ∧
      σ.length ≤ 3 * policyMisses σ S σ.length := by
  have hred0 := hred
  obtain ⟨_, _, hR1, _, _⟩ := hred0
  refine ⟨lru_misses _ σ hR1 σ.length le_rfl, ?_⟩
  by_contra hcon
  have hneg : bank3 m σ S σ.length < 0 := by
    rw [bank_eq m σ S hR1 σ.length le_rfl]
    push_cast
    omega
  have hex : ∃ r ≤ σ.length, bank3 m σ S r < 0 := ⟨σ.length, le_rfl, hneg⟩
  obtain ⟨h3, _, hnot⟩ := ChangingCache.UpperBound.lemma_5_4 m σ S hred hex
  have hmem := Nat.sInf_mem (s := {r | r ≤ σ.length ∧ bank3 m σ S r < 0})
    ⟨σ.length, le_rfl, hneg⟩
  exact hnot (eq4_all _ m σ S hred (by omega) hmem.1 h3)
