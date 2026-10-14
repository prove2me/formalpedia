-- Prove2me | solution 1 for DLSConsensus.BasicRound.decision_round_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:48:54.009997+00:00
-- url     : https://prove2.me/submissions/a72d756a-8efe-4340-86a9-7b6a35cc3811

import Mathlib
import Definitions.Def_DLSConsensus_BasicRound_Model



namespace DLSConsensus.BasicRound

open Classical

section Basic
variable {N : ℕ} {V : Type*}

lemma step_proper (t : ℕ) (pick : ℕ → Set V → V) (r : ℕ) (p : Fin N) (s : PState V)
    (box : Fin N → Option (Msg V)) :
    (step t pick r p s box).proper = s.proper ∪ {v | ∃ q m, box q = some m ∧ v ∈ m.proper} := by
  unfold step
  split_ifs <;> rfl

lemma step_lock13 (t : ℕ) (pick : ℕ → Set V → V) (r : ℕ) (p : Fin N) (s : PState V)
    (box : Fin N → Option (Msg V)) (h : r % 4 = 1 ∨ r % 4 = 3) :
    (step t pick r p s box).lock = s.lock := by
  unfold step
  rcases h with h | h
  · simp [h]
  · have h1 : ¬ r % 4 = 1 := by omega
    have h2 : ¬ r % 4 = 2 := by omega
    simp [h, h1, h2]

lemma step_lock2 (t : ℕ) (pick : ℕ → Set V → V) (r : ℕ) (p : Fin N) (s : PState V)
    (box : Fin N → Option (Msg V)) (h : r % 4 = 2) :
    (step t pick r p s box).lock =
      fun v => if ∃ q P, box q = some ⟨P, .lockReq v⟩ then some (phaseOf r) else s.lock v := by
  unfold step
  have h1 : ¬ r % 4 = 1 := by omega
  simp [h, h1]

lemma step_lock0 (t : ℕ) (pick : ℕ → Set V → V) (r : ℕ) (p : Fin N) (s : PState V)
    (box : Fin N → Option (Msg V)) (h : r % 4 = 0) :
    (step t pick r p s box).lock = fun v => match s.lock v with
               | none => none
               | some h =>
                 if ∃ q P S, box q = some ⟨P, .locks S⟩ ∧ ∃ w h', (w, h') ∈ S ∧ w ≠ v ∧ h ≤ h'
                 then none else some h := by
  unfold step
  have h1 : ¬ r % 4 = 1 := by omega
  have h2 : ¬ r % 4 = 2 := by omega
  have h3 : ¬ r % 4 = 3 := by omega
  simp [h1, h2, h3]
  funext v
  split <;> simp_all

lemma step_ackPending2 (t : ℕ) (pick : ℕ → Set V → V) (r : ℕ) (p : Fin N) (s : PState V)
    (box : Fin N → Option (Msg V)) (h : r % 4 = 2) :
    (step t pick r p s box).ackPending = ∃ q P v, box q = some ⟨P, .lockReq v⟩ := by
  unfold step
  have h1 : ¬ r % 4 = 1 := by omega
  simp [h, h1]

lemma step_ackPending_ne2 (t : ℕ) (pick : ℕ → Set V → V) (r : ℕ) (p : Fin N) (s : PState V)
    (box : Fin N → Option (Msg V)) (h : r % 4 ≠ 2) :
    (step t pick r p s box).ackPending = s.ackPending := by
  unfold step
  by_cases h1 : r % 4 = 1
  · simp [h1]
  · by_cases h3 : r % 4 = 3
    · simp [h3, h1, h]
    · simp [h1, h3, h]

lemma step_proposal_ne1 (t : ℕ) (pick : ℕ → Set V → V) (r : ℕ) (p : Fin N) (s : PState V)
    (box : Fin N → Option (Msg V)) (h : r % 4 ≠ 1) :
    (step t pick r p s box).proposal = s.proposal := by
  unfold step
  by_cases h2 : r % 4 = 2
  · simp [h2, h]
  · by_cases h3 : r % 4 = 3
    · simp [h3, h, h2]
    · simp [h, h2, h3]

lemma step_proposal1 (t : ℕ) (pick : ℕ → Set V → V) (r : ℕ) (p : Fin N) (s : PState V)
    (box : Fin N → Option (Msg V)) (h : r % 4 = 1) :
    (step t pick r p s box).proposal =
      if Owns p (phaseOf r) ∧ ({v : V | N - t ≤
        (Finset.univ.filter fun q => ∃ P L, box q = some ⟨P, .list L⟩ ∧ v ∈ L).card}).Nonempty
      then some (pick (phaseOf r) {v : V | N - t ≤
        (Finset.univ.filter fun q => ∃ P L, box q = some ⟨P, .list L⟩ ∧ v ∈ L).card})
      else none := by
  unfold step
  simp [h]


lemma send_mod1 (r : ℕ) (q p : Fin N) (s : PState V) (h : r % 4 = 1) :
    send r q p s = if Owns p (phaseOf r) then
      some ⟨s.proper, .list {v | v ∈ s.proper ∧ Acceptable s v}⟩ else none := by
  unfold send; simp [h]

lemma send_mod2 (r : ℕ) (q p : Fin N) (s : PState V) (h : r % 4 = 2) :
    send r q p s = if Owns q (phaseOf r) then
      s.proposal.map fun v => ⟨s.proper, .lockReq v⟩ else none := by
  have h1 : ¬ r % 4 = 1 := by omega
  unfold send; simp [h, h1]

lemma send_mod3 (r : ℕ) (q p : Fin N) (s : PState V) (h : r % 4 = 3) :
    send r q p s = if Owns p (phaseOf r) ∧ s.ackPending then
      some ⟨s.proper, .ack⟩ else none := by
  have h1 : ¬ r % 4 = 1 := by omega
  have h2 : ¬ r % 4 = 2 := by omega
  unfold send; simp [h, h1, h2]

lemma send_mod0 (r : ℕ) (q p : Fin N) (s : PState V) (h : r % 4 = 0) :
    send r q p s = some ⟨s.proper, .locks {x | s.lock x.1 = some x.2}⟩ := by
  have h1 : ¬ r % 4 = 1 := by omega
  have h2 : ¬ r % 4 = 2 := by omega
  have h3 : ¬ r % 4 = 3 := by omega
  unfold send; simp [h1, h2, h3]

lemma send_proper (r : ℕ) (q p : Fin N) (s : PState V) (m : Msg V)
    (h : send r q p s = some m) : m.proper = s.proper := by
  have : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
  rcases this with h0 | h0 | h0 | h0
  · rw [send_mod0 _ _ _ _ h0] at h; cases h; rfl
  · rw [send_mod1 _ _ _ _ h0] at h; split_ifs at h; cases h; rfl
  · rw [send_mod2 _ _ _ _ h0] at h; split_ifs at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨a, _, rfl⟩ := h; rfl
  · rw [send_mod3 _ _ _ _ h0] at h; split_ifs at h; cases h; rfl

lemma inbox_some {deliv : ℕ → Fin N → Fin N → Prop} {st : Fin N → PState V} {r : ℕ} {p q : Fin N}
    {m : Msg V} (h : inbox deliv st r p q = some m) :
    deliv r q p ∧ send r q p (st q) = some m := by
  unfold inbox at h
  split_ifs at h with hd
  exact ⟨hd, h⟩

lemma inbox_proper {deliv : ℕ → Fin N → Fin N → Prop} {st : Fin N → PState V} {r : ℕ}
    {p q : Fin N} {m : Msg V} (h : inbox deliv st r p q = some m) :
    m.proper = (st q).proper := send_proper _ _ _ _ _ (inbox_some h).2

lemma inbox_mk {deliv : ℕ → Fin N → Fin N → Prop} {st : Fin N → PState V} {r : ℕ}
    {p q : Fin N} {m : Msg V} (hd : deliv r q p) (h : send r q p (st q) = some m) :
    inbox deliv st r p q = some m := by
  unfold inbox; rw [if_pos hd]; exact h

lemma inbox_lockReq {deliv : ℕ → Fin N → Fin N → Prop} {st : Fin N → PState V} {r : ℕ}
    {p q : Fin N} {P : Set V} {w : V}
    (h : inbox deliv st r p q = some ⟨P, .lockReq w⟩) :
    r % 4 = 2 ∧ Owns q (phaseOf r) ∧ (st q).proposal = some w ∧ deliv r q p := by
  obtain ⟨hd, hs⟩ := inbox_some h
  have : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
  rcases this with h0 | h0 | h0 | h0
  · rw [send_mod0 _ _ _ _ h0] at hs; cases hs
  · rw [send_mod1 _ _ _ _ h0] at hs; split_ifs at hs; cases hs
  · rw [send_mod2 _ _ _ _ h0] at hs
    split_ifs at hs with ho
    simp only [Option.map_eq_some_iff] at hs
    obtain ⟨a, ha, he⟩ := hs
    cases he
    exact ⟨h0, ho, ha, hd⟩
  · rw [send_mod3 _ _ _ _ h0] at hs; split_ifs at hs; cases hs

lemma inbox_list {deliv : ℕ → Fin N → Fin N → Prop} {st : Fin N → PState V} {r : ℕ}
    {p q : Fin N} {P L : Set V}
    (h : inbox deliv st r p q = some ⟨P, .list L⟩) :
    r % 4 = 1 ∧ L = {v | v ∈ (st q).proper ∧ Acceptable (st q) v} ∧ deliv r q p := by
  obtain ⟨hd, hs⟩ := inbox_some h
  have : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
  rcases this with h0 | h0 | h0 | h0
  · rw [send_mod0 _ _ _ _ h0] at hs; cases hs
  · rw [send_mod1 _ _ _ _ h0] at hs; split_ifs at hs
    cases hs; exact ⟨h0, rfl, hd⟩
  · rw [send_mod2 _ _ _ _ h0] at hs
    split_ifs at hs
    · simp only [Option.map_eq_some_iff] at hs
      obtain ⟨a, ha, he⟩ := hs
      cases he
  · rw [send_mod3 _ _ _ _ h0] at hs; split_ifs at hs; cases hs

lemma inbox_locks {deliv : ℕ → Fin N → Fin N → Prop} {st : Fin N → PState V} {r : ℕ}
    {p q : Fin N} {P : Set V} {S : Set (V × ℕ)}
    (h : inbox deliv st r p q = some ⟨P, .locks S⟩) :
    r % 4 = 0 ∧ S = {x | (st q).lock x.1 = some x.2} := by
  obtain ⟨hd, hs⟩ := inbox_some h
  have : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
  rcases this with h0 | h0 | h0 | h0
  · rw [send_mod0 _ _ _ _ h0] at hs; cases hs; exact ⟨h0, rfl⟩
  · rw [send_mod1 _ _ _ _ h0] at hs; split_ifs at hs; cases hs
  · rw [send_mod2 _ _ _ _ h0] at hs
    split_ifs at hs
    · simp only [Option.map_eq_some_iff] at hs
      obtain ⟨a, ha, he⟩ := hs
      cases he
  · rw [send_mod3 _ _ _ _ h0] at hs; split_ifs at hs; cases hs

lemma inbox_ack {deliv : ℕ → Fin N → Fin N → Prop} {st : Fin N → PState V} {r : ℕ}
    {p q : Fin N} {P : Set V}
    (h : inbox deliv st r p q = some ⟨P, .ack⟩) :
    r % 4 = 3 ∧ (st q).ackPending := by
  obtain ⟨hd, hs⟩ := inbox_some h
  have : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
  rcases this with h0 | h0 | h0 | h0
  · rw [send_mod0 _ _ _ _ h0] at hs; cases hs
  · rw [send_mod1 _ _ _ _ h0] at hs; split_ifs at hs; cases hs
  · rw [send_mod2 _ _ _ _ h0] at hs
    split_ifs at hs
    · simp only [Option.map_eq_some_iff] at hs
      obtain ⟨a, ha, he⟩ := hs
      cases he
  · rw [send_mod3 _ _ _ _ h0] at hs
    split_ifs at hs with hh
    exact ⟨h0, hh.2⟩

lemma owns_unique {p q : Fin N} {k : ℕ} (hp : Owns p k) (hq : Owns q k) : p = q := by
  unfold Owns at hp hq
  have hp' : p.val + 1 ≡ q.val + 1 [MOD N] := by
    unfold Nat.ModEq; rw [← hp, ← hq]
  have := Nat.ModEq.add_right_cancel' 1 hp'
  apply Fin.ext
  exact Nat.ModEq.eq_of_lt_of_lt this p.isLt q.isLt


lemma step_lock0_old (t : ℕ) (pick : ℕ → Set V → V) (r : ℕ) (p : Fin N) (s : PState V)
    (box : Fin N → Option (Msg V)) (h0 : r % 4 = 0) (x : V) (h : ℕ)
    (hh : (step t pick r p s box).lock x = some h) : s.lock x = some h := by
  rw [step_lock0 _ _ _ _ _ _ h0] at hh
  dsimp only at hh
  cases hs : s.lock x with
  | none => rw [hs] at hh; simp at hh
  | some h' =>
    rw [hs] at hh
    dsimp only at hh
    split_ifs at hh
    cases hh; rfl

lemma step_lock0_keep (t : ℕ) (pick : ℕ → Set V → V) (r : ℕ) (p : Fin N) (s : PState V)
    (box : Fin N → Option (Msg V)) (h0 : r % 4 = 0) (x : V) (h : ℕ)
    (hs : s.lock x = some h)
    (hn : ¬ ∃ q P S, box q = some ⟨P, .locks S⟩ ∧ ∃ w h', (w, h') ∈ S ∧ w ≠ x ∧ h ≤ h') :
    (step t pick r p s box).lock x = some h := by
  rw [step_lock0 _ _ _ _ _ _ h0]
  dsimp only
  rw [hs]
  dsimp only
  rw [if_neg hn]

lemma step_lock2_pt (t : ℕ) (pick : ℕ → Set V → V) (r : ℕ) (p : Fin N) (s : PState V)
    (box : Fin N → Option (Msg V)) (h2 : r % 4 = 2) (x : V) :
    (step t pick r p s box).lock x =
      if ∃ q P, box q = some ⟨P, .lockReq x⟩ then some (phaseOf r) else s.lock x := by
  rw [step_lock2 _ _ _ _ _ _ h2]

lemma step_lock0_drop (t : ℕ) (pick : ℕ → Set V → V) (r : ℕ) (p : Fin N) (s : PState V)
    (box : Fin N → Option (Msg V)) (h0 : r % 4 = 0) (x : V) (h : ℕ)
    (hs : s.lock x = some h)
    (hn : ∃ q P S, box q = some ⟨P, .locks S⟩ ∧ ∃ w h', (w, h') ∈ S ∧ w ≠ x ∧ h ≤ h') :
    (step t pick r p s box).lock x = none := by
  rw [step_lock0 _ _ _ _ _ _ h0]
  dsimp only
  rw [hs]
  dsimp only
  rw [if_pos hn]

section Exec
variable {t : ℕ} {pick : ℕ → Set V → V} {init : Fin N → V}
  {deliv : ℕ → Fin N → Fin N → Prop}

lemma exec_succ (r : ℕ) (p : Fin N) :
    exec t pick init deliv (r + 1) p = step t pick (r + 1) p (exec t pick init deliv r p)
      (inbox deliv (exec t pick init deliv r) (r + 1) p) := rfl

lemma exec_zero (p : Fin N) : exec t pick init deliv 0 p = initState (init p) := rfl

lemma mod4_cases (r : ℕ) : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega

lemma lock_le : ∀ (r : ℕ) (p : Fin N) (x : V) (h : ℕ),
    (exec t pick init deliv r p).lock x = some h → 4 * h ≤ r + 2 := by
  intro r
  induction r with
  | zero => intro p x h hh; simp [exec_zero, initState] at hh
  | succ r ih =>
    intro p x h hh
    rw [exec_succ] at hh
    rcases mod4_cases (r + 1) with h0 | h0 | h0 | h0
    · have := step_lock0_old _ _ _ _ _ _ h0 _ _ hh
      have := ih _ _ _ this; omega
    · rw [step_lock13 _ _ _ _ _ _ (Or.inl h0)] at hh
      have := ih _ _ _ hh; omega
    · rw [step_lock2_pt _ _ _ _ _ _ h0] at hh
      split_ifs at hh with hc
      · cases hh
        unfold phaseOf; omega
      · have := ih _ _ _ hh; omega
    · rw [step_lock13 _ _ _ _ _ _ (Or.inr h0)] at hh
      have := ih _ _ _ hh; omega

lemma proper_mono_succ (r : ℕ) (p : Fin N) :
    (exec t pick init deliv r p).proper ⊆ (exec t pick init deliv (r + 1) p).proper := by
  rw [exec_succ, step_proper]; exact Set.subset_union_left

lemma proper_mono {r r' : ℕ} (h : r ≤ r') (p : Fin N) :
    (exec t pick init deliv r p).proper ⊆ (exec t pick init deliv r' p).proper := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (proper_mono_succ _ _)


lemma lemma_3_1_core (k : ℕ) (p q : Fin N) (v w : V)
    (hp : LocksAt t pick init deliv p k v) (hq : LocksAt t pick init deliv q k w) : v = w := by
  obtain ⟨hk, hp⟩ := hp
  obtain ⟨_, hq⟩ := hq
  simp only [Lockers, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
  obtain ⟨a, P, ha⟩ := hp
  obtain ⟨b, Q, hb⟩ := hq
  obtain ⟨_, oa, pa, _⟩ := inbox_lockReq ha
  obtain ⟨_, ob, pb, _⟩ := inbox_lockReq hb
  have e : phaseOf (4 * k - 2) = k := by unfold phaseOf; omega
  rw [e] at oa ob
  have := owns_unique oa ob
  subst this
  rw [pa] at pb
  exact Option.some.inj pb

lemma lemma_3_3_core (C : Finset (Fin N)) (GST : ℕ)
    (hdeliv : DelivOK C GST deliv) (k : ℕ) (hk : 1 ≤ k) (hGST : GST ≤ 4 * k) :
    {v : V | ∃ p ∈ C, (exec t pick init deliv (4 * k) p).lock v ≠ none}.Subsingleton := by
  rintro v ⟨p, hp, hv⟩ w ⟨q, hq, hw⟩
  by_contra hne
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hv
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hw
  obtain ⟨r, hr⟩ : ∃ r, 4 * k = r + 1 := ⟨4 * k - 1, by omega⟩
  rw [hr] at ha hb hGST
  have h0 : (r + 1) % 4 = 0 := by omega
  rw [exec_succ] at ha hb
  have ha' := step_lock0_old _ _ _ _ _ _ h0 _ _ ha
  have hb' := step_lock0_old _ _ _ _ _ _ h0 _ _ hb
  have mk : ∀ x ∈ C, ∀ y ∈ C, inbox deliv (exec t pick init deliv r) (r + 1) x y =
      some ⟨(exec t pick init deliv r y).proper, .locks {z | (exec t pick init deliv r y).lock z.1 = some z.2}⟩ :=
    fun x hx y hy => inbox_mk (hdeliv _ hGST y hy x hx) (send_mod0 _ _ _ _ h0)
  rcases le_total a b with hab | hab
  · rw [step_lock0_drop _ _ _ _ _ _ h0 _ _ ha'] at ha
    · cases ha
    · exact ⟨q, _, _, mk p hp q hq, w, b, hb', Ne.symm hne, hab⟩
  · rw [step_lock0_drop _ _ _ _ _ _ h0 _ _ hb'] at hb
    · cases hb
    · exact ⟨p, _, _, mk q hq p hp, v, a, ha', hne, hab⟩


lemma cands_mem (ht : t < N) (box : Fin N → Option (Msg V)) (w : V)
    (hw : N - t ≤ (Finset.univ.filter fun q => ∃ (P : Set V) (L : Set V),
      box q = some ⟨P, .list L⟩ ∧ w ∈ L).card) :
    ∃ q P L, box q = some ⟨P, .list L⟩ ∧ w ∈ L := by
  have hpos : 0 < (Finset.univ.filter fun q => ∃ (P : Set V) (L : Set V),
      box q = some ⟨P, .list L⟩ ∧ w ∈ L).card := by omega
  obtain ⟨q, hq⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
  obtain ⟨P, L, hb, hwL⟩ := hq
  exact ⟨q, P, L, hb, hwL⟩

lemma list_mem_proper (r : ℕ) (p q : Fin N) (w : V) (P L : Set V)
    (hb : inbox deliv (exec t pick init deliv r) (r + 1) p q = some ⟨P, .list L⟩)
    (hwL : w ∈ L) : w ∈ (exec t pick init deliv (r + 1) p).proper := by
  obtain ⟨_, hL, _⟩ := inbox_list hb
  have hP : (⟨P, .list L⟩ : Msg V).proper = (exec t pick init deliv r q).proper :=
    inbox_proper hb
  rw [hL] at hwL
  rw [exec_succ, step_proper]
  right
  exact ⟨q, ⟨P, .list L⟩, hb, hP ▸ hwL.1⟩

lemma inv_J (hpick : PickAdmissible pick) (ht : t < N) : ∀ (r : ℕ) (p : Fin N),
    (∀ w, (exec t pick init deliv r p).proposal = some w → w ∈ (exec t pick init deliv r p).proper) ∧
    (∀ x h, (exec t pick init deliv r p).lock x = some h → x ∈ (exec t pick init deliv r p).proper) := by
  intro r
  induction r with
  | zero =>
    intro p
    refine ⟨?_, ?_⟩
    · intro w hw; simp [exec_zero, initState] at hw
    · intro x h hh; simp [exec_zero, initState] at hh
  | succ r ih =>
    intro p
    have hmono := proper_mono_succ (t := t) (pick := pick) (init := init) (deliv := deliv) r p
    refine ⟨?_, ?_⟩
    · intro w hw
      by_cases h1 : (r + 1) % 4 = 1
      · have hprop := step_proposal1 t pick (r + 1) p (exec t pick init deliv r p)
          (inbox deliv (exec t pick init deliv r) (r + 1) p) h1
        rw [exec_succ, hprop] at hw
        split_ifs at hw with hc
        · have hmem := hpick (phaseOf (r + 1)) _ hc.2
          cases hw
          simp only [Set.mem_setOf_eq] at hmem
          obtain ⟨q, P, L, hb, hwL⟩ := cands_mem ht _ _ hmem
          exact list_mem_proper r p q _ P L hb hwL
      · rw [exec_succ, step_proposal_ne1 _ _ _ _ _ _ h1] at hw
        exact hmono ((ih p).1 w hw)
    · intro x h hh
      rcases mod4_cases (r + 1) with h0 | h0 | h0 | h0
      · rw [exec_succ] at hh
        exact hmono ((ih p).2 x h (step_lock0_old _ _ _ _ _ _ h0 _ _ hh))
      · rw [exec_succ, step_lock13 _ _ _ _ _ _ (Or.inl h0)] at hh
        exact hmono ((ih p).2 x h hh)
      · rw [exec_succ, step_lock2_pt _ _ _ _ _ _ h0] at hh
        split_ifs at hh with hc
        · obtain ⟨q, P, hb⟩ := hc
          obtain ⟨_, _, hpr, _⟩ := inbox_lockReq hb
          have hP := inbox_proper hb
          have h2 : (⟨P, .lockReq x⟩ : Msg V).proper = (exec t pick init deliv r q).proper := hP
          have h3 : x ∈ (exec t pick init deliv r q).proper := (ih q).1 x hpr
          rw [exec_succ, step_proper]
          right
          exact ⟨q, ⟨P, .lockReq x⟩, hb, h2 ▸ h3⟩
        · exact hmono ((ih p).2 x h hh)
      · rw [exec_succ, step_lock13 _ _ _ _ _ _ (Or.inr h0)] at hh
        exact hmono ((ih p).2 x h hh)

lemma strong_unan (v : V) (hv : ∀ q, init q = v) :
    ∀ (r : ℕ) (p : Fin N), (exec t pick init deliv r p).proper ⊆ {v} := by
  intro r
  induction r with
  | zero => intro p; simp [exec_zero, initState, hv]
  | succ r ih =>
    intro p
    rw [exec_succ, step_proper]
    rintro x (hx | ⟨q, m, hm, hxm⟩)
    · exact ih p hx
    · rw [inbox_proper hm] at hxm
      exact ih q hxm


lemma prop_after (hpick : PickAdmissible pick) (ht : t < N) (v : V) (Q : Finset (Fin N))
    (hQ : t + 1 ≤ Q.card) (r : ℕ) (hr : (r + 1) % 4 = 1)
    (hA : ∀ q ∈ Q, ∃ h, (exec t pick init deliv r q).lock v = some h) (p : Fin N) (w : V)
    (hw : (exec t pick init deliv (r + 1) p).proposal = some w) : w = v := by
  by_contra hne
  have hprop := step_proposal1 t pick (r + 1) p (exec t pick init deliv r p)
    (inbox deliv (exec t pick init deliv r) (r + 1) p) hr
  rw [exec_succ, hprop] at hw
  split_ifs at hw with hc
  cases hw
  have hmem := hpick (phaseOf (r + 1)) _ hc.2
  simp only [Set.mem_setOf_eq] at hmem
  set F := (Finset.univ.filter fun q => ∃ (P : Set V) (L : Set V),
      inbox deliv (exec t pick init deliv r) (r + 1) p q = some ⟨P, .list L⟩ ∧
      pick (phaseOf (r + 1)) {v : V | N - t ≤ (Finset.univ.filter fun q => ∃ (P : Set V) (L : Set V),
      inbox deliv (exec t pick init deliv r) (r + 1) p q = some ⟨P, .list L⟩ ∧ v ∈ L).card} ∈ L) with hF
  have hsub : F ⊆ Qᶜ := by
    intro q hq
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    obtain ⟨P, L, hb, hwL⟩ := hq
    rw [Finset.mem_compl]
    intro hqQ
    obtain ⟨h, hh⟩ := hA q hqQ
    obtain ⟨_, hL, _⟩ := inbox_list hb
    rw [hL] at hwL
    have := hwL.2 v (by rw [hh]; simp)
    exact hne this.symm
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_compl, Fintype.card_fin] at h1
  have h2 : Q.card ≤ N := by
    simpa using Finset.card_le_univ Q
  omega

/-- The invariant for Lemma 3.2. -/
def KInv (t : ℕ) (pick : ℕ → Set V → V) (init : Fin N → V)
    (deliv : ℕ → Fin N → Fin N → Prop) (k : ℕ) (v : V) (Q : Finset (Fin N)) (r : ℕ) : Prop :=
  (∀ q ∈ Q, ∃ h, k ≤ h ∧ (exec t pick init deliv r q).lock v = some h) ∧
  (∀ (p : Fin N) (x : V) (h : ℕ), (exec t pick init deliv r p).lock x = some h → k ≤ h → x = v) ∧
  (r % 4 = 1 → ∀ (q : Fin N) (w : V), (exec t pick init deliv r q).proposal = some w → w = v)

lemma kinv_step (hpick : PickAdmissible pick) (ht : t < N) (k : ℕ) (v : V) (Q : Finset (Fin N))
    (hQ : t + 1 ≤ Q.card) (r : ℕ) (hr : 4 * k - 2 ≤ r) (hk : 1 ≤ k)
    (h : KInv t pick init deliv k v Q r) : KInv t pick init deliv k v Q (r + 1) := by
  obtain ⟨hA, hB, hC⟩ := h
  rcases mod4_cases (r + 1) with h0 | h0 | h0 | h0
  · refine ⟨?_, ?_, ?_⟩
    · intro q hq
      obtain ⟨h, hkh, hh⟩ := hA q hq
      refine ⟨h, hkh, ?_⟩
      rw [exec_succ]
      apply step_lock0_keep _ _ _ _ _ _ h0 _ _ hh
      rintro ⟨q', P, S, hb, w, h', hS, hwv, hle⟩
      obtain ⟨_, hSe⟩ := inbox_locks hb
      rw [hSe] at hS
      exact hwv (hB q' w h' hS (hkh.trans hle))
    · intro p x h hh hkh
      rw [exec_succ] at hh
      exact hB p x h (step_lock0_old _ _ _ _ _ _ h0 _ _ hh) hkh
    · intro h1; omega
  · refine ⟨?_, ?_, ?_⟩
    · intro q hq
      obtain ⟨h, hkh, hh⟩ := hA q hq
      refine ⟨h, hkh, ?_⟩
      rw [exec_succ, step_lock13 _ _ _ _ _ _ (Or.inl h0)]
      exact hh
    · intro p x h hh hkh
      rw [exec_succ, step_lock13 _ _ _ _ _ _ (Or.inl h0)] at hh
      exact hB p x h hh hkh
    · intro _ q w hw
      exact prop_after hpick ht v Q hQ r h0
        (fun q hq => by obtain ⟨h, _, hh⟩ := hA q hq; exact ⟨h, hh⟩) q w hw
  · have hphase : k + 1 ≤ phaseOf (r + 1) := by unfold phaseOf; omega
    refine ⟨?_, ?_, ?_⟩
    · intro q hq
      obtain ⟨h, hkh, hh⟩ := hA q hq
      rw [exec_succ, step_lock2_pt _ _ _ _ _ _ h0]
      split_ifs with hc
      · exact ⟨_, by omega, rfl⟩
      · exact ⟨h, hkh, hh⟩
    · intro p x h hh hkh
      rw [exec_succ, step_lock2_pt _ _ _ _ _ _ h0] at hh
      split_ifs at hh with hc
      · obtain ⟨q, P, hb⟩ := hc
        obtain ⟨_, _, hpr, _⟩ := inbox_lockReq hb
        exact hC (by omega) q x hpr
      · exact hB p x h hh hkh
    · intro h1; omega
  · refine ⟨?_, ?_, ?_⟩
    · intro q hq
      obtain ⟨h, hkh, hh⟩ := hA q hq
      refine ⟨h, hkh, ?_⟩
      rw [exec_succ, step_lock13 _ _ _ _ _ _ (Or.inr h0)]
      exact hh
    · intro p x h hh hkh
      rw [exec_succ, step_lock13 _ _ _ _ _ _ (Or.inr h0)] at hh
      exact hB p x h hh hkh
    · intro h1; omega

lemma ackers_sub (p : Fin N) (k : ℕ) (v : V) (hdec : DecidesAt t pick init deliv p k v) :
    Ackers t pick init deliv p k ⊆ Lockers t pick init deliv k v := by
  obtain ⟨hk, hown, hprop, _⟩ := hdec
  intro q hq
  simp only [Ackers, Finset.mem_filter, Finset.mem_univ, true_and] at hq
  obtain ⟨P, hb⟩ := hq
  obtain ⟨_, hpend⟩ := inbox_ack hb
  obtain ⟨r, hr⟩ : ∃ r, 4 * k - 2 = r + 1 := ⟨4 * k - 3, by omega⟩
  have hr3 : r = 4 * k - 3 := by omega
  rw [hr, exec_succ, step_ackPending2 _ _ _ _ _ _ (by omega)] at hpend
  obtain ⟨q', P', v', hb'⟩ := hpend
  obtain ⟨_, ho, hpr, _⟩ := inbox_lockReq hb'
  have e : phaseOf (r + 1) = k := by unfold phaseOf; omega
  rw [e] at ho
  have := owns_unique ho hown
  subst this
  subst hr3
  rw [hprop] at hpr
  have hv := Option.some.inj hpr
  subst hv
  simp only [Lockers, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨q', P', ?_⟩
  rw [hr]
  exact hb'

theorem key_inv (hpick : PickAdmissible pick) (p : Fin N) (k : ℕ) (v : V)
    (hdec : DecidesAt t pick init deliv p k v) :
    t + 1 ≤ (Lockers t pick init deliv k v).card ∧ t < N ∧
      ∀ r, 4 * k - 2 ≤ r → KInv t pick init deliv k v (Lockers t pick init deliv k v) r := by
  have hQ : t + 1 ≤ (Lockers t pick init deliv k v).card :=
    hdec.2.2.2.trans (Finset.card_le_card (ackers_sub p k v hdec))
  have hN : t < N := by
    have := Finset.card_le_univ (Lockers t pick init deliv k v)
    simp at this; omega
  refine ⟨hQ, hN, ?_⟩
  obtain ⟨hk, hown, hprop, _⟩ := hdec
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    obtain ⟨m, hr⟩ : ∃ m, 4 * k - 2 = m + 1 := ⟨4 * k - 3, by omega⟩
    have hr3 : m = 4 * k - 3 := by omega
    subst hr3
    have e : phaseOf (4 * k - 3 + 1) = k := by unfold phaseOf; omega
    have h2 : (4 * k - 3 + 1) % 4 = 2 := by omega
    refine ⟨?_, ?_, ?_⟩
    · intro q hq
      simp only [Lockers, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      obtain ⟨a, P, ha⟩ := hq
      refine ⟨k, le_rfl, ?_⟩
      rw [hr, exec_succ, step_lock2_pt _ _ _ _ _ _ h2, if_pos ⟨a, P, by rw [← hr]; exact ha⟩, e]
    · intro p' x h hh hkh
      rw [hr, exec_succ, step_lock2_pt _ _ _ _ _ _ h2] at hh
      split_ifs at hh with hc
      · obtain ⟨q, P, hb⟩ := hc
        obtain ⟨_, ho, hpr, _⟩ := inbox_lockReq hb
        rw [e] at ho
        have := owns_unique ho hown
        subst this
        rw [hprop] at hpr
        exact (Option.some.inj hpr).symm
      · have := lock_le _ _ _ _ hh
        omega
    · intro h1; omega
  | succ r hr ih =>
    exact kinv_step hpick hN _ _ _ hQ r hr hk ih


theorem lemma_3_2_core (hpick : PickAdmissible pick) (p : Fin N) (k : ℕ) (v : V)
    (hdec : DecidesAt t pick init deliv p k v) :
    t + 1 ≤ (Lockers t pick init deliv k v).card ∧
      ∀ q : Fin N, LocksAt t pick init deliv q k v →
        ∀ r : ℕ, 4 * k - 2 ≤ r →
          ∃ h : ℕ, k ≤ h ∧ (exec t pick init deliv r q).lock v = some h := by
  obtain ⟨hQ, hN, hI⟩ := key_inv hpick p k v hdec
  exact ⟨hQ, fun q hq r hr => (hI r hr).1 q hq.2⟩

lemma decide_le (hpick : PickAdmissible pick) {p q : Fin N} {k k' : ℕ} {v w : V}
    (hp : DecidesAt t pick init deliv p k v) (hq : DecidesAt t pick init deliv q k' w)
    (hle : k ≤ k') : w = v := by
  rcases hle.eq_or_lt with rfl | hlt
  · have := owns_unique hq.2.1 hp.2.1
    subst this
    exact Option.some.inj (hq.2.2.1.symm.trans hp.2.2.1)
  · obtain ⟨_, _, hI⟩ := key_inv hpick p k v hp
    have hk' := hq.1
    exact (hI (4 * k' - 3) (by omega)).2.2 (by omega) q w hq.2.2.1

theorem consistency_core (hpick : PickAdmissible pick) (C : Finset (Fin N)) :
    Consistency t pick init deliv C := by
  intro p _ q _ k k' v w hp hq
  rcases le_total k k' with h | h
  · exact (decide_le hpick hp hq h).symm
  · exact decide_le hpick hq hp h

theorem unanimity_core (hpick : PickAdmissible pick) (ht : t < N) (C : Finset (Fin N)) :
    StrongUnanimity t pick init deliv C := by
  intro v hv p _ k w hdec
  have h1 := (inv_J hpick ht (4 * k - 3) p).1 w hdec.2.2.1
  have h2 := strong_unan (t := t) (pick := pick) (init := init) (deliv := deliv) v hv (4 * k - 3) p h1
  exact h2


lemma proper_exchange (C : Finset (Fin N)) (GST : ℕ) (hdeliv : DelivOK C GST deliv) (j : ℕ)
    (hj : 1 ≤ j) (hGST : GST ≤ 4 * j) (p q : Fin N) (hp : p ∈ C) (hq : q ∈ C) :
    (exec t pick init deliv (4 * j - 1) q).proper ⊆ (exec t pick init deliv (4 * j) p).proper := by
  obtain ⟨r, hr⟩ : ∃ r, 4 * j = r + 1 := ⟨4 * j - 1, by omega⟩
  have hr' : 4 * j - 1 = r := by omega
  rw [hr', hr, exec_succ, step_proper]
  intro x hx
  right
  refine ⟨q, ⟨(exec t pick init deliv r q).proper,
    .locks {z | (exec t pick init deliv r q).lock z.1 = some z.2}⟩, ?_, hx⟩
  exact inbox_mk (hdeliv _ (by omega) q hq p hp) (send_mod0 _ _ _ _ (by omega))

lemma lock_before_release (j : ℕ) (hj : 1 ≤ j) (q : Fin N) (x : V)
    (hx : (exec t pick init deliv (4 * j) q).lock x ≠ none) :
    (exec t pick init deliv (4 * j - 1) q).lock x ≠ none := by
  obtain ⟨r, hr⟩ : ∃ r, 4 * j = r + 1 := ⟨4 * j - 1, by omega⟩
  have hr' : 4 * j - 1 = r := by omega
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hx
  rw [hr, exec_succ] at ha
  rw [hr']
  rw [step_lock0_old _ _ _ _ _ _ (by omega) _ _ ha]
  simp

theorem decide_phase (hpick : PickAdmissible pick) {t : ℕ} (hN : 2 * t + 1 ≤ N)
    (C : Finset (Fin N)) (hC : N - t ≤ C.card) (GST : ℕ) (hdeliv : DelivOK C GST deliv)
    (j : ℕ) (hj : 1 ≤ j) (hGST : GST ≤ 4 * j) (p : Fin N) (hp : p ∈ C) (hown : Owns p (j + 1)) :
    ∃ v, DecidesAt t pick init deliv p (j + 1) v := by
  have ht : t < N := by omega
  -- a common value
  obtain ⟨w, hw1, hw2⟩ : ∃ w : V, (∀ q ∈ C, w ∈ (exec t pick init deliv (4 * j) q).proper) ∧
      (∀ q ∈ C, ∀ y, (exec t pick init deliv (4 * j) q).lock y ≠ none → y = w) := by
    by_cases hlock : ∃ q ∈ C, ∃ x, (exec t pick init deliv (4 * j) q).lock x ≠ none
    · obtain ⟨q0, hq0, x0, hx0⟩ := hlock
      refine ⟨x0, ?_, ?_⟩
      · intro q hq
        have h1 := lock_before_release (t := t) (pick := pick) (init := init) (deliv := deliv)
          j hj q0 x0 hx0
        obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp h1
        have h2 := (inv_J hpick ht (4 * j - 1) q0).2 x0 a ha
        exact proper_exchange C GST hdeliv j hj hGST q q0 hq hq0 h2
      · intro q hq y hy
        exact lemma_3_3_core C GST hdeliv j hj hGST ⟨q, hq, hy⟩ ⟨q0, hq0, hx0⟩
    · push_neg at hlock
      have hne : C.Nonempty := by
        rw [← Finset.card_pos]; omega
      obtain ⟨c0, hc0⟩ := hne
      refine ⟨init c0, ?_, ?_⟩
      · intro q hq
        have h0 : init c0 ∈ (exec t pick init deliv 0 c0).proper := by
          simp [exec_zero, initState]
        have h1 := proper_mono (t := t) (pick := pick) (init := init) (deliv := deliv)
          (show 0 ≤ 4 * j - 1 by omega) c0 h0
        exact proper_exchange C GST hdeliv j hj hGST q c0 hq hc0 h1
      · intro q hq y hy
        exact absurd (hlock q hq y) hy
  -- the list round
  have e1 : phaseOf (4 * j + 1) = j + 1 := by unfold phaseOf; omega
  have e2 : phaseOf (4 * j + 1 + 1) = j + 1 := by unfold phaseOf; omega
  have e3 : phaseOf (4 * j + 1 + 1 + 1) = j + 1 := by unfold phaseOf; omega
  have hlist : ∀ q ∈ C, inbox deliv (exec t pick init deliv (4 * j)) (4 * j + 1) p q =
      some ⟨(exec t pick init deliv (4 * j) q).proper,
        .list {v | v ∈ (exec t pick init deliv (4 * j) q).proper ∧
          Acceptable (exec t pick init deliv (4 * j) q) v}⟩ := by
    intro q hq
    apply inbox_mk (hdeliv _ (by omega) q hq p hp)
    rw [send_mod1 _ _ _ _ (by omega), if_pos (by rw [e1]; exact hown)]
  have hcand : N - t ≤ (Finset.univ.filter fun q => ∃ (P : Set V) (L : Set V),
      inbox deliv (exec t pick init deliv (4 * j)) (4 * j + 1) p q = some ⟨P, .list L⟩ ∧ w ∈ L).card := by
    refine hC.trans (Finset.card_le_card ?_)
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨_, _, hlist q hq, hw1 q hq, ?_⟩
    intro y hy
    exact hw2 q hq y hy
  have hprop := step_proposal1 t pick (4 * j + 1) p (exec t pick init deliv (4 * j) p)
    (inbox deliv (exec t pick init deliv (4 * j)) (4 * j + 1) p) (by omega)
  have hprop2 : (exec t pick init deliv (4 * j + 1) p).proposal = some (pick (j + 1)
      {v : V | N - t ≤ (Finset.univ.filter fun q => ∃ (P : Set V) (L : Set V),
      inbox deliv (exec t pick init deliv (4 * j)) (4 * j + 1) p q = some ⟨P, .list L⟩ ∧ v ∈ L).card}) := by
    rw [exec_succ, hprop, e1, if_pos]
    exact ⟨hown, ⟨w, hcand⟩⟩
  set u := pick (j + 1) {v : V | N - t ≤ (Finset.univ.filter fun q => ∃ (P : Set V) (L : Set V),
      inbox deliv (exec t pick init deliv (4 * j)) (4 * j + 1) p q = some ⟨P, .list L⟩ ∧ v ∈ L).card} with hu
  -- lock request round
  have hreq : ∀ q ∈ C, inbox deliv (exec t pick init deliv (4 * j + 1)) (4 * j + 1 + 1) q p =
      some ⟨(exec t pick init deliv (4 * j + 1) p).proper, .lockReq u⟩ := by
    intro q hq
    apply inbox_mk (hdeliv _ (by omega) p hp q hq)
    rw [send_mod2 _ _ _ _ (by omega), if_pos (by rw [e2]; exact hown), hprop2]
    rfl
  have hpend : ∀ q ∈ C, (exec t pick init deliv (4 * j + 1 + 1) q).ackPending := by
    intro q hq
    rw [exec_succ, step_ackPending2 _ _ _ _ _ _ (by omega)]
    exact ⟨p, _, u, hreq q hq⟩
  have hack : ∀ q ∈ C, inbox deliv (exec t pick init deliv (4 * j + 1 + 1)) (4 * j + 1 + 1 + 1) p q =
      some ⟨(exec t pick init deliv (4 * j + 1 + 1) q).proper, .ack⟩ := by
    intro q hq
    apply inbox_mk (hdeliv _ (by omega) q hq p hp)
    rw [send_mod3 _ _ _ _ (by omega), if_pos ⟨by rw [e3]; exact hown, hpend q hq⟩]
  refine ⟨u, by omega, hown, ?_, ?_⟩
  · have : 4 * (j + 1) - 3 = 4 * j + 1 := by omega
    rw [this]; exact hprop2
  · have h1 : 4 * (j + 1) - 2 = 4 * j + 1 + 1 := by omega
    have h2 : 4 * (j + 1) - 1 = 4 * j + 1 + 1 + 1 := by omega
    have hsub : C ⊆ Ackers t pick init deliv p (j + 1) := by
      intro q hq
      simp only [Ackers, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [h1, h2]
      exact ⟨_, hack q hq⟩
    have := Finset.card_le_card hsub
    omega

theorem decision_round_bound_core (hpick : PickAdmissible pick) {t : ℕ} (hN : 2 * t + 1 ≤ N)
    (C : Finset (Fin N)) (hC : N - t ≤ C.card) (GST : ℕ) (hdeliv : DelivOK C GST deliv) :
    ∀ p ∈ C, ∃ (k : ℕ) (v : V),
      DecidesAt t pick init deliv p k v ∧ 4 * k - 1 ≤ GST + 4 * (N + 1) := by
  intro p hp
  have hNpos : 0 < N := by omega
  set k0 := GST / 4 + 2 with hk0
  set d := p.val + 1 + N - k0 % N with hd
  have hmod : k0 % N < N := Nat.mod_lt _ hNpos
  have hdlt : (d % N) < N := Nat.mod_lt _ hNpos
  have hpN := p.isLt
  have hkey : (k0 + d % N) % N = (p.val + 1) % N := by
    rw [Nat.add_mod_mod]
    have h1 := Nat.div_add_mod k0 N
    have h2 : k0 + d = (p.val + 1) + N * (k0 / N + 1) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    rw [h2, Nat.add_mul_mod_self_left]
  have hkge : k0 ≤ k0 + d % N := Nat.le_add_right _ _
  obtain ⟨j, hj⟩ : ∃ j, k0 + d % N = j + 1 := ⟨k0 + d % N - 1, by omega⟩
  have hown : Owns p (j + 1) := by
    unfold Owns; rw [← hj]; exact hkey
  have hj1 : 1 ≤ j := by omega
  have hGST : GST ≤ 4 * j := by omega
  obtain ⟨v, hv⟩ := decide_phase hpick hN C hC GST hdeliv j hj1 hGST p hp hown
  exact ⟨j + 1, v, hv, by omega⟩


theorem theorem_3_1_core (hpick : PickAdmissible pick) {t : ℕ} (hN : 2 * t + 1 ≤ N)
    (C : Finset (Fin N)) (hC : N - t ≤ C.card) (GST : ℕ) (hdeliv : DelivOK C GST deliv) :
    Consistency t pick init deliv C ∧ StrongUnanimity t pick init deliv C ∧
      Termination t pick init deliv C := by
  refine ⟨consistency_core hpick C, unanimity_core hpick (by omega) C, ?_⟩
  intro p hp
  obtain ⟨k, v, h, _⟩ := decision_round_bound_core hpick hN C hC GST hdeliv p hp
  exact ⟨k, v, h⟩

end Exec

end Basic
end DLSConsensus.BasicRound

open DLSConsensus.BasicRound


theorem solution {N t : ℕ} (hN : 2 * t + 1 ≤ N) {V : Type*} (init : Fin N → V)
    (C : Finset (Fin N)) (hC : N - t ≤ C.card) (GST : ℕ) (deliv : ℕ → Fin N → Fin N → Prop)
    (hdeliv : DelivOK C GST deliv) (pick : ℕ → Set V → V) (hpick : PickAdmissible pick) :
    ∀ p ∈ C, ∃ (k : ℕ) (v : V),
      DecidesAt t pick init deliv p k v ∧ 4 * k - 1 ≤ GST + 4 * (N + 1) := by
  exact decision_round_bound_core hpick hN C hC GST hdeliv
