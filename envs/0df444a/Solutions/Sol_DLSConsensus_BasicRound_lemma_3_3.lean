-- Prove2me | solution 1 for DLSConsensus.BasicRound.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:41:46.755074+00:00
-- url     : https://prove2.me/submissions/9b65c814-277d-462d-88bb-60bd53805bc6

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

end Exec

end Basic
end DLSConsensus.BasicRound

open DLSConsensus.BasicRound


theorem solution {N : ℕ} {V : Type*} (t : ℕ) (pick : ℕ → Set V → V) (init : Fin N → V)
    (C : Finset (Fin N)) (GST : ℕ) (deliv : ℕ → Fin N → Fin N → Prop)
    (hdeliv : DelivOK C GST deliv) (k : ℕ) (hk : 1 ≤ k) (hGST : GST ≤ 4 * k) :
    {v : V | ∃ p ∈ C, (exec t pick init deliv (4 * k) p).lock v ≠ none}.Subsingleton := by
  exact lemma_3_3_core C GST hdeliv k hk hGST
