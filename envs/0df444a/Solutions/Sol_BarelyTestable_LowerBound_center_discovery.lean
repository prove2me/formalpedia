-- Prove2me | solution 1 for BarelyTestable.LowerBound.center_discovery
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:31:17.025718+00:00
-- url     : https://prove2.me/submissions/3040287d-24d5-44b8-a4b1-d001dd15d92c

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Discovery

set_option autoImplicit false

open BarelyTestable.LowerBound NonmonotoneSubmod.Shared MeasureTheory

namespace BTHelper_center_discovery

section Run
variable {ι : Type} (A : Procedure ι) (f : Oracle ι)

theorem run_zero_fst (h : History ι) : (run A f 0 h).1 = h := by
  cases hA : A h <;> simp [run, hA]

theorem run_prefix : ∀ (k : ℕ) (h : History ι), ∃ l, (run A f k h).1 = h ++ l := by
  intro k
  induction k with
  | zero => intro h; exact ⟨[], by simp [run_zero_fst]⟩
  | succ k ih =>
    intro h
    cases hA : A h with
    | inl b => exact ⟨[], by simp [run, hA]⟩
    | inr x =>
      obtain ⟨l, hl⟩ := ih (h ++ [(x, f x)])
      exact ⟨(x, f x) :: l, by simp [run, hA, hl]⟩

theorem run_length : ∀ (k : ℕ) (h : History ι), (run A f k h).1.length ≤ h.length + k := by
  intro k
  induction k with
  | zero => intro h; simp [run_zero_fst]
  | succ k ih =>
    intro h
    cases hA : A h with
    | inl b => simp [run, hA]
    | inr x =>
      have := ih (h ++ [(x, f x)])
      simp only [run, hA]
      simp at this
      omega

/-- Entries of the run transcript beyond the starting history: the `s`-th query is what `A`
asks on the length-`s` prefix, and the recorded answer is `f` at that point. -/
theorem run_entry : ∀ (k : ℕ) (h : History ι) (s : ℕ) (hs : s < (run A f k h).1.length),
    h.length ≤ s →
    A ((run A f k h).1.take s) = Sum.inr ((run A f k h).1[s]).1 ∧
      ((run A f k h).1[s]).2 = f ((run A f k h).1[s]).1 := by
  intro k
  induction k with
  | zero =>
    intro h s hs hle
    have : (run A f 0 h).1.length = h.length := by rw [run_zero_fst]
    omega
  | succ k ih =>
    intro h s hs hle
    cases hA : A h with
    | inl b =>
      have : (run A f (k+1) h).1 = h := by simp [run, hA]
      have : (run A f (k+1) h).1.length = h.length := by rw [this]
      omega
    | inr x =>
      have he : (run A f (k+1) h).1 = (run A f k (h ++ [(x, f x)])).1 := by simp [run, hA]
      have hs' : s < (run A f k (h ++ [(x, f x)])).1.length := he ▸ hs
      rcases Nat.lt_or_ge h.length s with hlt | hge
      · have := ih (h ++ [(x, f x)]) s hs' (by simp; omega)
        simp only [he]
        exact this
      · have hseq : s = h.length := le_antisymm hge hle
        obtain ⟨l, hl⟩ := run_prefix A f k (h ++ [(x, f x)])
        simp only [he]
        have hidx : (run A f k (h ++ [(x, f x)])).1[s] = (x, f x) := by
          simp only [hl, hseq]
          simp
        have htake : (run A f k (h ++ [(x, f x)])).1.take s = h := by
          simp only [hl, hseq]
          simp
        rw [hidx, htake]
        exact ⟨hA, rfl⟩

/-- Locality of runs: if `f` and `f'` agree at every point queried before position `t` in the
`f`-run, then the two runs have the same length-`t` prefix and the same `t`-th query point. -/
theorem run_agree (f' : Oracle ι) (t : ℕ) : ∀ (k : ℕ) (h : History ι),
    (∀ p ∈ (run A f k h).1.take t, f p.1 = f' p.1) →
    (run A f k h).1.take t = (run A f' k h).1.take t ∧
      ((run A f k h).1[t]?).map Prod.fst = ((run A f' k h).1[t]?).map Prod.fst := by
  intro k
  induction k with
  | zero => intro h _; simp [run_zero_fst]
  | succ k ih =>
    intro h hyp
    cases hA : A h with
    | inl b => simp [run, hA]
    | inr x =>
      simp only [run, hA] at hyp ⊢
      by_cases ht : h.length < t
      · have hx : f x = f' x := by
          apply hyp (x, f x)
          obtain ⟨l, hl⟩ := run_prefix A f k (h ++ [(x, f x)])
          rw [hl, List.take_append, List.take_of_length_le (by simp; omega)]
          simp
        rw [← hx]
        exact ih _ hyp
      · push Not at ht
        obtain ⟨l, hl⟩ := run_prefix A f k (h ++ [(x, f x)])
        obtain ⟨l', hl'⟩ := run_prefix A f' k (h ++ [(x, f' x)])
        rw [hl, hl']
        refine ⟨?_, ?_⟩
        · rw [List.append_assoc, List.append_assoc, List.take_append_of_le_length ht,
            List.take_append_of_le_length ht]
        · rcases lt_or_eq_of_le ht with hlt | heq
          · rw [List.append_assoc, List.append_assoc, List.getElem?_append_left hlt,
              List.getElem?_append_left hlt]
          · subst heq
            simp

end Run

section Count

open Classical in
/-- Involution counting: if every `φ` in the domain of the relation `R` has a unique key `k`,
and resampling `φ` at its key keeps the key and the "prefix" `pre φ`, then the event
`Bad (pre φ) (φ k)` has count at most `c / |V|` of all `φ`. -/
theorem count_involution {K V α : Type} [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]
    (R : (K → V) → K → Prop) (pre : (K → V) → α) (Bad : α → V → Prop) (c : ℕ)
    (huniq : ∀ φ k k', R φ k → R φ k' → k = k')
    (hstab : ∀ φ k v, R φ k →
      R (Function.update φ k v) k ∧ pre (Function.update φ k v) = pre φ)
    (hBad : ∀ φ, (Finset.univ.filter (fun v => Bad (pre φ) v)).card ≤ c) :
    (Finset.univ.filter (fun φ => ∃ k, R φ k ∧ Bad (pre φ) (φ k))).card * Fintype.card V
      ≤ c * Fintype.card (K → V) := by
  set E := Finset.univ.filter (fun φ => ∃ k, R φ k ∧ Bad (pre φ) (φ k))
  set T : Finset ((K → V) × V) :=
    Finset.univ.filter (fun z => ∃ k, R z.1 k ∧ Bad (pre z.1) z.2) with hT
  let σ : (K → V) × V → (K → V) × V := fun z =>
    if h : ∃ k, R z.1 k then (Function.update z.1 h.choose z.2, z.1 h.choose) else z
  have hσk : ∀ z k, R z.1 k → σ z = (Function.update z.1 k z.2, z.1 k) := by
    intro z k hk
    have hex : ∃ k, R z.1 k := ⟨k, hk⟩
    have hc : hex.choose = k := huniq _ _ _ hex.choose_spec hk
    simp only [σ, dif_pos hex, hc]
  have hσσ : ∀ z, σ (σ z) = z := by
    intro z
    by_cases hex : ∃ k, R z.1 k
    · obtain ⟨k, hk⟩ := hex
      rw [hσk z k hk, hσk _ k (hstab _ _ _ hk).1]
      simp
    · have : σ z = z := by simp only [σ, dif_neg hex]
      rw [this, this]
  have h1 : (E ×ˢ (Finset.univ : Finset V)).card ≤ T.card := by
    apply Finset.card_le_card_of_injOn σ
    · intro z hz
      simp only [Finset.mem_coe, Finset.mem_product, E, Finset.mem_filter] at hz
      obtain ⟨⟨_, k, hk, hb⟩, _⟩ := hz
      rw [hσk z k hk]
      simp only [Finset.mem_coe, hT, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨k, (hstab _ _ _ hk).1, by rw [(hstab _ _ _ hk).2]; exact hb⟩
    · intro z _ w _ hzw
      rw [← hσσ z, ← hσσ w, hzw]
  have h2 : T.card ≤ c * Fintype.card (K → V) := by
    rw [hT, Finset.card_filter, Fintype.sum_prod_type]
    calc ∑ φ : K → V, ∑ v : V, (if ∃ k, R (φ, v).1 k ∧ Bad (pre (φ, v).1) (φ, v).2 then 1 else 0)
        ≤ ∑ _φ : K → V, c := by
          apply Finset.sum_le_sum
          intro φ _
          rw [← Finset.card_filter]
          refine le_trans (Finset.card_le_card ?_) (hBad φ)
          intro v
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rintro ⟨k, _, hb⟩
          exact hb
      _ = c * Fintype.card (K → V) := by simp [mul_comm]
  have hS : (E ×ˢ (Finset.univ : Finset V)).card = E.card * Fintype.card V := by
    simp [Finset.card_product]
  omega

end Count

section Fresh

/-- History-level fresh-key event at position `t`: the `t`-th query point `x` has key `k`,
no earlier query has key `k`, and `Bad (H.take t) (val k)`. -/
def HistEvent {ι K V : Type} (H : History ι) (t : ℕ) (key : Cube ι → Option K)
    (Bad : History ι → V → Prop) (val : K → V) : Prop :=
  ∃ x k, (H[t]?).map Prod.fst = some x ∧ key x = some k ∧
    (∀ p ∈ H.take t, key p.1 ≠ some k) ∧ Bad (H.take t) (val k)

open Classical in
/-- Fresh-key resampling lemma: for an oracle family `F φ` reading the table `φ : K → V` at
point `x` only through the key `key x`, the fuel-`q` run has a fresh key at query `t` whose
table value is `Bad` for the earlier transcript with count at most `c / |V|` of all tables. -/
theorem fresh_key_count {ι K V : Type} [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]
    (A : Procedure ι) (q t : ℕ) (F : (K → V) → Oracle ι) (key : Cube ι → Option K)
    (hloc : ∀ φ φ' x, (∀ k, key x = some k → φ k = φ' k) → F φ x = F φ' x)
    (Bad : History ι → V → Prop) (c : ℕ)
    (hBad : ∀ h : History ι, h.length ≤ t → (Finset.univ.filter (fun v => Bad h v)).card ≤ c) :
    (Finset.univ.filter (fun φ => HistEvent (run A (F φ) q []).1 t key Bad φ)).card
      * Fintype.card V ≤ c * Fintype.card (K → V) := by
  let R : (K → V) → K → Prop := fun φ k => ∃ x,
    (((run A (F φ) q []).1)[t]?).map Prod.fst = some x ∧ key x = some k ∧
      ∀ p ∈ ((run A (F φ) q []).1).take t, key p.1 ≠ some k
  let pre : (K → V) → History ι := fun φ => ((run A (F φ) q []).1).take t
  have hev : ∀ φ, HistEvent (run A (F φ) q []).1 t key Bad φ ↔ ∃ k, R φ k ∧ Bad (pre φ) (φ k) := by
    intro φ
    constructor
    · rintro ⟨x, k, h1, h2, h3, h4⟩; exact ⟨k, ⟨x, h1, h2, h3⟩, h4⟩
    · rintro ⟨k, ⟨x, h1, h2, h3⟩, h4⟩; exact ⟨x, k, h1, h2, h3, h4⟩
  simp only [hev]
  have hci := count_involution R pre Bad c (by
      rintro φ k k' ⟨x, hx, hk, -⟩ ⟨x', hx', hk', -⟩
      rw [hx] at hx'
      cases hx'
      rw [hk] at hk'
      exact Option.some_injective _ hk')
    (by
      rintro φ k v ⟨x, hx, hk, hfresh⟩
      have hag := run_agree A (F φ) (F (Function.update φ k v)) t q [] (by
        intro p hp
        apply hloc
        intro k' hk'
        have hne : k' ≠ k := by
          rintro rfl
          exact hfresh p hp hk'
        simp [Function.update_of_ne hne])
      refine ⟨⟨x, ?_, hk, ?_⟩, ?_⟩
      · rw [← hag.2]; exact hx
      · rw [← hag.1]; exact hfresh
      · exact hag.1.symm)
    (fun φ => hBad _ (List.length_take_le _ _))
  convert hci using 3
  ext φ
  simp only [Finset.mem_filter]

end Fresh

section Apply

variable {m : ℕ}

/-- Key read from `φB` by a slice-01 point: its `Y`-half. -/
def keyB (x : Cube (Coord m)) : Option (HalfSet m) :=
  if actionA ∉ x ∧ actionB ∈ x then some (yPart x) else none

/-- Key read from `φA` by a slice-11 point: its `X`-half. -/
def keyA (x : Cube (Coord m)) : Option (HalfSet m) :=
  if actionA ∈ x ∧ actionB ∈ x then some (xPart x) else none

def BadB (h : History (Coord m)) (v : Bits m) : Prop :=
  ∃ p ∈ h, ∃ X, keyA p.1 = some X ∧ parity X = v

def BadA (h : History (Coord m)) (v : Bits m) : Prop :=
  ∃ p ∈ h, ∃ Y, keyB p.1 = some Y ∧ parity Y = v

open Classical in
theorem bad_card {ι K V : Type} [Fintype V] [DecidableEq V] (key : Cube ι → Option K)
    (g : K → V) (h : History ι) :
    (Finset.univ.filter (fun v => ∃ p ∈ h, ∃ k, key p.1 = some k ∧ g k = v)).card
      ≤ h.length := by
  calc _ ≤ (h.filterMap (fun p => (key p.1).map g)).toFinset.card := by
        apply Finset.card_le_card
        intro v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset,
          List.mem_filterMap, Option.map_eq_some_iff]
        rintro ⟨p, hp, k, hk, rfl⟩
        exact ⟨p, hp, k, hk, rfl⟩
    _ ≤ (h.filterMap (fun p => (key p.1).map g)).length := List.toFinset_card_le _
    _ ≤ h.length := List.length_filterMap_le _ _

theorem hard_locB (a : LabelMap m) (T : Table m) (sign : Bool) (φ φ' : LabelMap m)
    (x : Cube (Coord m)) (h : ∀ k, keyB x = some k → φ k = φ' k) :
    hard (a, φ, T) sign x = hard (a, φ', T) sign x := by
  unfold keyB at h
  unfold hard slice
  by_cases hA : actionA ∈ x <;> by_cases hB : actionB ∈ x <;> simp [hA, hB] at h ⊢
  simp [beta, h]

theorem hard_locA (b : LabelMap m) (T : Table m) (sign : Bool) (φ φ' : LabelMap m)
    (x : Cube (Coord m)) (h : ∀ k, keyA x = some k → φ k = φ' k) :
    hard (φ, b, T) sign x = hard (φ', b, T) sign x := by
  unfold keyA at h
  unfold hard slice
  by_cases hA : actionA ∈ x <;> by_cases hB : actionB ∈ x <;> simp [hA, hB] at h ⊢
  simp [alpha, h]


theorem keyA_keyB_disj (x : Cube (Coord m)) (X Y : HalfSet m) (hA : keyA x = some X)
    (hB : keyB x = some Y) : False := by
  unfold keyA at hA
  unfold keyB at hB
  by_cases h : actionA ∈ x <;> simp [h] at hA hB

theorem mem_take_of_lt {α : Type} (H : List α) (i j : ℕ) (hj : j < H.length) (hji : j < i) :
    H[j] ∈ H.take i := by
  rw [List.mem_take_iff_getElem]
  exact ⟨j, by omega, by simp⟩

theorem exists_lt_of_mem_take {α : Type} (H : List α) (i : ℕ) (p : α) (hp : p ∈ H.take i) :
    ∃ s, ∃ hs : s < H.length, s < i ∧ H[s] = p := by
  rw [List.mem_take_iff_getElem] at hp
  obtain ⟨s, hs, rfl⟩ := hp
  exact ⟨s, by omega, by omega, by simp⟩

/-- A discovery forces a fresh-key event at some query position. -/
theorem discovers_event (φA φB : LabelMap m) (H : History (Coord m))
    (hD : Discovers φA φB H) :
    ∃ t < H.length, HistEvent H t keyB BadB φB ∨ HistEvent H t keyA BadA φA := by
  classical
  obtain ⟨p, hp, p', hp', h1, h2, h3, h4, hC⟩ := hD
  set Y := yPart p.1
  set X := xPart p'.1
  have hCe : parity X = φB Y ∧ φA X = parity Y := by
    unfold Center alpha beta at hC
    exact Prod.mk.inj hC
  have hkB : keyB p.1 = some Y := by simp [keyB, h1, h2, Y]
  have hkA : keyA p'.1 = some X := by simp [keyA, h3, h4, X]
  have exB : ∃ s, ∃ hs : s < H.length, keyB H[s].1 = some Y := by
    obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hp
    exact ⟨s, hs, hkB⟩
  have exA : ∃ s, ∃ hs : s < H.length, keyA H[s].1 = some X := by
    obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hp'
    exact ⟨s, hs, hkA⟩
  obtain ⟨hi, hiY⟩ := Nat.find_spec exB
  obtain ⟨hj, hjX⟩ := Nat.find_spec exA
  set i := Nat.find exB
  set j := Nat.find exA
  have minB : ∀ q ∈ H.take i, keyB q.1 ≠ some Y := by
    intro q hq hqY
    obtain ⟨s, hs, hsi, rfl⟩ := exists_lt_of_mem_take H i q hq
    exact Nat.find_min exB hsi ⟨hs, hqY⟩
  have minA : ∀ q ∈ H.take j, keyA q.1 ≠ some X := by
    intro q hq hqX
    obtain ⟨s, hs, hsj, rfl⟩ := exists_lt_of_mem_take H j q hq
    exact Nat.find_min exA hsj ⟨hs, hqX⟩
  rcases lt_trichotomy i j with hij | hij | hij
  · refine ⟨j, hj, Or.inr ⟨H[j].1, X, by simp [List.getElem?_eq_getElem hj], hjX, minA, ?_⟩⟩
    exact ⟨H[i], mem_take_of_lt H j i hi hij, Y, hiY, hCe.2.symm⟩
  · exfalso
    have : keyA H[i].1 = some X := by simp only [hij]; exact hjX
    exact keyA_keyB_disj _ _ _ this hiY
  · refine ⟨i, hi, Or.inl ⟨H[i].1, Y, by simp [List.getElem?_eq_getElem hi], hiY, minB, ?_⟩⟩
    exact ⟨H[j], mem_take_of_lt H i j hj hij, X, hjX, hCe.1⟩

end Apply


section Counting

open Classical

theorem count_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (P : β → Prop) :
    (Finset.univ.filter P).card = (Finset.univ.filter (fun a => P (e a))).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (e.subtypeEquiv (fun a => Iff.rfl)).symm

theorem count_prod {R0 W : Type} [Fintype R0] [Fintype W] (P : R0 × W → Prop) (n c : ℕ)
    (h : ∀ r0, (Finset.univ.filter (fun w => P (r0, w))).card * n ≤ c * Fintype.card W) :
    (Finset.univ.filter P).card * n ≤ c * Fintype.card (R0 × W) := by
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_mul]
  calc ∑ r0 : R0, (∑ w : W, if P (r0, w) then 1 else 0) * n
      ≤ ∑ _r0 : R0, c * Fintype.card W := by
        apply Finset.sum_le_sum
        intro r0 _
        rw [← Finset.card_filter]
        exact h r0
    _ = c * Fintype.card (R0 × W) := by
        simp [Fintype.card_prod]; ring

variable {m : ℕ}

def eB (m : ℕ) : (LabelMap m × Table m) × LabelMap m ≃ Sample m where
  toFun z := (z.1.1, z.2, z.1.2)
  invFun r := ((r.1, r.2.2), r.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

def eA (m : ℕ) : (LabelMap m × Table m) × LabelMap m ≃ Sample m where
  toFun z := (z.2, z.1.1, z.1.2)
  invFun r := ((r.2.1, r.2.2), r.1)
  left_inv _ := rfl
  right_inv _ := rfl

theorem countB (A : Procedure (Coord m)) (q t : ℕ) (sign : Bool) :
    (Finset.univ.filter (fun r : Sample m =>
      HistEvent (run A (hard r sign) q []).1 t keyB BadB r.2.1)).card * 2 ^ m
      ≤ t * Fintype.card (Sample m) := by
  rw [count_equiv (eB m), ← Fintype.card_congr (eB m)]
  apply count_prod
  intro r0
  have := fresh_key_count A q t (fun φ => hard (r0.1, φ, r0.2) sign) keyB
    (fun φ φ' x hx => hard_locB r0.1 r0.2 sign φ φ' x hx) BadB t
    (fun h hh => by have := (bad_card keyA parity h).trans hh; exact le_trans (Finset.card_le_card (fun v hv => by simp only [Finset.mem_filter] at hv ⊢; exact hv)) this)
  have hV : Fintype.card (Bits m) = 2 ^ m := by simp [Bits]
  rw [hV] at this
  exact this

theorem countA (A : Procedure (Coord m)) (q t : ℕ) (sign : Bool) :
    (Finset.univ.filter (fun r : Sample m =>
      HistEvent (run A (hard r sign) q []).1 t keyA BadA r.1)).card * 2 ^ m
      ≤ t * Fintype.card (Sample m) := by
  rw [count_equiv (eA m), ← Fintype.card_congr (eA m)]
  apply count_prod
  intro r0
  have := fresh_key_count A q t (fun φ => hard (φ, r0.1, r0.2) sign) keyA
    (fun φ φ' x hx => hard_locA r0.1 r0.2 sign φ φ' x hx) BadA t
    (fun h hh => by have := (bad_card keyB parity h).trans hh; exact le_trans (Finset.card_le_card (fun v hv => by simp only [Finset.mem_filter] at hv ⊢; exact hv)) this)
  have hV : Fintype.card (Bits m) = 2 ^ m := by simp [Bits]
  rw [hV] at this
  exact this

theorem disc_count (A : Procedure (Coord m)) (q : ℕ) (sign : Bool) :
    (Finset.univ.filter (fun r : Sample m =>
      Discovers r.1 r.2.1 (run A (hard r sign) q []).1)).card * 2 ^ m
      ≤ q ^ 2 * Fintype.card (Sample m) := by
  set EB := fun t => Finset.univ.filter (fun r : Sample m =>
      HistEvent (run A (hard r sign) q []).1 t keyB BadB r.2.1)
  set EA := fun t => Finset.univ.filter (fun r : Sample m =>
      HistEvent (run A (hard r sign) q []).1 t keyA BadA r.1)
  have hsub : Finset.univ.filter (fun r : Sample m =>
      Discovers r.1 r.2.1 (run A (hard r sign) q []).1) ⊆
      (Finset.range q).biUnion (fun t => EB t ∪ EA t) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    obtain ⟨t, ht, hE⟩ := discovers_event _ _ _ hr
    have hl := run_length A (hard r sign) q []
    simp only [List.length_nil, zero_add] at hl
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_union, EB, EA,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨t, by omega, hE⟩
  have hsum : (Finset.range q).sum (fun t => (EB t ∪ EA t).card * 2 ^ m)
      ≤ (Finset.range q).sum (fun t => 2 * t * Fintype.card (Sample m)) := by
    apply Finset.sum_le_sum
    intro t _
    have h1 := countB A q t sign
    have h2 := countA A q t sign
    have h3 := Finset.card_union_le (EB t) (EA t)
    calc (EB t ∪ EA t).card * 2 ^ m ≤ ((EB t).card + (EA t).card) * 2 ^ m :=
          Nat.mul_le_mul_right _ h3
      _ = (EB t).card * 2 ^ m + (EA t).card * 2 ^ m := by ring
      _ ≤ t * Fintype.card (Sample m) + t * Fintype.card (Sample m) := Nat.add_le_add h1 h2
      _ = 2 * t * Fintype.card (Sample m) := by ring
  have hgauss : (Finset.range q).sum (fun t => 2 * t * Fintype.card (Sample m))
      = q * (q - 1) * Fintype.card (Sample m) := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, mul_comm 2, Finset.sum_range_id_mul_two]
  calc _ ≤ ((Finset.range q).biUnion (fun t => EB t ∪ EA t)).card * 2 ^ m :=
        Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
    _ ≤ ((Finset.range q).sum (fun t => (EB t ∪ EA t).card)) * 2 ^ m :=
        Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = (Finset.range q).sum (fun t => (EB t ∪ EA t).card * 2 ^ m) := Finset.sum_mul _ _ _
    _ ≤ q * (q - 1) * Fintype.card (Sample m) := hsum.trans hgauss.le
    _ ≤ q ^ 2 * Fintype.card (Sample m) := by
        apply Nat.mul_le_mul_right
        rw [sq]
        exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

end Counting

end BTHelper_center_discovery

open BTHelper_center_discovery in
theorem solution {m : ℕ} (hm : 1 ≤ m) (A : Procedure (Coord m))
    (q : ℕ) (hbudget : Budget A q) (sign : Bool) :
    discoveryProbability A q sign ≤ (q : ℝ)^2 / 2^m := by
  classical
  have key := disc_count A q sign
  unfold discoveryProbability uniformProb
  have hpos : (0 : ℝ) < Fintype.card (Sample m) := by exact_mod_cast Fintype.card_pos
  rw [div_le_div_iff₀ hpos (by positivity)]
  have key' : ((Finset.univ.filter (fun r : Sample m =>
      Discovers r.1 r.2.1 (run A (hard r sign) q []).1)).card : ℝ) * 2 ^ m
      ≤ (q : ℝ) ^ 2 * Fintype.card (Sample m) := by exact_mod_cast key
  convert key' using 4
