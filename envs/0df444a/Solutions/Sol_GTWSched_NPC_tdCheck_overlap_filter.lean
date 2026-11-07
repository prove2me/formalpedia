-- Prove2me | solution 1 for GTWSched.NPC.tdCheck_overlap_filter
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T22:28:53.719964+00:00
-- url     : https://prove2.me/submissions/a1eef908-affd-4b38-ae51-341a7042eb48

import Mathlib
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_CookPvsNP_StackMacros
import Definitions.Def_ProjSchedTW_Complexity_Encoding

set_option autoImplicit false
set_option linter.all false

/-! Shared stack library for the d0bf0960 checker children (D0bfL).
Part 1: a generic one-pass Mealy scan loop, and the shape DFA for
`(encInts c).map ι1 ++ none :: (encNats d).map ι2`. -/

open CookPvsNP ProjSchedTW.Complexity

namespace D0bfL

/-! ## Generic Mealy scan -/

section Scan
variable {K A : Type} [DecidableEq K]

def scanAct (ki st : K) (δ : Option A → A → A) (out : K → Option A → A → Option A)
    (h : K → Option A) (k : K) : StackAct A :=
  match h ki with
  | none => .keep
  | some a =>
    if k = ki then .pop else if k = st then .push (δ (h st) a)
    else match out k (h st) a with
      | some b => .push b
      | none => .keep

def scanProg (ki st : K) (δ : Option A → A → A) (out : K → Option A → A → Option A) :
    StackProg K A :=
  .loop (fun h => (h ki).isSome) (.act (scanAct ki st δ out))

def scanStep (ki st : K) (δ : Option A → A → A) (out : K → Option A → A → Option A)
    (s : K → List A) (a : A) : K → List A := fun k =>
  if k = ki then (s ki).tail else if k = st then δ (s st).head? a :: s st
  else (out k (s st).head? a).toList ++ s k

def scanRun (ki st : K) (δ : Option A → A → A) (out : K → Option A → A → Option A) :
    List A → (K → List A) → (K → List A)
  | [], s => s
  | a :: l, s => scanRun ki st δ out l (scanStep ki st δ out s a)

lemma applyAct_scan (ki st : K) (δ : Option A → A → A) (out : K → Option A → A → Option A)
    (s : K → List A) (a : A) (l : List A) (hs : s ki = a :: l) :
    StackProg.applyAct (scanAct ki st δ out) s = scanStep ki st δ out s a := by
  funext k
  simp only [StackProg.applyAct, scanAct, scanStep, hs, List.head?_cons]
  by_cases h1 : k = ki
  · subst h1; simp [StackAct.apply, hs]
  · by_cases h2 : k = st
    · subst h2; simp [h1, StackAct.apply]
    · simp only [h1, h2, if_false]
      cases out k (s st).head? a <;> simp [StackAct.apply]

lemma exec_scan (ki st : K) (δ : Option A → A → A) (out : K → Option A → A → Option A) :
    ∀ (l : List A) (s : K → List A), s ki = l →
      (scanProg ki st δ out).Exec s (scanRun ki st δ out l s) (3 * l.length + 1) := by
  intro l
  induction l with
  | nil =>
    intro s hs
    exact StackProg.Exec.loopFalse (by simp [hs])
  | cons a l ih =>
    intro s hs
    have h1 := StackProg.Exec.act (scanAct ki st δ out) s
    rw [applyAct_scan ki st δ out s a l hs] at h1
    have h2 := ih (scanStep ki st δ out s a) (by simp [scanStep, hs])
    have h3 := StackProg.Exec.loopTrue (test := fun h => (h ki).isSome) (by simp [hs]) h1 h2
    simp only [scanRun, List.length_cons]
    have e : 3 * (l.length + 1) + 1 = 1 + 1 + 1 + (3 * l.length + 1) := by ring
    rw [e]; exact h3

/-- the state trace: `runQ q l` is the top of the state stack after scanning `l` from top `q`. -/
def runQ (δ : Option A → A → A) : Option A → List A → Option A
  | q, [] => q
  | q, a :: l => runQ δ (some (δ q a)) l

/-- what a non-state stack `k` receives (in stack order) while scanning `l` from top `q`. -/
def emitR (δ : Option A → A → A) (out : K → Option A → A → Option A) (k : K) :
    Option A → List A → List A
  | _, [] => []
  | q, a :: l => emitR δ out k (some (δ q a)) l ++ (out k q a).toList

lemma scanRun_ki (ki st : K) (δ : Option A → A → A) (out : K → Option A → A → Option A) :
    ∀ (l : List A) (s : K → List A), s ki = l → scanRun ki st δ out l s ki = [] := by
  intro l
  induction l with
  | nil => intro s hs; simpa [scanRun] using hs
  | cons a l ih => intro s hs; exact ih _ (by simp [scanStep, hs])

lemma scanRun_st (ki st : K) (hks : ki ≠ st) (δ : Option A → A → A)
    (out : K → Option A → A → Option A) :
    ∀ (l : List A) (s : K → List A), (scanRun ki st δ out l s st).head? = runQ δ (s st).head? l := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons a l ih =>
    intro s
    rw [scanRun, ih]
    simp [scanStep, Ne.symm hks, runQ]

lemma scanRun_other (ki st : K) (hks : ki ≠ st) (δ : Option A → A → A)
    (out : K → Option A → A → Option A) (k : K) (hk1 : k ≠ ki) (hk2 : k ≠ st) :
    ∀ (l : List A) (s : K → List A),
      scanRun ki st δ out l s k = emitR δ out k (s st).head? l ++ s k := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons a l ih =>
    intro s
    rw [scanRun, ih]
    simp [scanStep, hk1, hk2, Ne.symm hks, emitR]

end Scan

/-! ## The shape DFA -/

abbrev A := Option (BSym ⊕ BSym)

def ι1 (b : BSym) : A := some (Sum.inl b)
def ι2 (b : BSym) : A := some (Sum.inr b)
def dg (b : Bool) : BSym := if b then BSym.one else BSym.zero

/-- the input shape: an integer list, a `none` separator, a natural list. -/
def Ew (c : List ℤ) (d : List ℕ) : List A :=
  (encInts c).map ι1 ++ none :: (encNats d).map ι2

inductive DS
  | S0 | M | Z | O | T0 | TZ | TO | X
  deriving DecidableEq

open DS

def dstep : DS → A → DS
  | S0, some (.inl .minus) => M
  | S0, some (.inl .sep) => S0
  | O, some (.inl .sep) => S0
  | S0, none => T0
  | S0, some (.inl .zero) => Z
  | M, some (.inl .zero) => Z
  | Z, some (.inl .zero) => Z
  | O, some (.inl .zero) => Z
  | S0, some (.inl .one) => O
  | M, some (.inl .one) => O
  | Z, some (.inl .one) => O
  | O, some (.inl .one) => O
  | T0, some (.inr .zero) => TZ
  | TZ, some (.inr .zero) => TZ
  | TO, some (.inr .zero) => TZ
  | T0, some (.inr .one) => TO
  | TZ, some (.inr .one) => TO
  | TO, some (.inr .one) => TO
  | T0, some (.inr .sep) => T0
  | TO, some (.inr .sep) => T0
  | _, _ => X

def runD (q : DS) (l : List A) : DS := l.foldl dstep q

@[simp] lemma runD_nil (q : DS) : runD q [] = q := rfl
@[simp] lemma runD_cons (q : DS) (a : A) (l : List A) : runD q (a :: l) = runD (dstep q a) l := rfl
lemma runD_append (q : DS) (l l' : List A) : runD q (l ++ l') = runD (runD q l) l' := by
  simp [runD, List.foldl_append]

@[simp] lemma runD_X : ∀ l : List A, runD X l = X := by
  intro l; induction l with
  | nil => rfl
  | cons a l ih => rw [runD_cons]; cases a <;> exact ih

/-! ### canonical bit lists -/

lemma bits_getLast : ∀ k : ℕ, k ≠ 0 → (Nat.bits k).getLast? = some true := by
  intro k
  induction k using Nat.binaryRec' with
  | zero => intro h; exact absurd rfl h
  | bit b n hn ih =>
    intro _
    rw [Nat.bits_append_bit _ _ hn]
    by_cases h0 : n = 0
    · subst h0; have := hn rfl; subst this; simp
    · have := ih h0
      rw [List.getLast?_cons]
      simp [this]

lemma canon_bits : ∀ bs : List Bool, (bs = [] ∨ bs.getLast? = some true) → ∃ k, Nat.bits k = bs := by
  intro bs
  induction bs with
  | nil => intro _; exact ⟨0, by simp⟩
  | cons b bs ih =>
    intro h
    rcases bs with _ | ⟨b', bs'⟩
    · have hb : b = true := by simpa using h
      subst hb
      exact ⟨1, by
        have := Nat.bits_append_bit 0 true (by simp)
        simpa using this⟩
    · have hl : (b' :: bs').getLast? = some true := by
        rcases h with h | h
        · simp at h
        · rw [List.getLast?_cons_cons] at h; exact h
      obtain ⟨k, hk⟩ := ih (Or.inr hl)
      have hk0 : k ≠ 0 := by rintro rfl; simp at hk
      refine ⟨Nat.bit b k, ?_⟩
      rw [Nat.bits_append_bit _ _ (fun h => absurd h hk0), hk]

/-! ### the natural-number part -/

lemma dpart_digits : ∀ (l : List A) (q : DS), (q = TZ ∨ q = TO) → runD q l = T0 →
    ∃ (bs : List Bool) (rest : List A), l = bs.map (ι2 ∘ dg) ++ ι2 .sep :: rest ∧
      (bs.getLast? = some true ∨ (bs = [] ∧ q = TO)) ∧ runD T0 rest = T0 := by
  intro l
  induction l with
  | nil => intro q hq h; rcases hq with rfl | rfl <;> simp at h
  | cons a l ih =>
    intro q hq h
    rw [runD_cons] at h
    rcases a with _ | (b | b)
    · rcases hq with rfl | rfl <;> simp [dstep] at h
    · rcases hq with rfl | rfl <;> cases b <;> simp [dstep] at h
    · cases b with
      | zero =>
        have hd : dstep q (some (.inr .zero)) = TZ := by rcases hq with rfl | rfl <;> rfl
        rw [hd] at h
        obtain ⟨bs, rest, h1, h2, h3⟩ := ih TZ (Or.inl rfl) h
        refine ⟨false :: bs, rest, by simp [h1, ι2, dg], Or.inl ?_, h3⟩
        rcases h2 with h2 | ⟨_, h2⟩
        · rw [List.getLast?_cons]; simp [h2]
        · exact absurd h2 (by decide)
      | one =>
        have hd : dstep q (some (.inr .one)) = TO := by rcases hq with rfl | rfl <;> rfl
        rw [hd] at h
        obtain ⟨bs, rest, h1, h2, h3⟩ := ih TO (Or.inr rfl) h
        refine ⟨true :: bs, rest, by simp [h1, ι2, dg], Or.inl ?_, h3⟩
        rcases h2 with h2 | ⟨h2, _⟩
        · rw [List.getLast?_cons]; simp [h2]
        · subst h2; simp
      | minus => rcases hq with rfl | rfl <;> simp [dstep] at h
      | sep =>
        rcases hq with rfl | rfl
        · simp [dstep] at h
        · exact ⟨[], l, rfl, Or.inr ⟨rfl, rfl⟩, by simpa [dstep] using h⟩

lemma encNats_cons (k : ℕ) (d : List ℕ) : encNats (k :: d) = encNat k ++ encNats d := by
  simp [encNats]

lemma encInts_cons (z : ℤ) (c : List ℤ) : encInts (z :: c) = encInt z ++ encInts c := by
  simp [encInts]

lemma dpart_sound : ∀ (L : ℕ) (l : List A), l.length ≤ L → runD T0 l = T0 →
    ∃ d : List ℕ, l = (encNats d).map ι2 := by
  intro L
  induction L with
  | zero =>
    intro l hl _
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact ⟨[], by simp [this, encNats]⟩
  | succ L ih =>
    intro l hl h
    rcases l with _ | ⟨a, l⟩
    · exact ⟨[], by simp [encNats]⟩
    rw [runD_cons] at h
    simp only [List.length_cons] at hl
    rcases a with _ | (b | b)
    · simp [dstep] at h
    · cases b <;> simp [dstep] at h
    · cases b with
      | sep =>
        obtain ⟨d, hd⟩ := ih l (by omega) (by simpa [dstep] using h)
        exact ⟨0 :: d, by simp [hd, encNats_cons, encNat, ι2]⟩
      | minus => simp [dstep] at h
      | zero =>
        obtain ⟨bs, rest, h1, h2, h3⟩ := dpart_digits l TZ (Or.inl rfl) (by simpa [dstep] using h)
        have hc : (false :: bs) = [] ∨ (false :: bs).getLast? = some true := by
          rcases h2 with h2 | ⟨_, h2⟩
          · right; rw [List.getLast?_cons]; simp [h2]
          · exact absurd h2 (by decide)
        obtain ⟨k, hk⟩ := canon_bits _ hc
        have hlen : rest.length ≤ L := by
          have := congrArg List.length h1; simp at this; omega
        obtain ⟨d, hd⟩ := ih rest hlen h3
        refine ⟨k :: d, ?_⟩
        rw [encNats_cons, List.map_append, ← hd, encNat, hk, h1]
        simp [ι2, dg]
      | one =>
        obtain ⟨bs, rest, h1, h2, h3⟩ := dpart_digits l TO (Or.inr rfl) (by simpa [dstep] using h)
        have hc : (true :: bs) = [] ∨ (true :: bs).getLast? = some true := by
          right
          rcases h2 with h2 | ⟨h2, _⟩
          · rw [List.getLast?_cons]; simp [h2]
          · subst h2; simp
        obtain ⟨k, hk⟩ := canon_bits _ hc
        have hlen : rest.length ≤ L := by
          have := congrArg List.length h1; simp at this; omega
        obtain ⟨d, hd⟩ := ih rest hlen h3
        refine ⟨k :: d, ?_⟩
        rw [encNats_cons, List.map_append, ← hd, encNat, hk, h1]
        simp [ι2, dg]

lemma dpart_bits : ∀ (k : ℕ) (q : DS), (q = T0 ∨ q = TZ ∨ q = TO) → k ≠ 0 →
    runD q ((Nat.bits k).map (ι2 ∘ dg)) = TO := by
  intro k
  induction k using Nat.binaryRec' with
  | zero => intro q _ h; exact absurd rfl h
  | bit b n hn ih =>
    intro q hq _
    rw [Nat.bits_append_bit _ _ hn, List.map_cons, runD_cons]
    by_cases h0 : n = 0
    · subst h0
      have hb := hn rfl; subst hb
      rcases hq with rfl | rfl | rfl <;> rfl
    · apply ih _ _ h0
      rcases hq with rfl | rfl | rfl <;> cases b <;> simp [dstep, ι2, dg]

lemma encNat_dg (k : ℕ) : encNat k = (Nat.bits k).map dg ++ [BSym.sep] := rfl

lemma dpart_complete : ∀ d : List ℕ, runD T0 ((encNats d).map ι2) = T0 := by
  intro d
  induction d with
  | nil => rfl
  | cons k d ih =>
    rw [encNats_cons, List.map_append, runD_append, encNat_dg, List.map_append, runD_append]
    by_cases hk : k = 0
    · subst hk; simpa [ι2, dstep] using ih
    · rw [List.map_map, dpart_bits k T0 (Or.inl rfl) hk]
      simpa [ι2, dstep] using ih

/-! ### the integer part -/

lemma cpart_digits : ∀ (l : List A) (q : DS), (q = M ∨ q = Z ∨ q = O) → runD q l = T0 →
    ∃ (bs : List Bool) (rest : List A), l = bs.map (ι1 ∘ dg) ++ ι1 .sep :: rest ∧
      (bs.getLast? = some true ∨ (bs = [] ∧ q = O)) ∧ runD S0 rest = T0 := by
  intro l
  induction l with
  | nil => intro q hq h; rcases hq with rfl | rfl | rfl <;> simp at h
  | cons a l ih =>
    intro q hq h
    rw [runD_cons] at h
    rcases a with _ | (b | b)
    · rcases hq with rfl | rfl | rfl <;> simp [dstep] at h
    · cases b with
      | zero =>
        have hd : dstep q (some (.inl .zero)) = Z := by rcases hq with rfl | rfl | rfl <;> rfl
        rw [hd] at h
        obtain ⟨bs, rest, h1, h2, h3⟩ := ih Z (Or.inr (Or.inl rfl)) h
        refine ⟨false :: bs, rest, by simp [h1, ι1, dg], Or.inl ?_, h3⟩
        rcases h2 with h2 | ⟨_, h2⟩
        · rw [List.getLast?_cons]; simp [h2]
        · exact absurd h2 (by decide)
      | one =>
        have hd : dstep q (some (.inl .one)) = O := by rcases hq with rfl | rfl | rfl <;> rfl
        rw [hd] at h
        obtain ⟨bs, rest, h1, h2, h3⟩ := ih O (Or.inr (Or.inr rfl)) h
        refine ⟨true :: bs, rest, by simp [h1, ι1, dg], Or.inl ?_, h3⟩
        rcases h2 with h2 | ⟨h2, _⟩
        · rw [List.getLast?_cons]; simp [h2]
        · subst h2; simp
      | minus => rcases hq with rfl | rfl | rfl <;> simp [dstep] at h
      | sep =>
        rcases hq with rfl | rfl | rfl
        · simp [dstep] at h
        · simp [dstep] at h
        · exact ⟨[], l, rfl, Or.inr ⟨rfl, rfl⟩, by simpa [dstep] using h⟩
    · rcases hq with rfl | rfl | rfl <;> cases b <;> simp [dstep] at h

lemma encInt_neg (k : ℕ) (hk : k ≠ 0) :
    encInt (-(k : ℤ)) = BSym.minus :: ((Nat.bits k).map dg ++ [BSym.sep]) := by
  have h : (-(k : ℤ)) < 0 := by omega
  simp only [encInt, if_pos h, Int.natAbs_neg, Int.natAbs_natCast, List.singleton_append]; rfl

lemma encInt_nat (k : ℕ) : encInt (k : ℤ) = (Nat.bits k).map dg ++ [BSym.sep] := by
  have h : ¬ ((k : ℤ) < 0) := by omega
  simp only [encInt, if_neg h, Int.natAbs_natCast, List.nil_append]; rfl

lemma cpart_sound : ∀ (L : ℕ) (l : List A), l.length ≤ L → runD S0 l = T0 →
    ∃ (c : List ℤ) (d : List ℕ), l = Ew c d := by
  intro L
  induction L with
  | zero =>
    intro l hl h
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp at h
  | succ L ih =>
    intro l hl h
    rcases l with _ | ⟨a, l⟩
    · simp at h
    rw [runD_cons] at h
    simp only [List.length_cons] at hl
    rcases a with _ | (b | b)
    · obtain ⟨d, hd⟩ := dpart_sound l.length l le_rfl (by simpa [dstep] using h)
      exact ⟨[], d, by simp [Ew, hd, encInts]⟩
    · cases b with
      | sep =>
        obtain ⟨c, d, hcd⟩ := ih l (by omega) (by simpa [dstep] using h)
        exact ⟨0 :: c, d, by simp [hcd, Ew, encInts_cons, encInt, encNat, ι1]⟩
      | minus =>
        obtain ⟨bs, rest, h1, h2, h3⟩ := cpart_digits l M (Or.inl rfl) (by simpa [dstep] using h)
        have hl2 : bs.getLast? = some true := by
          rcases h2 with h2 | ⟨_, h2⟩
          · exact h2
          · exact absurd h2 (by decide)
        obtain ⟨k, hk⟩ := canon_bits _ (Or.inr hl2)
        have hk0 : k ≠ 0 := by rintro rfl; simp at hk; subst hk; simp at hl2
        have hlen : rest.length ≤ L := by
          have := congrArg List.length h1; simp at this; omega
        obtain ⟨c, d, hcd⟩ := ih rest hlen h3
        refine ⟨-(k : ℤ) :: c, d, ?_⟩
        rw [h1, hcd]
        simp only [Ew, encInts_cons, encInt_neg k hk0, hk]
        simp [ι1, dg]
      | zero =>
        obtain ⟨bs, rest, h1, h2, h3⟩ := cpart_digits l Z (Or.inr (Or.inl rfl))
          (by simpa [dstep] using h)
        have hc : (false :: bs) = [] ∨ (false :: bs).getLast? = some true := by
          rcases h2 with h2 | ⟨_, h2⟩
          · right; rw [List.getLast?_cons]; simp [h2]
          · exact absurd h2 (by decide)
        obtain ⟨k, hk⟩ := canon_bits _ hc
        have hlen : rest.length ≤ L := by
          have := congrArg List.length h1; simp at this; omega
        obtain ⟨c, d, hcd⟩ := ih rest hlen h3
        refine ⟨(k : ℤ) :: c, d, ?_⟩
        rw [h1, hcd]
        simp only [Ew, encInts_cons, encInt_nat k, hk]
        simp [ι1, dg]
      | one =>
        obtain ⟨bs, rest, h1, h2, h3⟩ := cpart_digits l O (Or.inr (Or.inr rfl))
          (by simpa [dstep] using h)
        have hc : (true :: bs) = [] ∨ (true :: bs).getLast? = some true := by
          right
          rcases h2 with h2 | ⟨h2, _⟩
          · rw [List.getLast?_cons]; simp [h2]
          · subst h2; simp
        obtain ⟨k, hk⟩ := canon_bits _ hc
        have hlen : rest.length ≤ L := by
          have := congrArg List.length h1; simp at this; omega
        obtain ⟨c, d, hcd⟩ := ih rest hlen h3
        refine ⟨(k : ℤ) :: c, d, ?_⟩
        rw [h1, hcd]
        simp only [Ew, encInts_cons, encInt_nat k, hk]
        simp [ι1, dg]
    · cases b <;> simp [dstep] at h

lemma cpart_bits : ∀ (k : ℕ) (q : DS), (q = S0 ∨ q = M ∨ q = Z ∨ q = O) → k ≠ 0 →
    runD q ((Nat.bits k).map (ι1 ∘ dg)) = O := by
  intro k
  induction k using Nat.binaryRec' with
  | zero => intro q _ h; exact absurd rfl h
  | bit b n hn ih =>
    intro q hq _
    rw [Nat.bits_append_bit _ _ hn, List.map_cons, runD_cons]
    by_cases h0 : n = 0
    · subst h0
      have hb := hn rfl; subst hb
      rcases hq with rfl | rfl | rfl | rfl <;> rfl
    · apply ih _ _ h0
      rcases hq with rfl | rfl | rfl | rfl <;> cases b <;> simp [dstep, ι1, dg]

lemma cpart_int (z : ℤ) : runD S0 ((encInt z).map ι1) = S0 := by
  rcases lt_or_ge z 0 with hz | hz
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, z = -(k : ℤ) := ⟨z.natAbs, by omega⟩
    have hk : k ≠ 0 := by omega
    rw [encInt_neg k hk, List.map_cons, runD_cons, List.map_append, runD_append, List.map_map,
      show dstep S0 (ι1 .minus) = M from rfl, cpart_bits k M (Or.inr (Or.inl rfl)) hk]
    rfl
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, z = (k : ℤ) := ⟨z.natAbs, by omega⟩
    rw [encInt_nat, List.map_append, runD_append, List.map_map]
    by_cases hk : k = 0
    · subst hk; rfl
    · rw [cpart_bits k S0 (Or.inl rfl) hk]; rfl

lemma cpart_complete (c : List ℤ) (d : List ℕ) : runD S0 (Ew c d) = T0 := by
  have hc : ∀ c : List ℤ, runD S0 ((encInts c).map ι1) = S0 := by
    intro c
    induction c with
    | nil => rfl
    | cons z c ih => rw [encInts_cons, List.map_append, runD_append, cpart_int, ih]
  rw [Ew, runD_append, hc, runD_cons]
  exact dpart_complete d

/-- the shape DFA accepts exactly the well-shaped words. -/
theorem runD_iff (u : List A) : runD S0 u = T0 ↔ ∃ (c : List ℤ) (d : List ℕ), u = Ew c d := by
  constructor
  · exact cpart_sound u.length u le_rfl
  · rintro ⟨c, d, rfl⟩; exact cpart_complete c d

/-! ## Generic transfer / copy / halving (ported from P5c6, generic in `K`, `A`) -/

section Basic
variable {K A : Type} [DecidableEq K]

lemma exec_transfer (src : K) (targets : K → Bool) :
    ∀ (l : List A) (s : K → List A), s src = l →
      ∃ n ≤ 3 * l.length + 1, (transferProg src targets).Exec s (transferStore src targets s) n := by
  intro l
  induction l with
  | nil =>
    intro s hs
    refine ⟨1, by simp, ?_⟩
    have : transferStore src targets s = s := by
      funext k; simp only [transferStore]
      split_ifs with h1 h2 <;> simp_all
    rw [this]
    exact StackProg.Exec.loopFalse (by simp [hs])
  | cons a l ih =>
    intro s hs
    obtain ⟨s1, hs1⟩ : ∃ s1, s1 = StackProg.applyAct (transferAct src targets) s := ⟨_, rfl⟩
    have e1 : s1 src = l := by
      rw [hs1]; simp [StackProg.applyAct, transferAct, StackAct.apply, hs]
    obtain ⟨m, hm, hex⟩ := ih s1 e1
    refine ⟨1 + 1 + 1 + m, by simp; omega, ?_⟩
    have hpost : transferStore src targets s1 = transferStore src targets s := by
      funext k; simp only [transferStore]
      by_cases k1 : k = src
      · simp [k1]
      by_cases k2 : targets k = true
      · simp [k1, k2, e1, hs, hs1, StackProg.applyAct, transferAct, StackAct.apply]
      · simp [k1, k2, hs1, StackProg.applyAct, transferAct, StackAct.apply]
    rw [← hpost]; subst hs1
    exact StackProg.Exec.loopTrue (by simp [hs]) (StackProg.Exec.act _ _) hex

lemma exec_copy (src dst scr : K) (h1 : src ≠ dst) (h2 : src ≠ scr) (h3 : dst ≠ scr)
    (s : K → List A) (hs : s scr = []) :
    ∃ n ≤ 6 * (s src).length + 3,
      (copyProg src dst scr).Exec s (Function.update s dst (s src ++ s dst)) n := by
  obtain ⟨n1, hn1, e1⟩ := exec_transfer src (fun k => decide (k = scr)) (s src) s rfl
  set s1 := transferStore src (fun k => decide (k = scr)) s with hs1
  have hs1scr : s1 scr = (s src).reverse := by simp [hs1, transferStore, h2.symm, hs]
  obtain ⟨n2, hn2, e2⟩ := exec_transfer scr (fun k => decide (k = src ∨ k = dst)) _ s1 hs1scr
  refine ⟨n1 + 1 + n2, by simp at hn2; omega, ?_⟩
  have : transferStore scr (fun k => decide (k = src ∨ k = dst)) s1 =
      Function.update s dst (s src ++ s dst) := by
    funext k
    by_cases k1 : k = scr
    · subst k1; simp [transferStore, h3.symm, hs]
    by_cases k2 : k = src
    · subst k2; simp [transferStore, hs1, k1, h1, Ne.symm k1, hs]
    by_cases k3 : k = dst
    · subst k3; simp [transferStore, hs1, k1, k2, h2.symm, h3, hs]
    · simp [transferStore, hs1, k1, k2, k3]
  rw [← this]
  exact StackProg.Exec.seq e1 e2

end Basic


/-! ## Phase A scan: the DFA on a state stack plus counters and part copies -/

section ScanA
open DS

/-- states as stack symbols -/
def dsA : DS → A
  | S0 => some (.inr .minus) | M => some (.inl .minus) | Z => some (.inl .zero)
  | O => some (.inl .one) | T0 => some (.inr .sep) | TZ => some (.inr .zero)
  | TO => some (.inr .one) | X => some (.inl .sep)

def decS : Option A → DS
  | some (some (.inl .minus)) => M
  | some (some (.inl .zero)) => Z
  | some (some (.inl .one)) => O
  | some (some (.inr .sep)) => T0
  | some (some (.inr .zero)) => TZ
  | some (some (.inr .one)) => TO
  | some (some (.inl .sep)) => X
  | some none => X
  | _ => S0

lemma decS_dsA (q : DS) : decS (some (dsA q)) = q := by cases q <;> rfl

lemma dsA_inj {q q' : DS} (h : dsA q = dsA q') : q = q' := by
  rw [← decS_dsA q, ← decS_dsA q', h]

def δA (q : Option A) (a : A) : A := dsA (dstep (decS q) a)

lemma runQ_some : ∀ (l : List A) (q : DS), runQ δA (some (dsA q)) l = some (dsA (runD q l)) := by
  intro l
  induction l with
  | nil => intro q; rfl
  | cons a l ih => intro q; simp only [runQ, δA, decS_dsA, ih, runD_cons]

lemma runQ_none_accept (u : List A) :
    runQ δA none u = some (dsA T0) ↔ ∃ (c : List ℤ) (d : List ℕ), u = Ew c d := by
  rw [← runD_iff]
  rcases u with _ | ⟨a, l⟩
  · simp [runQ]
  · simp only [runQ, δA, runQ_some, runD_cons, Option.some.injEq]
    have : decS none = S0 := rfl
    rw [this]
    exact ⟨fun h => dsA_inj h, fun h => by rw [h]⟩

def mkA : A := none

def gc (a : A) : Option A := if a = ι1 .sep then some mkA else none
def gd (a : A) : Option A := if a = ι2 .sep then some mkA else none
def gC (a : A) : Option A := match a with | some (.inl _) => some a | _ => none
def gD (a : A) : Option A := match a with | some (.inr _) => some a | _ => none

lemma encInt_split (z : ℤ) : encInt z =
    ((if z < 0 then [BSym.minus] else []) ++ (Nat.bits z.natAbs).map dg) ++ [BSym.sep] := by
  simp only [encInt, encNat_dg, List.append_assoc]

lemma pre_no_sep (z : ℤ) : ∀ b ∈ ((if z < 0 then [BSym.minus] else []) ++ (Nat.bits z.natAbs).map dg),
    b ≠ BSym.sep := by
  intro b hb
  simp only [List.mem_append, List.mem_map] at hb
  rcases hb with hb | ⟨x, -, rfl⟩
  · split_ifs at hb <;> simp_all
  · cases x <;> simp [dg]

lemma digits_no_sep (k : ℕ) : ∀ b ∈ (Nat.bits k).map dg, b ≠ BSym.sep := by
  intro b hb
  simp only [List.mem_map] at hb
  obtain ⟨x, -, rfl⟩ := hb
  cases x <;> simp [dg]

lemma fm_ι2_gc (l : List BSym) : (l.map ι2).filterMap gc = [] := by
  induction l <;> simp_all [gc, ι1, ι2]
lemma fm_ι1_gd (l : List BSym) : (l.map ι1).filterMap gd = [] := by
  induction l <;> simp_all [gd, ι1, ι2]
lemma fm_ι2_gC (l : List BSym) : (l.map ι2).filterMap gC = [] := by
  induction l <;> simp_all [gC, ι2]
lemma fm_ι1_gD (l : List BSym) : (l.map ι1).filterMap gD = [] := by
  induction l <;> simp_all [gD, ι1]
lemma fm_ι1_gC (l : List BSym) : (l.map ι1).filterMap gC = l.map ι1 := by
  induction l <;> simp_all [gC, ι1]
lemma fm_ι2_gD (l : List BSym) : (l.map ι2).filterMap gD = l.map ι2 := by
  induction l <;> simp_all [gD, ι2]
lemma fm_ι1_gc_nosep (l : List BSym) (h : ∀ b ∈ l, b ≠ BSym.sep) : (l.map ι1).filterMap gc = [] := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have hb := h b List.mem_cons_self
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp [gc, ι1, hb, this]
lemma fm_ι2_gd_nosep (l : List BSym) (h : ∀ b ∈ l, b ≠ BSym.sep) : (l.map ι2).filterMap gd = [] := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have hb := h b List.mem_cons_self
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp [gd, ι2, hb, this]

lemma fm_gc (c : List ℤ) (d : List ℕ) : (Ew c d).filterMap gc = List.replicate c.length mkA := by
  have h0 : gc none = none := by simp [gc, ι1]
  rw [Ew, List.filterMap_append, List.filterMap_cons_none h0, fm_ι2_gc, List.append_nil]
  induction c with
  | nil => rfl
  | cons z c ih =>
    rw [encInts_cons, List.map_append, List.filterMap_append, ih, encInt_split, List.map_append,
      List.filterMap_append, fm_ι1_gc_nosep _ (pre_no_sep z)]
    simp [gc, ι1, List.replicate_succ]

lemma fm_gd (c : List ℤ) (d : List ℕ) : (Ew c d).filterMap gd = List.replicate d.length mkA := by
  have h0 : gd none = none := by simp [gd, ι2]
  rw [Ew, List.filterMap_append, List.filterMap_cons_none h0, fm_ι1_gd, List.nil_append]
  induction d with
  | nil => rfl
  | cons k d ih =>
    rw [encNats_cons, List.map_append, List.filterMap_append, ih, encNat_dg, List.map_append,
      List.filterMap_append, fm_ι2_gd_nosep _ (digits_no_sep k)]
    simp [gd, ι2, List.replicate_succ]

lemma fm_gC (c : List ℤ) (d : List ℕ) : (Ew c d).filterMap gC = (encInts c).map ι1 := by
  have h0 : gC none = none := rfl
  rw [Ew, List.filterMap_append, List.filterMap_cons_none h0, fm_ι2_gC, List.append_nil, fm_ι1_gC]

lemma fm_gD (c : List ℤ) (d : List ℕ) : (Ew c d).filterMap gD = (encNats d).map ι2 := by
  have h0 : gD none = none := rfl
  rw [Ew, List.filterMap_append, List.filterMap_cons_none h0, fm_ι1_gD, List.nil_append, fm_ι2_gD]

variable {K : Type} [DecidableEq K]

lemma emitR_indep (δ : Option A → A → A) (out : K → Option A → A → Option A) (k : K)
    (g : A → Option A) (hg : ∀ q a, out k q a = g a) :
    ∀ (l : List A) (q : Option A), emitR δ out k q l = (l.filterMap g).reverse := by
  intro l
  induction l with
  | nil => intro q; rfl
  | cons a l ih =>
    intro q
    rw [emitR, ih, hg, List.filterMap_cons]
    cases g a <;> simp

/-- the phase-A output function: counters `kc`, `kd` and part copies `kC`, `kD`. -/
def outA (kc kd kC kD : K) (k : K) (_q : Option A) (a : A) : Option A :=
  if k = kc then gc a else if k = kd then gd a else if k = kC then gC a
  else if k = kD then gD a else none

end ScanA

section ScanA2
variable {K : Type} [DecidableEq K]

/-- Phase-A scan, summarised. -/
lemma scanA_result (ki st kc kd kC kD : K) (h01 : ki ≠ st)
    (hc0 : kc ≠ ki) (hc1 : kc ≠ st) (hd0 : kd ≠ ki) (hd1 : kd ≠ st)
    (hC0 : kC ≠ ki) (hC1 : kC ≠ st) (hD0 : kD ≠ ki) (hD1 : kD ≠ st)
    (hcd : kc ≠ kd) (hcC : kc ≠ kC) (hcD : kc ≠ kD) (hdC : kd ≠ kC) (hdD : kd ≠ kD) (hCD : kC ≠ kD)
    (u : List A) (s : K → List A) (hs : s ki = u) (hst : s st = [])
    (hkc : s kc = []) (hkd : s kd = []) (hkC : s kC = []) (hkD : s kD = []) :
    (scanProg ki st δA (outA kc kd kC kD)).Exec s (scanRun ki st δA (outA kc kd kC kD) u s)
        (3 * u.length + 1) ∧
      ((scanRun ki st δA (outA kc kd kC kD) u s st).head? = some (dsA DS.T0) ↔
        ∃ (c : List ℤ) (d : List ℕ), u = Ew c d) ∧
      (∀ c d, u = Ew c d →
        scanRun ki st δA (outA kc kd kC kD) u s kc = List.replicate c.length mkA ∧
        scanRun ki st δA (outA kc kd kC kD) u s kd = List.replicate d.length mkA ∧
        scanRun ki st δA (outA kc kd kC kD) u s kC = ((encInts c).map ι1).reverse ∧
        scanRun ki st δA (outA kc kd kC kD) u s kD = ((encNats d).map ι2).reverse) ∧
      (∀ k, k ≠ ki → k ≠ st → k ≠ kc → k ≠ kd → k ≠ kC → k ≠ kD →
        scanRun ki st δA (outA kc kd kC kD) u s k = s k) := by
  set out := outA kc kd kC kD with hout
  refine ⟨exec_scan ki st δA out u s hs, ?_, ?_, ?_⟩
  · rw [scanRun_st ki st h01, hst]
    exact runQ_none_accept u
  · intro c d hu
    have ec : ∀ q a, out kc q a = gc a := by intro q a; simp [hout, outA]
    have ed : ∀ q a, out kd q a = gd a := by intro q a; simp [hout, outA, Ne.symm hcd]
    have eC : ∀ q a, out kC q a = gC a := by intro q a; simp [hout, outA, Ne.symm hcC, Ne.symm hdC]
    have eD : ∀ q a, out kD q a = gD a := by
      intro q a; simp [hout, outA, Ne.symm hcD, Ne.symm hdD, Ne.symm hCD]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [scanRun_other ki st h01 δA out kc hc0 hc1, emitR_indep δA out kc gc ec, hkc, hu, fm_gc]
      simp
    · rw [scanRun_other ki st h01 δA out kd hd0 hd1, emitR_indep δA out kd gd ed, hkd, hu, fm_gd]
      simp
    · rw [scanRun_other ki st h01 δA out kC hC0 hC1, emitR_indep δA out kC gC eC, hkC, hu, fm_gC]
      simp
    · rw [scanRun_other ki st h01 δA out kD hD0 hD1, emitR_indep δA out kD gD eD, hkD, hu, fm_gD]
      simp
  · intro k k0 k1 k2 k3 k4 k5
    have e : ∀ q a, out k q a = (fun _ => none) a := by intro q a; simp [hout, outA, k2, k3, k4, k5]
    rw [scanRun_other ki st h01 δA out k k0 k1, emitR_indep δA out k _ e]
    simp

end ScanA2

/-! ## Unary arithmetic: synchronous pop, repeated copy, division -/

section Unary
variable {K A : Type} [DecidableEq K]

def syncPopAct (i j : K) (_h : K → Option A) (k : K) : StackAct A :=
  if k = i ∨ k = j then .pop else .keep

/-- pop `i` and `j` together while both are nonempty. -/
def syncPopProg (i j : K) : StackProg K A :=
  .loop (fun h => (h i).isSome && (h j).isSome) (.act (syncPopAct i j))

lemma exec_syncPop (i j : K) (hij : i ≠ j) : ∀ (L : ℕ) (s : K → List A),
    min (s i).length (s j).length = L →
    (syncPopProg i j).Exec s
      (Function.update (Function.update s i ((s i).drop L)) j ((s j).drop L)) (3 * L + 1) := by
  intro L
  induction L with
  | zero =>
    intro s hL
    have hpost : Function.update (Function.update s i ((s i).drop 0)) j ((s j).drop 0) = s := by
      funext k; by_cases k1 : k = j
      · subst k1; simp
      · by_cases k2 : k = i
        · subst k2; simp [k1]
        · simp [k1, k2]
    rw [hpost]
    refine StackProg.Exec.loopFalse ?_
    rcases Nat.min_eq_zero_iff.1 hL with h | h
    · simp [List.eq_nil_of_length_eq_zero h]
    · simp [List.eq_nil_of_length_eq_zero h]
  | succ L ih =>
    intro s hL
    obtain ⟨a, l1, h1⟩ : ∃ a l1, s i = a :: l1 := by
      rcases h : s i with _ | ⟨a, l1⟩
      · rw [h] at hL; simp at hL
      · exact ⟨a, l1, rfl⟩
    obtain ⟨b, l2, h2⟩ : ∃ b l2, s j = b :: l2 := by
      rcases h : s j with _ | ⟨b, l2⟩
      · rw [h] at hL; simp at hL
      · exact ⟨b, l2, rfl⟩
    set s1 := StackProg.applyAct (syncPopAct i j) s with hs1
    have e1i : s1 i = l1 := by simp [hs1, StackProg.applyAct, syncPopAct, StackAct.apply, h1]
    have e1j : s1 j = l2 := by simp [hs1, StackProg.applyAct, syncPopAct, StackAct.apply, h2]
    have hL1 : min (s1 i).length (s1 j).length = L := by
      rw [e1i, e1j]; rw [h1, h2] at hL; simp at hL; omega
    have e2 := ih s1 hL1
    have hpost : Function.update (Function.update s1 i ((s1 i).drop L)) j ((s1 j).drop L) =
        Function.update (Function.update s i ((s i).drop (L + 1))) j ((s j).drop (L + 1)) := by
      funext k
      by_cases k1 : k = j
      · subst k1; simp [e1j, h2]
      by_cases k2 : k = i
      · subst k2; simp [k1, e1i, h1]
      · simp [k1, k2, hs1, StackProg.applyAct, syncPopAct, StackAct.apply]
    rw [← hpost, show 3 * (L + 1) + 1 = 1 + 1 + 1 + (3 * L + 1) by ring]
    exact StackProg.Exec.loopTrue (by simp [h1, h2]) (StackProg.Exec.act _ _) e2

lemma exec_pop (c : K) (s : K → List A) :
    (popProg c).Exec s (Function.update s c (s c).tail) 1 := by
  have h := StackProg.Exec.act (fun (_ : K → Option A) k => if k = c then StackAct.pop else .keep) s
  have e : StackProg.applyAct (fun (_ : K → Option A) k => if k = c then StackAct.pop else .keep) s =
      Function.update s c (s c).tail := by
    funext k; by_cases k1 : k = c
    · subst k1; simp [StackProg.applyAct, StackAct.apply]
    · simp [StackProg.applyAct, StackAct.apply, k1]
  rw [e] at h; exact h

end Unary

/-! ## Unary division with remainder flag -/

section Div
variable {K A : Type} [DecidableEq K]

def divAct (Y Q Bd : K) (mk : A) (h : K → Option A) (k : K) : StackAct A :=
  if k = Q then .push mk else if k = Bd then (if (h Y).isSome then .push mk else .keep) else .keep

/-- `Q` gets `⌈r/D⌉` marks, `Bd` one mark iff `D ∤ r` (`R` holds `r`, `Np` holds `D`). -/
def divLoop (R Np Y Q Bd scr : K) (mk : A) : StackProg K A :=
  .loop (fun h => (h R).isSome)
    (.seq (copyProg Np Y scr) (.seq (syncPopProg R Y)
      (.seq (.act (divAct Y Q Bd mk)) (clearProg Y))))

def divPost (R Q Bd : K) (mk : A) (s : K → List A) (r D : ℕ) : K → List A :=
  Function.update (Function.update (Function.update s R []) Q
    (List.replicate ((r + D - 1) / D) mk ++ s Q)) Bd
    (List.replicate (if r % D = 0 then 0 else 1) mk ++ s Bd)

lemma exec_div (R Np Y Q Bd scr : K)
    (hRN : R ≠ Np) (hRY : R ≠ Y) (hRQ : R ≠ Q) (hRB : R ≠ Bd) (hRs : R ≠ scr)
    (hNY : Np ≠ Y) (hNQ : Np ≠ Q) (hNB : Np ≠ Bd) (hNs : Np ≠ scr)
    (hYQ : Y ≠ Q) (hYB : Y ≠ Bd) (hYs : Y ≠ scr) (hQB : Q ≠ Bd) (hQs : Q ≠ scr) (hBs : Bd ≠ scr)
    (mk : A) (D : ℕ) (hD : 1 ≤ D) :
    ∀ (r : ℕ) (s : K → List A), s R = List.replicate r mk → s Np = List.replicate D mk →
      s Y = [] → s scr = [] →
      ∃ n ≤ r * (12 * D + 12) + 1, (divLoop R Np Y Q Bd scr mk).Exec s (divPost R Q Bd mk s r D) n := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro s hR hN hY hs
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨1, by simp, ?_⟩
    have hpost : divPost R Q Bd mk s 0 D = s := by
      have h1 : (0 + D - 1) / D = 0 := Nat.div_eq_of_lt (by omega)
      funext k
      simp only [divPost, h1, Nat.zero_mod, if_true, List.replicate_zero, List.nil_append]
      by_cases k1 : k = Bd
      · subst k1; simp
      by_cases k2 : k = Q
      · subst k2; simp [k1]
      by_cases k3 : k = R
      · subst k3; simp [k1, k2, hR]
      · simp [k1, k2, k3]
    rw [hpost]
    exact StackProg.Exec.loopFalse (by simp [hR])
  · -- one iteration
    obtain ⟨n1, hn1, e1⟩ := exec_copy Np Y scr hNY hNs hYs s hs
    set s1 := Function.update s Y (s Np ++ s Y) with hs1
    set L := min r D with hL
    have hL1 : 1 ≤ L := by omega
    have e2 := exec_syncPop R Y hRY L s1 (by simp [hs1, hRY, hR, hN, hY, hL])
    set s2 := Function.update (Function.update s1 R ((s1 R).drop L)) Y ((s1 Y).drop L) with hs2
    have h2R : s2 R = List.replicate (r - L) mk := by
      simp [hs2, hs1, hRY, hR, List.drop_replicate]
    have h2Y : s2 Y = List.replicate (D - L) mk := by
      simp [hs2, hs1, hN, hY, List.drop_replicate]
    have h2o : ∀ k, k ≠ R → k ≠ Y → s2 k = s k := by
      intro k k1 k2; simp [hs2, hs1, k1, k2]
    have e3 := StackProg.Exec.act (divAct Y Q Bd mk) s2
    set s3 := StackProg.applyAct (divAct Y Q Bd mk) s2 with hs3
    have h3Q : s3 Q = mk :: s Q := by
      simp [hs3, StackProg.applyAct, divAct, StackAct.apply, h2o Q (Ne.symm hRQ) (Ne.symm hYQ)]
    have h3B : s3 Bd = List.replicate (if r < D then 1 else 0) mk ++ s Bd := by
      simp only [hs3, StackProg.applyAct, divAct, if_neg (Ne.symm hQB), if_true, h2Y,
        h2o Bd (Ne.symm hRB) (Ne.symm hYB)]
      by_cases hrD : r < D
      · have : D - L ≠ 0 := by omega
        obtain ⟨j, hj⟩ : ∃ j, D - L = j + 1 := ⟨D - L - 1, by omega⟩
        simp [hrD, hj, List.replicate_succ, StackAct.apply]
      · have : D - L = 0 := by omega
        simp [hrD, this, StackAct.apply]
    have h3o : ∀ k, k ≠ Q → k ≠ Bd → s3 k = s2 k := by
      intro k k1 k2; simp [hs3, StackProg.applyAct, divAct, StackAct.apply, k1, k2]
    obtain ⟨n4, hn4, e4⟩ := exec_transfer Y (fun _ => false) (s3 Y) s3 rfl
    set s4 := transferStore Y (fun _ => false) s3 with hs4
    have h3Y : s3 Y = List.replicate (D - L) mk := by rw [h3o Y hYQ hYB, h2Y]
    have h4R : s4 R = List.replicate (r - L) mk := by
      simp [hs4, transferStore, hRY, h3o R hRQ hRB, h2R]
    have h4N : s4 Np = List.replicate D mk := by
      simp [hs4, transferStore, hNY, h3o Np hNQ hNB, h2o Np hRN.symm hNY, hN]
    have h4Y : s4 Y = [] := by simp [hs4, transferStore]
    have h4s : s4 scr = [] := by
      simp [hs4, transferStore, hYs.symm, h3o scr hQs.symm hBs.symm, h2o scr hRs.symm hYs.symm, hs]
    have hlt : r - L < r := by omega
    obtain ⟨n', hn', e5⟩ := ih (r - L) hlt s4 h4R h4N h4Y h4s
    have hpost : divPost R Q Bd mk s4 (r - L) D = divPost R Q Bd mk s r D := by
      have h4Q : s4 Q = mk :: s Q := by simp [hs4, transferStore, hYQ.symm, h3Q]
      have h4B : s4 Bd = List.replicate (if r < D then 1 else 0) mk ++ s Bd := by
        simp [hs4, transferStore, hYB.symm, h3B]
      have hq : (r - L + D - 1) / D + 1 = (r + D - 1) / D := by
        by_cases hrD : r < D
        · have h0 : r - L = 0 := by omega
          rw [h0, Nat.div_eq_of_lt (by omega : 0 + D - 1 < D)]
          symm; apply Nat.div_eq_of_lt_le <;> omega
        · have h0 : r - L = r - D := by omega
          rw [h0, ← Nat.add_div_right _ (by omega : 0 < D)]
          congr 1; omega
      have hb : (if (r - L) % D = 0 then 0 else 1) + (if r < D then 1 else 0) =
          (if r % D = 0 then 0 else 1) := by
        by_cases hrD : r < D
        · have h0 : r - L = 0 := by omega
          have h1 : r % D = r := Nat.mod_eq_of_lt hrD
          rw [h0, Nat.zero_mod, h1]; simp [hrD]; omega
        · have h0 : r - L = r - D := by omega
          rw [h0, ← Nat.mod_eq_sub_mod (by omega)]
          simp [hrD]
      funext k
      by_cases k1 : k = Bd
      · subst k1
        simp only [divPost, Function.update_self, h4B, ← List.append_assoc,
          List.replicate_append_replicate, hb]
      by_cases k2 : k = Q
      · subst k2
        simp only [divPost, Function.update_self, Function.update_of_ne k1, h4Q]
        rw [← hq, List.replicate_succ', List.append_assoc, List.singleton_append]
      by_cases k3 : k = R
      · subst k3; simp [divPost, k1, k2]
      · simp only [divPost, Function.update_of_ne k1, Function.update_of_ne k2,
          Function.update_of_ne k3]
        by_cases k4 : k = Y
        · subst k4; rw [h4Y, hY]
        · simp [hs4, transferStore, k4, h3o k k2 k1, h2o k k3 k4]
    rw [← hpost]
    refine ⟨1 + (n1 + 1 + ((3 * L + 1) + 1 + (1 + 1 + n4))) + 1 + n', ?_,
      StackProg.Exec.loopTrue (by simp [hR]; omega)
        (StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3 e4))) e5⟩
    rw [h3Y, List.length_replicate] at hn4
    rw [hN, List.length_replicate] at hn1
    have hmul : (r - L) * (12 * D + 12) ≤ (r - 1) * (12 * D + 12) :=
      Nat.mul_le_mul_right _ (by omega)
    have hexp : r * (12 * D + 12) = (r - 1) * (12 * D + 12) + (12 * D + 12) := by
      obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      simp; ring
    rw [hexp]
    generalize (r - 1) * (12 * D + 12) = X at hmul ⊢
    generalize (r - L) * (12 * D + 12) = Y at hmul hn'
    omega

end Div

/-! ## Token-level facts for the digit loops -/

section Tokens

def isDA (o : Option A) : Bool := decide (o = some (ι1 .zero)) || decide (o = some (ι1 .one))
def isOneA (o : Option A) : Bool := decide (o = some (ι1 .one))
def dsymA (b : Bool) : A := ι1 (dg b)

lemma isDA_dsym (b : Bool) : isDA (some (dsymA b)) = true := by cases b <;> rfl
lemma isOneA_dsym (b : Bool) : isOneA (some (dsymA b)) = b := by cases b <;> rfl

/-- the head token of a nonnegative integer: its digits, then the separator. -/
lemma encInts_head_nonneg (z : ℤ) (hz : 0 ≤ z) (c : List ℤ) :
    (encInts (z :: c)).map ι1 =
      (Nat.bits z.natAbs).map dsymA ++ ι1 .sep :: (encInts c).map ι1 := by
  rw [encInts_cons, encInt_split, if_neg (by omega)]
  simp [dsymA, Function.comp_def]

lemma encInts_head_neg (z : ℤ) (hz : z < 0) (c : List ℤ) :
    ((encInts (z :: c)).map ι1).head? = some (ι1 .minus) := by
  rw [encInts_cons, encInt_split, if_pos hz]
  simp

lemma isDA_sep : isDA (some (ι1 .sep)) = false := rfl

lemma head_encInts_nonneg (z : ℤ) (hz : 0 ≤ z) (c : List ℤ) :
    isDA ((encInts (z :: c)).map ι1).head? = decide (z ≠ 0) := by
  rw [encInts_head_nonneg z hz]
  rcases Nat.eq_zero_or_pos z.natAbs with h | h
  · have : z = 0 := by omega
    subst this; simp [isDA_sep]
  · have hb := bits_getLast z.natAbs (by omega)
    obtain ⟨b, l, hbl⟩ : ∃ b l, Nat.bits z.natAbs = b :: l := by
      rcases hh : Nat.bits z.natAbs with _ | ⟨b, l⟩
      · rw [hh] at hb; simp at hb
      · exact ⟨b, l, rfl⟩
    rw [hbl]
    have : z ≠ 0 := by omega
    simp [isDA_dsym, this]

end Tokens


end D0bfL

/-! ## Library part 2 (namespace D0bfT): token skipping and binary comparison -/

namespace D0bfT
open D0bfL

/-! ### binary values, last difference -/

def bval : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (bval l)

lemma bval_cons (b : Bool) (l : List Bool) : bval (b :: l) = 2 * bval l + b.toNat := by
  simp only [bval, Nat.bit_val]

lemma bval_bits (n : ℕ) : bval (Nat.bits n) = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bval]
  | bit b n hn ih => rw [Nat.bits_append_bit _ _ hn]; simp [bval, ih]

/-- the comparison result of the most significant differing position (LSB-first lists). -/
def lastDiff : List Bool → List Bool → Option Bool
  | a :: as, b :: bs => (lastDiff as bs).elim (if a = b then none else some b) some
  | _, _ => none

lemma lastDiff_eq : ∀ (as bs : List Bool), as.length = bs.length →
    lastDiff as bs = (if bval as < bval bs then some true
      else if bval bs < bval as then some false else none) := by
  intro as
  induction as with
  | nil =>
    intro bs h
    rcases bs with _ | ⟨b, bs⟩
    · simp [lastDiff, bval]
    · simp at h
  | cons a as ih =>
    intro bs h
    rcases bs with _ | ⟨b, bs⟩
    · simp at h
    simp only [lastDiff, bval_cons]
    rw [ih bs (by simpa using h)]
    have ha : a.toNat ≤ 1 := by cases a <;> decide
    have hb : b.toNat ≤ 1 := by cases b <;> decide
    by_cases h1 : bval as < bval bs
    · have h3 : 2 * bval as + a.toNat < 2 * bval bs + b.toNat := by omega
      simp [h1, h3]
    · by_cases h2 : bval bs < bval as
      · have h3 : ¬ 2 * bval as + a.toNat < 2 * bval bs + b.toNat := by omega
        have h4 : 2 * bval bs + b.toNat < 2 * bval as + a.toNat := by omega
        simp [h1, h2, h3, h4]
      · have e : bval as = bval bs := by omega
        rw [if_neg h1, if_neg h2, e]
        cases a <;> cases b <;> simp

lemma lt_of_bits_len {a b : ℕ} (h : (Nat.bits a).length < (Nat.bits b).length) : a < b := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len] at h
  calc a < 2 ^ Nat.size a := Nat.lt_size_self a
    _ ≤ 2 ^ (Nat.size b - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ b := Nat.lt_size.1 (by omega)

/-! ### token lists -/

/-- a list of sep-free tokens, each followed by the separator, embedded by `e`. -/
def toksE (e : BSym → A) (ts : List (List BSym)) : List A :=
  (ts.map (fun t => t.map e ++ [e .sep])).flatten

lemma toksE_nil (e : BSym → A) : toksE e [] = [] := rfl

lemma toksE_cons (e : BSym → A) (t : List BSym) (ts : List (List BSym)) :
    toksE e (t :: ts) = t.map e ++ e .sep :: toksE e ts := by
  simp [toksE]

/-- the digit token of a natural number. -/
def tokN (k : ℕ) : List BSym := (Nat.bits k).map dg

lemma tokN_no_sep (k : ℕ) : BSym.sep ∉ tokN k := fun h => digits_no_sep k _ h rfl

lemma encNats_toks (e : BSym → A) : ∀ d : List ℕ, (encNats d).map e = toksE e (d.map tokN) := by
  intro d
  induction d with
  | nil => rfl
  | cons k d ih => rw [encNats_cons, encNat_dg, List.map_cons, toksE_cons, ← ih]; simp [tokN]

/-! ### skipping tokens -/

section Skip
variable {K : Type} [DecidableEq K]

def skipOne (W : K) (e : BSym → A) : StackProg K A :=
  .seq (.loop (fun h => (h W).isSome && !decide (h W = some (e .sep))) (popProg W)) (popProg W)

lemma exec_skipOne (W : K) (e : BSym → A) (he : Function.Injective e) (rest : List A) :
    ∀ (tok : List BSym) (s : K → List A), BSym.sep ∉ tok →
      s W = tok.map e ++ e .sep :: rest →
      ∃ n ≤ 3 * tok.length + 3, (skipOne W e).Exec s (Function.update s W rest) n := by
  have hl : ∀ (tok : List BSym) (s : K → List A), BSym.sep ∉ tok →
      s W = tok.map e ++ e .sep :: rest →
      (StackProg.loop (fun h => (h W).isSome && !decide (h W = some (e .sep))) (popProg W)).Exec s
        (Function.update s W (e .sep :: rest)) (3 * tok.length + 1) := by
    intro tok
    induction tok with
    | nil =>
      intro s _ hs
      have : Function.update s W (e .sep :: rest) = s := by
        funext k; by_cases hk : k = W
        · subst hk; simp [hs]
        · simp [hk]
      rw [this]
      exact StackProg.Exec.loopFalse (by simp [hs])
    | cons b tok ih =>
      intro s hsep hs
      have hb : b ≠ BSym.sep := fun h => hsep (h ▸ List.mem_cons_self)
      have e1 := exec_pop W s
      have e2 := ih (Function.update s W (s W).tail) (fun h => hsep (List.mem_cons_of_mem _ h))
        (by simp [hs])
      have hu : Function.update (Function.update s W (s W).tail) W (e .sep :: rest) =
          Function.update s W (e .sep :: rest) := by simp
      rw [hu] at e2
      have hne : e b ≠ e .sep := fun h => hb (he h)
      have e3 := StackProg.Exec.loopTrue
        (test := fun h => (h W).isSome && !decide (h W = some (e .sep)))
        (by simp [hs, hne]) e1 e2
      simp only [List.length_cons]
      have e : 3 * (tok.length + 1) + 1 = 1 + 1 + 1 + (3 * tok.length + 1) := by ring
      rw [e]; exact e3
  intro tok s hsep hs
  have e1 := hl tok s hsep hs
  have e2 := exec_pop W (Function.update s W (e .sep :: rest))
  have hu : Function.update (Function.update s W (e .sep :: rest)) W
      ((Function.update s W (e .sep :: rest)) W).tail = Function.update s W rest := by simp
  rw [hu] at e2
  exact ⟨_, by omega, StackProg.Exec.seq e1 e2⟩

def skipToks (cnt W : K) (e : BSym → A) : StackProg K A :=
  .loop (fun h => (h cnt).isSome) (.seq (popProg cnt) (skipOne W e))

lemma exec_skipToks (cnt W : K) (hcW : cnt ≠ W) (e : BSym → A) (he : Function.Injective e)
    (mk : A) (rest : List A) :
    ∀ (k : ℕ) (ts : List (List BSym)) (s : K → List A),
      (∀ t ∈ ts, BSym.sep ∉ t) → k ≤ ts.length →
      s cnt = List.replicate k mk → s W = toksE e ts ++ rest →
      ∃ n ≤ 7 * (s W).length + 1, (skipToks cnt W e).Exec s
        (Function.update (Function.update s cnt []) W (toksE e (ts.drop k) ++ rest)) n := by
  intro k
  induction k with
  | zero =>
    intro ts s _ _ hc hW
    refine ⟨1, by omega, ?_⟩
    have : Function.update (Function.update s cnt []) W (toksE e (ts.drop 0) ++ rest) = s := by
      funext j
      by_cases h1 : j = W
      · subst h1; simp [hW]
      · by_cases h2 : j = cnt
        · subst h2; simp [hc, h1]
        · simp [h1, h2]
    rw [this]
    exact StackProg.Exec.loopFalse (by simp [hc])
  | succ k ih =>
    intro ts s hts hk hc hW
    rcases ts with _ | ⟨t, ts⟩
    · simp at hk
    have ht : BSym.sep ∉ t := hts t List.mem_cons_self
    have e1 := exec_pop cnt s
    set s1 := Function.update s cnt (s cnt).tail with hs1
    have hs1W : s1 W = t.map e ++ e .sep :: (toksE e ts ++ rest) := by
      simp [hs1, Ne.symm hcW, hW, toksE_cons]
    obtain ⟨n2, hn2, e2⟩ := exec_skipOne W e he (toksE e ts ++ rest) t s1 ht hs1W
    set s2 := Function.update s1 W (toksE e ts ++ rest) with hs2
    obtain ⟨n3, hn3, e3⟩ := ih ts s2 (fun t' h' => hts t' (List.mem_cons_of_mem _ h'))
      (by simp at hk; omega) (by simp [hs2, hs1, hcW, hc]) (by simp [hs2])
    have hpost : Function.update (Function.update s2 cnt []) W (toksE e (ts.drop k) ++ rest) =
        Function.update (Function.update s cnt []) W (toksE e ((t :: ts).drop (k + 1)) ++ rest) := by
      funext j
      by_cases h1 : j = W
      · subst h1; simp
      · by_cases h2 : j = cnt
        · subst h2; simp [h1]
        · simp [hs2, hs1, h1, h2]
    rw [hpost] at e3
    refine ⟨1 + (1 + 1 + n2) + 1 + n3, ?_, StackProg.Exec.loopTrue (by simp [hc])
      (StackProg.Exec.seq e1 e2) e3⟩
    have hl : (s W).length = t.length + 1 + (s2 W).length := by
      simp [hs2, hW, toksE_cons]; omega
    rw [hl]; omega

end Skip

/-! ### comparing two natural-number tokens -/

section Cmp
variable {K : Type} [DecidableEq K]

def isDig (e : BSym → A) (o : Option A) : Bool :=
  decide (o = some (e .zero)) || decide (o = some (e .one))

def stSym (b : Bool) : A := if b then ι1 .one else ι1 .zero

end Cmp

/-! ### generic counted loop, skipping a possibly missing token -/

section For
variable {K : Type} [DecidableEq K]

/-- a loop whose body pops the counter `C` once per round, specified by an invariant. -/
lemma exec_for (C : K) (body : StackProg K A) (mk : A) (Inv : ℕ → (K → List A) → Prop) (n T : ℕ)
    (hbody : ∀ k < n, ∀ s, Inv k s → s C = List.replicate (n - k) mk →
      ∃ s' t, t ≤ T ∧ body.Exec s s' t ∧ Inv (k + 1) s' ∧
        s' C = List.replicate (n - k - 1) mk) :
    ∀ s, Inv 0 s → s C = List.replicate n mk →
      ∃ s' t, t ≤ n * (T + 2) + 1 ∧
        (StackProg.loop (fun h => (h C).isSome) body).Exec s s' t ∧ Inv n s' := by
  have key : ∀ r, r ≤ n → ∀ s, Inv (n - r) s → s C = List.replicate r mk →
      ∃ s' t, t ≤ r * (T + 2) + 1 ∧
        (StackProg.loop (fun h => (h C).isSome) body).Exec s s' t ∧ Inv n s' := by
    intro r
    induction r with
    | zero =>
      intro _ s hI hC
      exact ⟨s, 1, by omega, StackProg.Exec.loopFalse (by simp [hC]), by simpa using hI⟩
    | succ r ih =>
      intro hr s hI hC
      obtain ⟨s1, t1, ht1, e1, hI1, hC1⟩ :=
        hbody (n - (r + 1)) (by omega) s hI (by rw [hC]; congr 1; omega)
      have hk : n - (r + 1) + 1 = n - r := by omega
      rw [hk] at hI1
      obtain ⟨s2, t2, ht2, e2, hI2⟩ := ih (by omega) s1 hI1 (by rw [hC1]; congr 1; omega)
      refine ⟨s2, 1 + t1 + 1 + t2, ?_, StackProg.Exec.loopTrue (by simp [hC]) e1 e2, hI2⟩
      have : (r + 1) * (T + 2) = r * (T + 2) + T + 2 := by ring
      omega
  intro s hI hC
  exact key n le_rfl s (by simpa using hI) hC

lemma exec_skipOne' (W : K) (e : BSym → A) (he : Function.Injective e) :
    ∀ (ts : List (List BSym)) (s : K → List A), (∀ t ∈ ts, BSym.sep ∉ t) →
      s W = toksE e ts →
      ∃ n ≤ 3 * (s W).length + 3, (skipOne W e).Exec s (Function.update s W (toksE e ts.tail)) n := by
  intro ts s hts hW
  rcases ts with _ | ⟨t, ts⟩
  · have e1 : (StackProg.loop (fun h => (h W).isSome && !decide (h W = some (e .sep)))
        (popProg W)).Exec s s 1 := StackProg.Exec.loopFalse (by simp [hW, toksE_nil])
    have e2 := exec_pop W s
    rw [hW, toksE_nil] at e2
    exact ⟨1 + 1 + 1, by omega, StackProg.Exec.seq e1 e2⟩
  · obtain ⟨n, hn, h⟩ := exec_skipOne W e he (toksE e ts) t s (hts t List.mem_cons_self)
      (by rw [hW, toksE_cons])
    refine ⟨n, ?_, h⟩
    rw [hW, toksE_cons]; simp; omega

end For

/-! ### generic one-step helpers and the "token = 1" reader -/

section Gen
variable {K : Type} [DecidableEq K]

lemma ι1_inj : Function.Injective ι1 := fun a b h => by simpa [ι1] using h
lemma ι2_inj : Function.Injective ι2 := fun a b h => by simpa [ι2] using h

lemma exec_congrG {p : StackProg K A} {s t t' : K → List A} {n : ℕ} (h : p.Exec s t n)
    (e : t = t') : p.Exec s t' n := e ▸ h

def skipP : StackProg K A := .act (fun _ _ => .keep)

lemma exec_skipP (s : K → List A) : (skipP : StackProg K A).Exec s s 1 := by
  unfold skipP
  refine exec_congrG (StackProg.Exec.act _ s) ?_
  funext k; simp [StackProg.applyAct, StackAct.apply]

def flagP (B : K) (t : (K → Option A) → Bool) : StackProg K A :=
  .act (fun h k => if k = B ∧ t h = true then .push mkA else .keep)

lemma exec_flagP (B : K) (t : (K → Option A) → Bool) (s : K → List A) :
    (flagP B t).Exec s (Function.update s B
      (if t (fun k => (s k).head?) = true then mkA :: s B else s B)) 1 := by
  unfold flagP
  refine exec_congrG (StackProg.Exec.act _ s) ?_
  funext k
  by_cases hk : k = B
  · subst hk
    by_cases ht : t (fun k => (s k).head?) = true <;> simp [StackProg.applyAct, StackAct.apply, ht]
  · simp [StackProg.applyAct, StackAct.apply, hk]

lemma exec_pushG (c : K) (a : A) (s : K → List A) :
    (pushProg c a).Exec s (Function.update s c (a :: s c)) 1 := by
  unfold pushProg
  refine exec_congrG (StackProg.Exec.act _ s) ?_
  funext k; by_cases k1 : k = c
  · subst k1; simp [StackProg.applyAct, StackAct.apply]
  · simp [StackProg.applyAct, StackAct.apply, k1]

lemma exec_clearG (c : K) (s : K → List A) :
    ∃ n ≤ 3 * (s c).length + 1, (clearProg c).Exec s (Function.update s c []) n := by
  obtain ⟨n, hn, h⟩ := exec_transfer c (fun _ => false) (s c) s rfl
  refine ⟨n, hn, exec_congrG h ?_⟩
  funext k; by_cases k1 : k = c
  · subst k1; simp [transferStore]
  · simp [transferStore, k1]

end Gen

end D0bfT

/-! ## Library part 3 (namespace D0bfS): streaming comparison of two sums of binary numbers -/

namespace D0bfS
open D0bfL D0bfT

/-- a digit symbol of either part. -/
def digA (o : Option A) : Bool :=
  decide (o = some (ι1 .zero)) || decide (o = some (ι1 .one)) ||
  decide (o = some (ι2 .zero)) || decide (o = some (ι2 .one))

def oneA (o : Option A) : Bool := decide (o = some (ι1 .one)) || decide (o = some (ι2 .one))

/-- value of a digit list (least significant digit first). -/
def dval (l : List A) : ℕ := bval (l.map (fun a => oneA (some a)))

/-- the lowest digit of a digit list (0 when empty). -/
def dtop : List A → ℕ
  | [] => 0
  | a :: _ => (oneA (some a)).toNat

lemma dval_split (l : List A) : dval l = dtop l + 2 * dval l.tail := by
  cases l with
  | nil => simp [dval, dtop, bval]
  | cons a l => simp only [dval, dtop, List.map_cons, bval_cons, List.tail_cons]; ring

def cv (o : Option A) : ℕ := if o.isSome then 1 else 0
def dvo (o : Option A) : ℕ := if oneA o then 1 else 0

lemma oneA_of_not_dig {o : Option A} (h : digA o = false) : oneA o = false := by
  simp only [digA, oneA, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h ⊢
  tauto

lemma dvo_head (l r : List A) (hr : digA r.head? = false) : dvo (l ++ r).head? = dtop l := by
  cases l with
  | nil => simp [dvo, dtop, oneA_of_not_dig hr]
  | cons a l =>
    simp only [dvo, dtop, List.cons_append, List.head?_cons]
    rcases Bool.eq_false_or_eq_true (oneA (some a)) with h | h <;> simp [h]

lemma dig_head (l r : List A) (hl : ∀ a ∈ l, digA (some a) = true) (hr : digA r.head? = false) :
    digA (l ++ r).head? = !l.isEmpty := by
  cases l with
  | nil => simpa using hr
  | cons a l => simpa using hl a List.mem_cons_self

lemma tail_pop (l r : List A) (hl : ∀ a ∈ l, digA (some a) = true) (hr : digA r.head? = false) :
    (if digA (l ++ r).head? = true then StackAct.pop else StackAct.keep).apply (l ++ r) =
      l.tail ++ r := by
  rw [dig_head l r hl hr]
  cases l with
  | nil => simp [StackAct.apply]
  | cons a l => simp [StackAct.apply]

/-- the comparison result as the top of the state stack. -/
def scRes (X Y : ℕ) (o : Option A) : Option A :=
  if X < Y then some (stSym true) else if Y < X then some (stSym false) else o

lemma scRes_step (X Y b1 b2 : ℕ) (hb1 : b1 < 2) (hb2 : b2 < 2) (o : Option A) :
    scRes (b1 + 2 * X) (b2 + 2 * Y) o =
      scRes X Y (if b1 % 2 = b2 % 2 then o else some (stSym (decide (b2 % 2 = 1)))) := by
  unfold scRes
  interval_cases b1 <;> interval_cases b2 <;> simp <;> split_ifs <;> first | rfl | omega

section Sum
variable {K : Type} [DecidableEq K]

def sumAct (X1 X2 Y1 Y2 C1 C2 St : K) (mk : A) (h : K → Option A) (k : K) : StackAct A :=
  if k = X1 ∨ k = X2 ∨ k = Y1 ∨ k = Y2 then (if digA (h k) then .pop else .keep)
  else if k = C1 then
    (if 2 ≤ dvo (h X1) + dvo (h X2) + cv (h C1) then (if (h C1).isSome then .keep else .push mk)
      else (if (h C1).isSome then .pop else .keep))
  else if k = C2 then
    (if 2 ≤ dvo (h Y1) + dvo (h Y2) + cv (h C2) then (if (h C2).isSome then .keep else .push mk)
      else (if (h C2).isSome then .pop else .keep))
  else if k = St then
    (if (dvo (h X1) + dvo (h X2) + cv (h C1)) % 2 = (dvo (h Y1) + dvo (h Y2) + cv (h C2)) % 2
      then .keep
      else .push (stSym (decide ((dvo (h Y1) + dvo (h Y2) + cv (h C2)) % 2 = 1))))
  else .keep

def sumTest (X1 X2 Y1 Y2 C1 C2 : K) (h : K → Option A) : Bool :=
  digA (h X1) || digA (h X2) || digA (h Y1) || digA (h Y2) || (h C1).isSome || (h C2).isSome

def sumLoop (X1 X2 Y1 Y2 C1 C2 St : K) (mk : A) : StackProg K A :=
  .loop (sumTest X1 X2 Y1 Y2 C1 C2) (.act (sumAct X1 X2 Y1 Y2 C1 C2 St mk))

def cst (mk : A) (b : Bool) : List A := if b then [mk] else []

lemma cv_cst (mk : A) (b : Bool) : cv (cst mk b).head? = b.toNat := by cases b <;> rfl

lemma carry_act (mk : A) (c : Bool) (v : ℕ) :
    (if 2 ≤ v + cv (cst mk c).head? then
        (if ((cst mk c).head?).isSome then StackAct.keep else .push mk)
      else (if ((cst mk c).head?).isSome then .pop else .keep)).apply (cst mk c) =
      cst mk (decide (2 ≤ v + c.toNat)) := by
  cases c <;> by_cases h : 2 ≤ v <;> by_cases h1 : 2 ≤ v + 1 <;>
    simp [cst, cv, StackAct.apply, h, h1]

/-- the state after one round of the sum-compare loop. -/
def sumNext (X1 X2 Y1 Y2 C1 C2 St : K) (mk : A) (s : K → List A) (l1 l2 l3 l4 r1 r2 r3 r4 : List A)
    (c1 c2 : Bool) : K → List A :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update s X1 (l1.tail ++ r1)) X2 (l2.tail ++ r2)) Y1
    (l3.tail ++ r3)) Y2 (l4.tail ++ r4)) C1 (cst mk (decide (2 ≤ dtop l1 + dtop l2 + c1.toNat))))
    C2 (cst mk (decide (2 ≤ dtop l3 + dtop l4 + c2.toNat)))) St
    ((if (dtop l1 + dtop l2 + c1.toNat) % 2 = (dtop l3 + dtop l4 + c2.toNat) % 2 then []
      else [stSym (decide ((dtop l3 + dtop l4 + c2.toNat) % 2 = 1))]) ++ s St)

set_option maxHeartbeats 2000000 in
lemma sum_act_eq (X1 X2 Y1 Y2 C1 C2 St : K)
    (h12 : X1 ≠ X2) (h13 : X1 ≠ Y1) (h14 : X1 ≠ Y2) (h15 : X1 ≠ C1) (h16 : X1 ≠ C2) (h17 : X1 ≠ St)
    (h23 : X2 ≠ Y1) (h24 : X2 ≠ Y2) (h25 : X2 ≠ C1) (h26 : X2 ≠ C2) (h27 : X2 ≠ St)
    (h34 : Y1 ≠ Y2) (h35 : Y1 ≠ C1) (h36 : Y1 ≠ C2) (h37 : Y1 ≠ St)
    (h45 : Y2 ≠ C1) (h46 : Y2 ≠ C2) (h47 : Y2 ≠ St)
    (h56 : C1 ≠ C2) (h57 : C1 ≠ St) (h67 : C2 ≠ St)
    (mk : A) (r1 r2 r3 r4 : List A)
    (hr1 : digA r1.head? = false) (hr2 : digA r2.head? = false)
    (hr3 : digA r3.head? = false) (hr4 : digA r4.head? = false)
    (l1 l2 l3 l4 : List A) (c1 c2 : Bool) (s : K → List A)
    (hl1 : ∀ a ∈ l1, digA (some a) = true) (hl2 : ∀ a ∈ l2, digA (some a) = true)
    (hl3 : ∀ a ∈ l3, digA (some a) = true) (hl4 : ∀ a ∈ l4, digA (some a) = true)
    (hX1 : s X1 = l1 ++ r1) (hX2 : s X2 = l2 ++ r2) (hY1 : s Y1 = l3 ++ r3) (hY2 : s Y2 = l4 ++ r4)
    (hC1 : s C1 = cst mk c1) (hC2 : s C2 = cst mk c2) :
    StackProg.applyAct (sumAct X1 X2 Y1 Y2 C1 C2 St mk) s =
      sumNext X1 X2 Y1 Y2 C1 C2 St mk s l1 l2 l3 l4 r1 r2 r3 r4 c1 c2 := by
  have t1 : dvo (s X1).head? = dtop l1 := by rw [hX1]; exact dvo_head l1 r1 hr1
  have t2 : dvo (s X2).head? = dtop l2 := by rw [hX2]; exact dvo_head l2 r2 hr2
  have t3 : dvo (s Y1).head? = dtop l3 := by rw [hY1]; exact dvo_head l3 r3 hr3
  have t4 : dvo (s Y2).head? = dtop l4 := by rw [hY2]; exact dvo_head l4 r4 hr4
  have t5 : cv (s C1).head? = c1.toNat := by rw [hC1]; exact cv_cst mk c1
  have t6 : cv (s C2).head? = c2.toNat := by rw [hC2]; exact cv_cst mk c2
  funext k
  simp only [StackProg.applyAct, sumNext]
  by_cases k1 : k = X1
  · rw [k1]; simp only [sumAct, true_or, if_true]
    simp only [hX1]; rw [tail_pop l1 r1 hl1 hr1]; rw [Function.update_of_ne h17, Function.update_of_ne h16, Function.update_of_ne h15, Function.update_of_ne h14, Function.update_of_ne h13, Function.update_of_ne h12, Function.update_self]
  by_cases k2 : k = X2
  · rw [k2]; simp only [sumAct, true_or, or_true, if_true]
    simp only [hX2]; rw [tail_pop l2 r2 hl2 hr2]; rw [Function.update_of_ne h27, Function.update_of_ne h26, Function.update_of_ne h25, Function.update_of_ne h24, Function.update_of_ne h23, Function.update_self]
  by_cases k3 : k = Y1
  · rw [k3]; simp only [sumAct, true_or, or_true, if_true]
    simp only [hY1]; rw [tail_pop l3 r3 hl3 hr3]; rw [Function.update_of_ne h37, Function.update_of_ne h36, Function.update_of_ne h35, Function.update_of_ne h34, Function.update_self]
  by_cases k4 : k = Y2
  · rw [k4]; simp only [sumAct, true_or, or_true, if_true]
    simp only [hY2]; rw [tail_pop l4 r4 hl4 hr4]; rw [Function.update_of_ne h47, Function.update_of_ne h46, Function.update_of_ne h45, Function.update_self]
  by_cases k5 : k = C1
  · rw [k5]
    simp only [sumAct, Ne.symm h15, Ne.symm h25, Ne.symm h35, Ne.symm h45, or_self, if_false,
      if_true]
    simp only [t1, t2, hC1]; rw [carry_act, Function.update_of_ne h57, Function.update_of_ne h56, Function.update_self]
  by_cases k6 : k = C2
  · rw [k6]
    simp only [sumAct, Ne.symm h16, Ne.symm h26, Ne.symm h36, Ne.symm h46, Ne.symm h56, or_self,
      if_false, if_true]
    simp only [t3, t4, hC2]; rw [carry_act, Function.update_of_ne h67, Function.update_self]
  by_cases k7 : k = St
  · rw [k7]
    simp only [sumAct, Ne.symm h17, Ne.symm h27, Ne.symm h37, Ne.symm h47, Ne.symm h57,
      Ne.symm h67, or_self, if_false, if_true]
    simp only [t1, t2, t3, t4, t5, t6, Function.update_self]
    split_ifs <;> simp [StackAct.apply]
  · simp [sumAct, k1, k2, k3, k4, k5, k6, k7, Function.update_apply, StackAct.apply]

set_option maxHeartbeats 2000000 in
lemma upd7_congr (X1 X2 Y1 Y2 C1 C2 St : K) (s s' : K → List A) (v1 v2 v3 v4 v5 v6 v7 w7 : List A)
    (h : ∀ k, k ≠ X1 → k ≠ X2 → k ≠ Y1 → k ≠ Y2 → k ≠ C1 → k ≠ C2 → k ≠ St → s k = s' k)
    (h7 : v7 = w7) :
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update s X1 v1) X2 v2) Y1 v3) Y2 v4) C1 v5) C2 v6) St v7 =
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update s' X1 v1) X2 v2) Y1 v3) Y2 v4) C1 v5) C2 v6) St w7 := by
  subst h7
  funext k
  by_cases k7 : k = St; · subst k7; simp
  by_cases k6 : k = C2; · subst k6; simp [k7]
  by_cases k5 : k = C1; · subst k5; simp [k7, k6]
  by_cases k4 : k = Y2; · subst k4; simp [k7, k6, k5]
  by_cases k3 : k = Y1; · subst k3; simp [k7, k6, k5, k4]
  by_cases k2 : k = X2; · subst k2; simp [k7, k6, k5, k4, k3]
  by_cases k1 : k = X1; · subst k1; simp [k7, k6, k5, k4, k3, k2]
  simp [Function.update_apply, k1, k2, k3, k4, k5, k6, k7, h k k1 k2 k3 k4 k5 k6 k7]

lemma dtop_le (l : List A) : dtop l ≤ 1 := by
  cases l with
  | nil => simp [dtop]
  | cons a l =>
    simp only [dtop]
    rcases Bool.eq_false_or_eq_true (oneA (some a)) with h | h <;> simp [h]

lemma val_step (l1 l2 : List A) (c : Bool) :
    dval l1 + dval l2 + c.toNat = (dtop l1 + dtop l2 + c.toNat) % 2 +
      2 * (dval l1.tail + dval l2.tail + (decide (2 ≤ dtop l1 + dtop l2 + c.toNat)).toNat) := by
  rw [dval_split l1, dval_split l2]
  have := dtop_le l1
  have := dtop_le l2
  have : c.toNat ≤ 1 := by cases c <;> simp
  by_cases h2 : 2 ≤ dtop l1 + dtop l2 + c.toNat <;> simp [h2] <;> omega

lemma fuel_step (l1 l2 l3 l4 : List A) (c1 c2 : Bool) (m : ℕ)
    (hn : max (max l1.length l2.length) (max l3.length l4.length) + 1 ≤ m + 1 ∨
      (l1 = [] ∧ l2 = [] ∧ l3 = [] ∧ l4 = [] ∧ c1 = false ∧ c2 = false))
    (hstop : ¬(l1 = [] ∧ l2 = [] ∧ l3 = [] ∧ l4 = [] ∧ c1 = false ∧ c2 = false)) :
    max (max l1.tail.length l2.tail.length) (max l3.tail.length l4.tail.length) + 1 ≤ m ∨
      (l1.tail = [] ∧ l2.tail = [] ∧ l3.tail = [] ∧ l4.tail = [] ∧
        decide (2 ≤ dtop l1 + dtop l2 + c1.toNat) = false ∧
        decide (2 ≤ dtop l3 + dtop l4 + c2.toNat) = false) := by
  rcases hn with hn | hn
  · by_cases hall : l1 = [] ∧ l2 = [] ∧ l3 = [] ∧ l4 = []
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := hall
      right
      simp only [List.tail_nil, true_and, dtop, zero_add, decide_eq_false_iff_not]
      constructor <;> cases c1 <;> cases c2 <;> simp
    · left
      simp only [List.length_tail]
      have : 1 ≤ max (max l1.length l2.length) (max l3.length l4.length) := by
        by_contra hc
        apply hall
        simp only [not_le, Nat.lt_one_iff, Nat.max_eq_zero_iff, List.length_eq_zero_iff] at hc
        exact ⟨hc.1.1, hc.1.2, hc.2.1, hc.2.2⟩
      omega
  · exact absurd hn hstop

lemma sum_test_true (l1 l2 l3 l4 : List A) (c1 c2 : Bool) (mk : A)
    (h : ¬(l1 = [] ∧ l2 = [] ∧ l3 = [] ∧ l4 = [] ∧ c1 = false ∧ c2 = false)) :
    (!l1.isEmpty || !l2.isEmpty || !l3.isEmpty || !l4.isEmpty || ((cst mk c1).head?).isSome ||
      ((cst mk c2).head?).isSome) = true := by
  cases l1 <;> cases l2 <;> cases l3 <;> cases l4 <;> cases c1 <;> cases c2 <;> simp_all [cst]

set_option maxHeartbeats 2000000 in
lemma exec_sum (X1 X2 Y1 Y2 C1 C2 St : K)
    (h12 : X1 ≠ X2) (h13 : X1 ≠ Y1) (h14 : X1 ≠ Y2) (h15 : X1 ≠ C1) (h16 : X1 ≠ C2) (h17 : X1 ≠ St)
    (h23 : X2 ≠ Y1) (h24 : X2 ≠ Y2) (h25 : X2 ≠ C1) (h26 : X2 ≠ C2) (h27 : X2 ≠ St)
    (h34 : Y1 ≠ Y2) (h35 : Y1 ≠ C1) (h36 : Y1 ≠ C2) (h37 : Y1 ≠ St)
    (h45 : Y2 ≠ C1) (h46 : Y2 ≠ C2) (h47 : Y2 ≠ St)
    (h56 : C1 ≠ C2) (h57 : C1 ≠ St) (h67 : C2 ≠ St)
    (mk : A) (r1 r2 r3 r4 : List A)
    (hr1 : digA r1.head? = false) (hr2 : digA r2.head? = false)
    (hr3 : digA r3.head? = false) (hr4 : digA r4.head? = false) :
    ∀ (n : ℕ) (l1 l2 l3 l4 : List A) (c1 c2 : Bool) (s : K → List A),
      (∀ a ∈ l1, digA (some a) = true) → (∀ a ∈ l2, digA (some a) = true) →
      (∀ a ∈ l3, digA (some a) = true) → (∀ a ∈ l4, digA (some a) = true) →
      s X1 = l1 ++ r1 → s X2 = l2 ++ r2 → s Y1 = l3 ++ r3 → s Y2 = l4 ++ r4 →
      s C1 = cst mk c1 → s C2 = cst mk c2 →
      (max (max l1.length l2.length) (max l3.length l4.length) + 1 ≤ n ∨
        (l1 = [] ∧ l2 = [] ∧ l3 = [] ∧ l4 = [] ∧ c1 = false ∧ c2 = false)) →
      ∃ P t, t ≤ 3 * n + 1 ∧ P.length ≤ n ∧
        (sumLoop X1 X2 Y1 Y2 C1 C2 St mk).Exec s
          (Function.update (Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update s X1 r1) X2 r2) Y1 r3) Y2 r4) C1 []) C2 [])
            St (P ++ s St)) t ∧
        (P ++ s St).head? = scRes (dval l1 + dval l2 + c1.toNat) (dval l3 + dval l4 + c2.toNat)
          (s St).head? := by
  have hstopcase : ∀ (n : ℕ) (s : K → List A), s X1 = [] ++ r1 → s X2 = [] ++ r2 →
      s Y1 = [] ++ r3 → s Y2 = [] ++ r4 → s C1 = cst mk false → s C2 = cst mk false →
      ∃ P t, t ≤ 3 * n + 1 ∧ P.length ≤ n ∧
        (sumLoop X1 X2 Y1 Y2 C1 C2 St mk).Exec s
          (Function.update (Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update s X1 r1) X2 r2) Y1 r3) Y2 r4) C1 []) C2 [])
            St (P ++ s St)) t ∧
        (P ++ s St).head? = scRes (dval [] + dval [] + (false).toNat)
          (dval [] + dval [] + (false).toNat) (s St).head? := by
    intro n s hX1 hX2 hY1 hY2 hC1 hC2
    refine ⟨[], 1, by omega, by simp, ?_, by simp [scRes, dval, bval]⟩
    have hs : Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update s X1 r1) X2 r2) Y1 r3) Y2 r4) C1 []) C2 [])
        St ([] ++ s St) = s := by
      simp only [List.nil_append] at hX1 hX2 hY1 hY2
      funext k
      by_cases k7 : k = St; · subst k7; simp
      by_cases k6 : k = C2; · subst k6; simp [k7, hC2, cst]
      by_cases k5 : k = C1; · subst k5; simp [k7, k6, hC1, cst]
      by_cases k4 : k = Y2; · subst k4; simp [k7, k6, k5, hY2]
      by_cases k3 : k = Y1; · subst k3; simp [k7, k6, k5, k4, hY1]
      by_cases k2 : k = X2; · subst k2; simp [k7, k6, k5, k4, k3, hX2]
      by_cases k1 : k = X1; · subst k1; simp [k7, k6, k5, k4, k3, k2, hX1]
      simp [Function.update_apply, k1, k2, k3, k4, k5, k6, k7]
    rw [hs]
    refine StackProg.Exec.loopFalse ?_
    simp [sumTest, hX1, hX2, hY1, hY2, hC1, hC2, cst, hr1, hr2, hr3, hr4]
  intro n
  induction n with
  | zero =>
    intro l1 l2 l3 l4 c1 c2 s hl1 hl2 hl3 hl4 hX1 hX2 hY1 hY2 hC1 hC2 hn
    rcases hn with hn | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · omega
    exact hstopcase 0 s hX1 hX2 hY1 hY2 hC1 hC2
  | succ m ih =>
    intro l1 l2 l3 l4 c1 c2 s hl1 hl2 hl3 hl4 hX1 hX2 hY1 hY2 hC1 hC2 hn
    by_cases hstop : l1 = [] ∧ l2 = [] ∧ l3 = [] ∧ l4 = [] ∧ c1 = false ∧ c2 = false
    · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hstop
      exact hstopcase (m + 1) s hX1 hX2 hY1 hY2 hC1 hC2
    have hact := sum_act_eq X1 X2 Y1 Y2 C1 C2 St h12 h13 h14 h15 h16 h17 h23 h24 h25 h26 h27
      h34 h35 h36 h37 h45 h46 h47 h56 h57 h67 mk r1 r2 r3 r4 hr1 hr2 hr3 hr4 l1 l2 l3 l4 c1 c2 s
      hl1 hl2 hl3 hl4 hX1 hX2 hY1 hY2 hC1 hC2
    set s' := sumNext X1 X2 Y1 Y2 C1 C2 St mk s l1 l2 l3 l4 r1 r2 r3 r4 c1 c2 with hs'
    obtain ⟨P, t, ht, hP, he, hhead⟩ := ih l1.tail l2.tail l3.tail l4.tail
      (decide (2 ≤ dtop l1 + dtop l2 + c1.toNat)) (decide (2 ≤ dtop l3 + dtop l4 + c2.toNat)) s'
      (fun a ha => hl1 a (List.mem_of_mem_tail ha))
      (fun a ha => hl2 a (List.mem_of_mem_tail ha)) (fun a ha => hl3 a (List.mem_of_mem_tail ha))
      (fun a ha => hl4 a (List.mem_of_mem_tail ha))
      (by simp only [hs', sumNext]; rw [Function.update_of_ne h17, Function.update_of_ne h16, Function.update_of_ne h15, Function.update_of_ne h14, Function.update_of_ne h13, Function.update_of_ne h12, Function.update_self])
      (by simp only [hs', sumNext]; rw [Function.update_of_ne h27, Function.update_of_ne h26, Function.update_of_ne h25, Function.update_of_ne h24, Function.update_of_ne h23, Function.update_self])
      (by simp only [hs', sumNext]; rw [Function.update_of_ne h37, Function.update_of_ne h36, Function.update_of_ne h35, Function.update_of_ne h34, Function.update_self])
      (by simp only [hs', sumNext]; rw [Function.update_of_ne h47, Function.update_of_ne h46, Function.update_of_ne h45, Function.update_self])
      (by simp only [hs', sumNext]; rw [Function.update_of_ne h57, Function.update_of_ne h56, Function.update_self])
      (by simp only [hs', sumNext]; rw [Function.update_of_ne h67, Function.update_self]) (fuel_step l1 l2 l3 l4 c1 c2 m hn hstop)
    have htest : sumTest X1 X2 Y1 Y2 C1 C2 (fun k => (s k).head?) = true := by
      simp only [sumTest, hX1, hX2, hY1, hY2, hC1, hC2, dig_head l1 r1 hl1 hr1,
        dig_head l2 r2 hl2 hr2, dig_head l3 r3 hl3 hr3, dig_head l4 r4 hl4 hr4]
      exact sum_test_true l1 l2 l3 l4 c1 c2 mk hstop
    have hSt' : s' St = (if (dtop l1 + dtop l2 + c1.toNat) % 2 = (dtop l3 + dtop l4 + c2.toNat) % 2
        then [] else [stSym (decide ((dtop l3 + dtop l4 + c2.toNat) % 2 = 1))]) ++ s St := by
      simp only [hs', sumNext, Function.update_self]
    refine ⟨P ++ (if (dtop l1 + dtop l2 + c1.toNat) % 2 = (dtop l3 + dtop l4 + c2.toNat) % 2
        then [] else [stSym (decide ((dtop l3 + dtop l4 + c2.toNat) % 2 = 1))]),
      1 + 1 + 1 + t, by omega, ?_, ?_, ?_⟩
    · simp only [List.length_append]; split_ifs <;> simp <;> omega
    · have e1 := StackProg.Exec.act (sumAct X1 X2 Y1 Y2 C1 C2 St mk) s
      rw [hact] at e1
      refine StackProg.Exec.loopTrue htest e1 (exec_congrG he ?_)
      refine upd7_congr X1 X2 Y1 Y2 C1 C2 St s' s _ _ _ _ _ _ _ _ ?_ ?_
      · intro k k1 k2 k3 k4 k5 k6 k7
        simp only [hs', sumNext]
        rw [Function.update_of_ne k7, Function.update_of_ne k6, Function.update_of_ne k5,
          Function.update_of_ne k4, Function.update_of_ne k3, Function.update_of_ne k2,
          Function.update_of_ne k1]
      · rw [hSt', List.append_assoc]
    · rw [List.append_assoc, ← hSt', hhead, hSt', val_step l1 l2 c1, val_step l3 l4 c2,
        scRes_step _ _ _ _ (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))]
      simp only [Nat.mod_mod]
      split_ifs <;> simp

end Sum

/-! ### digit tokens of a natural number -/

lemma oneA_dg1 (b : Bool) : oneA (some (ι1 (dg b))) = b := by cases b <;> rfl
lemma oneA_dg2 (b : Bool) : oneA (some (ι2 (dg b))) = b := by cases b <;> rfl
lemma digA_dg1 (b : Bool) : digA (some (ι1 (dg b))) = true := by cases b <;> rfl
lemma digA_dg2 (b : Bool) : digA (some (ι2 (dg b))) = true := by cases b <;> rfl

lemma dval_bits1 (k : ℕ) : dval ((Nat.bits k).map (ι1 ∘ dg)) = k := by
  simp only [dval, List.map_map]
  have : ((fun a => oneA (some a)) ∘ ι1 ∘ dg) = id := by
    funext b; exact oneA_dg1 b
  rw [this, List.map_id, bval_bits]

lemma dval_bits2 (k : ℕ) : dval ((Nat.bits k).map (ι2 ∘ dg)) = k := by
  simp only [dval, List.map_map]
  have : ((fun a => oneA (some a)) ∘ ι2 ∘ dg) = id := by
    funext b; exact oneA_dg2 b
  rw [this, List.map_id, bval_bits]

lemma digs1 (k : ℕ) : ∀ a ∈ (Nat.bits k).map (ι1 ∘ dg), digA (some a) = true := by
  intro a ha
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
  exact digA_dg1 b

lemma digs2 (k : ℕ) : ∀ a ∈ (Nat.bits k).map (ι2 ∘ dg), digA (some a) = true := by
  intro a ha
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
  exact digA_dg2 b

lemma digA_sep1 : digA (some (ι1 .sep)) = false := rfl
lemma digA_sep2 : digA (some (ι2 .sep)) = false := rfl
lemma digA_minus : digA (some (ι1 .minus)) = false := rfl
lemma digA_none : digA (none : Option A) = false := rfl

end D0bfS

/-! ## E_time stack program (namespace D0bfB) -/

namespace D0bfB
open D0bfL D0bfT D0bfS


def bval' : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (bval' l)

lemma bval'_bits (n : ℕ) : bval' (Nat.bits n) = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bval']
  | bit b n hn ih => rw [Nat.bits_append_bit _ _ hn]; simp [bval', ih]

lemma sep_split_inj : ∀ {u u' R R' : List BSym}, BSym.sep ∉ u → BSym.sep ∉ u' →
    u ++ BSym.sep :: R = u' ++ BSym.sep :: R' → u = u' ∧ R = R' := by
  intro u
  induction u with
  | nil =>
    intro u' R R' _ hu' h
    rcases u' with _ | ⟨a, u'⟩
    · simpa using h
    · simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hu'
  | cons a u ih =>
    intro u' R R' hu hu' h
    rcases u' with _ | ⟨b, u'⟩
    · simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hu
    · simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := ih (fun hm => hu (List.mem_cons_of_mem _ hm))
        (fun hm => hu' (List.mem_cons_of_mem _ hm)) h.2
      exact ⟨by rw [h.1, h1], h2⟩

def digU (z : ℤ) : List BSym :=
  (if z < 0 then [BSym.minus] else []) ++
    (Nat.bits z.natAbs).map (fun b => if b then BSym.one else BSym.zero)

lemma encInt_eq_digU (z : ℤ) : encInt z = digU z ++ [BSym.sep] := by
  simp [encInt, encNat, digU]

lemma sep_not_mem_digU (z : ℤ) : BSym.sep ∉ digU z := by
  simp only [digU, List.mem_append, List.mem_map, not_or]
  constructor
  · split_ifs <;> simp
  · rintro ⟨b, -, hb⟩; cases b <;> simp at hb

lemma map_bits_inj {a b : List Bool}
    (h : a.map (fun b => if b then BSym.one else BSym.zero) =
      b.map (fun b => if b then BSym.one else BSym.zero)) : a = b := by
  refine List.map_injective_iff.mpr ?_ h
  intro x y hxy; cases x <;> cases y <;> simp_all

lemma digU_inj {z z' : ℤ} (h : digU z = digU z') : z = z' := by
  have key : ∀ {z z' : ℤ}, digU z = digU z' → (z < 0 ↔ z' < 0) := by
    intro z z' h
    by_contra hne
    simp only [digU] at h
    rcases lt_or_ge z 0 with hz | hz <;> rcases lt_or_ge z' 0 with hz' | hz'
    · exact hne (iff_of_true hz hz')
    · rw [if_pos hz, if_neg (not_lt.2 hz')] at h
      cases hb : Nat.bits z'.natAbs with
      | nil => rw [hb] at h; simp at h
      | cons c l => rw [hb] at h; cases c <;> simp at h
    · rw [if_neg (not_lt.2 hz), if_pos hz'] at h
      cases hb : Nat.bits z.natAbs with
      | nil => rw [hb] at h; simp at h
      | cons c l => rw [hb] at h; cases c <;> simp at h
    · exact hne (iff_of_false (not_lt.2 hz) (not_lt.2 hz'))
  have hs := key h
  have habs : z.natAbs = z'.natAbs := by
    simp only [digU] at h
    by_cases hz : z < 0
    · rw [if_pos hz, if_pos (hs.1 hz)] at h
      simp only [List.singleton_append, List.cons.injEq, true_and] at h
      rw [← bval'_bits z.natAbs, ← bval'_bits z'.natAbs, map_bits_inj h]
    · rw [if_neg hz, if_neg (fun h' => hz (hs.2 h'))] at h
      simp only [List.nil_append] at h
      rw [← bval'_bits z.natAbs, ← bval'_bits z'.natAbs, map_bits_inj h]
  omega

lemma encInts_inj : ∀ (l l' : List ℤ), encInts l = encInts l' → l = l' := by
  intro l
  induction l with
  | nil =>
    intro l' h
    rcases l' with _ | ⟨z, l'⟩
    · rfl
    · rw [encInts_cons, encInt_eq_digU] at h; simp [encInts] at h
  | cons z l ih =>
    intro l' h
    rcases l' with _ | ⟨z', l'⟩
    · rw [encInts_cons, encInt_eq_digU] at h; simp [encInts] at h
    · rw [encInts_cons, encInts_cons, encInt_eq_digU, encInt_eq_digU] at h
      simp only [List.append_assoc, List.singleton_append] at h
      obtain ⟨h1, h2⟩ := sep_split_inj (sep_not_mem_digU z) (sep_not_mem_digU z') h
      rw [digU_inj h1, ih l' h2]


/-! ### token helpers -/

lemma encInts_toks (c : List ℤ) : (encInts c).map ι1 = toksE ι1 (c.map digU) := by
  induction c with
  | nil => simp [encInts, toksE_nil]
  | cons z c ih =>
    rw [encInts_cons, encInt_eq_digU, List.map_cons, toksE_cons, ← ih]
    simp

lemma toksE_len_drop (e : BSym → A) (ts : List (List BSym)) (k : ℕ) :
    (toksE e (ts.drop k)).length ≤ (toksE e ts).length := by
  have h : toksE e ts = toksE e (ts.take k) ++ toksE e (ts.drop k) := by
    unfold toksE; rw [← List.flatten_append, ← List.map_append, List.take_append_drop]
  rw [h, List.length_append]; omega

lemma digU_one : digU 1 = [BSym.one] := by
  simp [digU]

lemma headFlag (cl : List ℤ) (p : ℕ) :
    ((cl.map digU).drop p).head? = some [BSym.one] ↔ cl.getD p 0 = 1 := by
  rw [List.head?_drop, List.getElem?_map, List.getD_eq_getElem?_getD]
  obtain ⟨o, ho⟩ : ∃ o, cl[p]? = o := ⟨_, rfl⟩
  rw [ho]
  cases o with
  | none => simp
  | some z =>
    simp only [Option.map_some, Option.some.injEq, Option.getD_some]
    constructor
    · intro hz; exact digU_inj (hz.trans digU_one.symm)
    · intro hz; rw [hz, digU_one]

lemma dropTok (d : List ℕ) (k : ℕ) (hk : k < d.length) :
    toksE ι2 ((d.map tokN).drop k) = (Nat.bits (d.getD k 0)).map (ι2 ∘ dg) ++
      ι2 .sep :: toksE ι2 ((d.map tokN).drop (k + 1)) := by
  rw [List.drop_eq_getElem_cons (by simpa using hk), toksE_cons]
  simp [tokN, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

lemma bits_len_le_toks (d : List ℕ) (k : ℕ) (hk : k < d.length) :
    (Nat.bits (d.getD k 0)).length ≤ (toksE ι2 (d.map tokN)).length := by
  have h1 := toksE_len_drop ι2 (d.map tokN) k
  rw [dropTok d k hk] at h1
  simp only [List.length_append, List.length_map, List.length_cons] at h1; omega

lemma digU_toks_nosep (cl : List ℤ) (p : ℕ) : ∀ t ∈ (cl.map digU).drop p, BSym.sep ∉ t := by
  intro t ht
  obtain ⟨z, -, rfl⟩ := List.mem_map.1 (List.mem_of_mem_drop ht)
  exact sep_not_mem_digU z

/-! ### the integer token at the head of `W` -/

/-- what follows the digits of the integer token at position `q`. -/
def Rw (cl : List ℤ) (q : ℕ) : List A :=
  if q < cl.length then ι1 .sep :: toksE ι1 ((cl.map digU).drop (q + 1)) else []

lemma W_split (cl : List ℤ) (q : ℕ) :
    toksE ι1 ((cl.map digU).drop q) = (digU (cl.getD q 0)).map ι1 ++ Rw cl q := by
  by_cases hq : q < cl.length
  · rw [List.drop_eq_getElem_cons (by simpa using hq), toksE_cons]
    simp [Rw, hq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
  · have h1 : (cl.map digU).drop q = [] := List.drop_eq_nil_of_le (by simp; omega)
    have h2 : cl.getD q 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [h1, h2, toksE_nil]; simp [Rw, hq, digU]

lemma Rw_tail (cl : List ℤ) (q : ℕ) : (Rw cl q).tail = toksE ι1 ((cl.map digU).drop (q + 1)) := by
  unfold Rw; split_ifs with hq
  · rfl
  · rw [List.drop_eq_nil_of_le (by simp; omega), toksE_nil]; rfl

lemma Rw_head (cl : List ℤ) (q : ℕ) :
    (Rw cl q).head? = none ∨ (Rw cl q).head? = some (ι1 .sep) := by
  unfold Rw; split_ifs <;> simp

lemma Rw_dig (cl : List ℤ) (q : ℕ) : digA (Rw cl q).head? = false := by
  rcases Rw_head cl q with h | h <;> rw [h] <;> rfl

lemma digU_map (z : ℤ) : (digU z).map ι1 =
    (if z < 0 then [ι1 .minus] else []) ++ (Nat.bits z.natAbs).map (ι1 ∘ dg) := by
  unfold digU; rw [List.map_append, List.map_map]; split_ifs <;> rfl

lemma head_nonminus (k : ℕ) (cl : List ℤ) (q : ℕ) :
    ((Nat.bits k).map (ι1 ∘ dg) ++ Rw cl q).head? ≠ some (ι1 .minus) := by
  cases h : Nat.bits k with
  | nil =>
    simp only [List.map_nil, List.nil_append]
    rcases Rw_head cl q with h' | h' <;> rw [h']
    · simp
    · intro hb; have := ι1_inj (Option.some.inj hb); cases this
  | cons b l =>
    simp only [List.map_cons, List.cons_append, List.head?_cons]
    intro hb; have := ι1_inj (Option.some.inj hb); cases b <;> cases this

lemma scRes_false (X Y : ℕ) : scRes X Y none = some (stSym false) ↔ Y < X := by
  unfold scRes
  split_ifs with h1 h2 <;> simp [stSym, ι1] <;> omega

lemma dval_nil : dval [] = 0 := rfl

lemma dd_head (d : List ℕ) : digA (toksE ι2 (d.map tokN)).head? = !decide (d.getD 0 0 = 0) := by
  cases d with
  | nil => rw [List.map_nil, toksE_nil]; rfl
  | cons a d =>
    rw [List.map_cons, toksE_cons]
    have hg : (a :: d).getD 0 0 = a := rfl
    rw [hg]
    by_cases ha : a = 0
    · subst ha; rfl
    · obtain ⟨b, l, hbl⟩ : ∃ b l, Nat.bits a = b :: l := by
        cases h : Nat.bits a with
        | nil => exact absurd (show a = 0 by rw [← bval_bits a, h]; rfl) ha
        | cons b l => exact ⟨b, l, rfl⟩
      simp only [tokN, hbl, List.map_cons, List.cons_append, List.head?_cons, ha, decide_false,
        Bool.not_false]
      cases b <;> rfl


end D0bfB


set_option autoImplicit false
set_option linter.all false

open CookPvsNP ProjSchedTW.Complexity

namespace OvlB
open D0bfL D0bfT D0bfS D0bfB

/-! ### keys -/

inductive KO
  | ki | ko | sc | st | kc | kd | kC | kD | W0 | DD | N | Np | Y0 | Bd0 | Ic | Jc | I3 | NI | J3
  | NJ | Q1 | Q2 | Q3 | X | E | Y | Z | C1 | C2 | St | FA | FC | Bd
  deriving DecidableEq

instance : Fintype KO := Fintype.ofList
  [KO.ki, KO.ko, KO.sc, KO.st, KO.kc, KO.kd, KO.kC, KO.kD, KO.W0, KO.DD, KO.N, KO.Np, KO.Y0,
    KO.Bd0, KO.Ic, KO.Jc, KO.I3, KO.NI, KO.J3, KO.NJ, KO.Q1, KO.Q2, KO.Q3, KO.X, KO.E, KO.Y, KO.Z,
    KO.C1, KO.C2, KO.St, KO.FA, KO.FC, KO.Bd]
  (by intro x; cases x <;> simp)

abbrev SP := StackProg KO A

lemma exec_congr {p : SP} {s t t' : KO → List A} {n : ℕ} (h : p.Exec s t n) (e : t = t') :
    p.Exec s t' n := e ▸ h

lemma bndA (L : ℕ) : L * (3 * L + 7) + 1 + 60 * L + 100 ≤ 20 * (L + 3) * (L + 3) := by
  ring_nf; omega

lemma bndB (L : ℕ) : 2 * (20 * (L + 3) * (L + 3)) + 36 * L + 100 ≤ 60 * (L + 3) * (L + 3) := by
  ring_nf; omega

lemma bndC (L : ℕ) : (3 * L + 4) * ((3 * L + 4) * (60 * (3 * L + 6) * (3 * L + 6) + 14) +
    40 * (3 * L + 3) + 80) + 1 ≤ 1000 * ((3 * L + 4) * (3 * L + 4) * (3 * L + 4) * (3 * L + 4)) := by
  ring_nf; omega

/-! ### skipping `k` tokens when fewer may be present -/

lemma exec_skipToks' (cnt W : KO) (hcW : cnt ≠ W) (e : BSym → A) (he : Function.Injective e)
    (k : ℕ) (ts : List (List BSym)) (s : KO → List A) (hts : ∀ t ∈ ts, BSym.sep ∉ t)
    (hc : s cnt = List.replicate k mkA) (hW : s W = toksE e ts) :
    ∃ m ≤ k * (3 * (toksE e ts).length + 7) + 1, (skipToks cnt W e).Exec s
      (Function.update (Function.update s cnt []) W (toksE e (ts.drop k))) m := by
  have key := exec_for cnt (.seq (popProg cnt) (skipOne W e)) mkA
    (fun t s' => s' = Function.update (Function.update s cnt (List.replicate (k - t) mkA)) W
      (toksE e (ts.drop t))) k (3 * (toksE e ts).length + 5) ?_ s ?_ hc
  · obtain ⟨s', m, hm, he', hs'⟩ := key
    refine ⟨m, by omega, ?_⟩
    rw [hs', Nat.sub_self, List.replicate_zero] at he'; exact he'
  · intro t ht s' hs' _
    subst hs'
    set S := Function.update (Function.update s cnt (List.replicate (k - t) mkA)) W
      (toksE e (ts.drop t)) with hS
    have e1 := exec_pop cnt S
    obtain ⟨m2, hm2, e2⟩ := exec_skipOne' W e he (ts.drop t) (Function.update S cnt (S cnt).tail)
      (fun x hx => hts x (List.mem_of_mem_drop hx)) (by simp [hS, Function.update_apply, hcW.symm])
    have hl := toksE_len_drop e ts t
    refine ⟨_, _, ?_, StackProg.Exec.seq e1 e2, ?_, ?_⟩
    · simp [hS, Function.update_apply, hcW.symm] at hm2; omega
    · funext x
      by_cases h1 : x = W
      · subst h1; simp [hS, List.tail_drop]
      · by_cases h2 : x = cnt
        · subst h2; simp [hS, Function.update_apply, h1, List.tail_replicate, Nat.sub_sub]
        · simp [hS, Function.update_apply, h1, h2]
    · simp [hS, Function.update_apply, hcW, List.tail_replicate, Nat.sub_sub]
  · funext x
    by_cases h1 : x = W
    · subst h1; simp [hW]
    · by_cases h2 : x = cnt
      · subst h2; simp [Function.update_apply, h1, hc]
      · simp [Function.update_apply, h1, h2]

/-! ### digit lists -/

lemma dval_zero_cons (l : List A) : dval (ι1 .zero :: l) = 2 * dval l := by
  rw [dval_split]; simp [dtop, oneA, ι1, ι2]

lemma digA_zero : digA (some (ι1 .zero)) = true := rfl

/-! ### one comparison block: flag `FC` unless `d_{p₁} + 2|c_{p₂}| ≤ d_{p₃}` -/

def minusPop : SP := .branch (fun h => decide (h KO.E = some (ι1 .minus))) (popProg KO.E) skipP

def cmpBlock : SP :=
  .seq (copyProg KO.DD KO.X KO.sc) (.seq (skipToks KO.Q1 KO.X ι2)
  (.seq (copyProg KO.W0 KO.E KO.sc) (.seq (skipToks KO.Q2 KO.E ι1)
  (.seq minusPop (.seq (pushProg KO.E (ι1 .zero))
  (.seq (copyProg KO.DD KO.Y KO.sc) (.seq (skipToks KO.Q3 KO.Y ι2)
  (.seq (sumLoop KO.X KO.E KO.Y KO.Z KO.C1 KO.C2 KO.St mkA)
  (.seq (flagP KO.FC (fun h => decide (h KO.St = some (stSym false))))
  (.seq (clearProg KO.X) (.seq (clearProg KO.E) (.seq (clearProg KO.Y) (clearProg KO.St)))))))))))))

set_option maxHeartbeats 4000000 in
lemma exec_minusPop (s : KO → List A) (cl : List ℤ) (q : ℕ)
    (hE : s KO.E = toksE ι1 ((cl.map digU).drop q)) :
    ∃ m ≤ 2, minusPop.Exec s (Function.update s KO.E
      ((Nat.bits (cl.getD q 0).natAbs).map (ι1 ∘ dg) ++ Rw cl q)) m := by
  have hWs := W_split cl q
  rw [digU_map] at hWs
  by_cases hneg : cl.getD q 0 < 0
  · rw [if_pos hneg, List.singleton_append] at hWs
    have e1 := exec_pop KO.E s
    refine ⟨1 + 1, le_rfl, StackProg.Exec.branchTrue ?_ (exec_congr e1 ?_)⟩
    · show decide ((s KO.E).head? = some (ι1 .minus)) = true
      rw [hE, hWs]; simp
    · rw [hE, hWs]; rfl
  · rw [if_neg hneg, List.nil_append] at hWs
    have e1 := exec_skipP (K := KO) s
    refine ⟨1 + 1, le_rfl, StackProg.Exec.branchFalse ?_ (exec_congr e1 ?_)⟩
    · show decide ((s KO.E).head? = some (ι1 .minus)) = false
      rw [hE, hWs]; exact decide_eq_false (head_nonminus _ cl q)
    · rw [← hWs, ← hE]; simp

set_option maxHeartbeats 8000000 in
lemma exec_cmpBlock (s : KO → List A) (cl : List ℤ) (d : List ℕ) (p1 p2 p3 L : ℕ)
    (hW0 : s KO.W0 = toksE ι1 (cl.map digU)) (hDD : s KO.DD = toksE ι2 (d.map tokN))
    (hQ1 : s KO.Q1 = List.replicate p1 mkA) (hQ2 : s KO.Q2 = List.replicate p2 mkA)
    (hQ3 : s KO.Q3 = List.replicate p3 mkA)
    (hX : s KO.X = []) (hE : s KO.E = []) (hY : s KO.Y = []) (hZ : s KO.Z = [])
    (hC1 : s KO.C1 = []) (hC2 : s KO.C2 = []) (hSt : s KO.St = []) (hsc : s KO.sc = [])
    (hp1 : p1 < d.length) (hp3 : p3 < d.length)
    (hLc : (toksE ι1 (cl.map digU)).length ≤ L) (hL : (toksE ι2 (d.map tokN)).length ≤ L)
    (hp2 : p2 ≤ L) :
    ∃ m ≤ 20 * (L + 3) * (L + 3), cmpBlock.Exec s
      (Function.update (Function.update (Function.update (Function.update s KO.Q1 []) KO.Q2 [])
        KO.Q3 [])
        KO.FC (if d.getD p1 0 + 2 * (cl.getD p2 0).natAbs ≤ d.getD p3 0 then s KO.FC
          else mkA :: s KO.FC)) m := by
  have hts : ∀ t ∈ d.map tokN, BSym.sep ∉ t := by
    simp only [List.mem_map]; rintro t ⟨a, -, rfl⟩; exact tokN_no_sep a
  -- fetch `d_{p1}` into X
  obtain ⟨m1, hm1, e1⟩ := exec_copy KO.DD KO.X KO.sc (by decide) (by decide) (by decide) s hsc
  set s1 := Function.update s KO.X (s KO.DD ++ s KO.X) with hs1
  obtain ⟨m2, hm2, e2⟩ := exec_skipToks KO.Q1 KO.X (by decide) ι2 ι2_inj mkA [] p1
    (d.map tokN) s1 hts (by simp; omega) (by simp [hs1, hQ1]) (by simp [hs1, hDD, hX])
  set s2 := Function.update (Function.update s1 KO.Q1 []) KO.X
    (toksE ι2 ((d.map tokN).drop p1) ++ []) with hs2
  -- fetch `|c_{p2}|` into E
  obtain ⟨m3, hm3, e3⟩ := exec_copy KO.W0 KO.E KO.sc (by decide) (by decide) (by decide) s2
    (by simp [hs1, hs2, hsc])
  set s3 := Function.update s2 KO.E (s2 KO.W0 ++ s2 KO.E) with hs3
  obtain ⟨m4, hm4, e4⟩ := exec_skipToks' KO.Q2 KO.E (by decide) ι1 ι1_inj p2 (cl.map digU) s3
    (by simpa using digU_toks_nosep cl 0) (by simp [hs1, hs2, hs3, hQ2])
    (by simp [hs1, hs2, hs3, hW0, hE])
  set s4 := Function.update (Function.update s3 KO.Q2 []) KO.E
    (toksE ι1 ((cl.map digU).drop p2)) with hs4
  obtain ⟨m5, hm5, e5⟩ := exec_minusPop s4 cl p2 (by simp [hs4])
  set s5 := Function.update s4 KO.E
    ((Nat.bits (cl.getD p2 0).natAbs).map (ι1 ∘ dg) ++ Rw cl p2) with hs5
  have e6 := exec_pushG KO.E (ι1 .zero) s5
  set s6 := Function.update s5 KO.E (ι1 .zero :: s5 KO.E) with hs6
  -- fetch `d_{p3}` into Y
  obtain ⟨m7, hm7, e7⟩ := exec_copy KO.DD KO.Y KO.sc (by decide) (by decide) (by decide) s6
    (by simp [hs1, hs2, hs3, hs4, hs5, hs6, hsc])
  set s7 := Function.update s6 KO.Y (s6 KO.DD ++ s6 KO.Y) with hs7
  obtain ⟨m8, hm8, e8⟩ := exec_skipToks KO.Q3 KO.Y (by decide) ι2 ι2_inj mkA [] p3
    (d.map tokN) s7 hts (by simp; omega) (by simp [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hQ3])
    (by simp [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hDD, hY])
  set s8 := Function.update (Function.update s7 KO.Q3 []) KO.Y
    (toksE ι2 ((d.map tokN).drop p3) ++ []) with hs8
  -- the comparison
  have hdx := dropTok d p1 hp1
  have hdy := dropTok d p3 hp3
  have hbx := bits_len_le_toks d p1 hp1
  have hby := bits_len_le_toks d p3 hp3
  have hWs := W_split cl p2
  have hlz : (Nat.bits (cl.getD p2 0).natAbs).length ≤ L := by
    have h := le_trans (toksE_len_drop ι1 (cl.map digU) p2) hLc
    rw [hWs, digU_map] at h
    simp only [List.length_append, List.length_map] at h
    omega
  have h8X : s8 KO.X = (Nat.bits (d.getD p1 0)).map (ι2 ∘ dg) ++
      ι2 .sep :: toksE ι2 ((d.map tokN).drop (p1 + 1)) := by
    rw [← hdx]; simp [hs8, hs7, hs6, hs5, hs4, hs3, hs2]
  have h8Y : s8 KO.Y = (Nat.bits (d.getD p3 0)).map (ι2 ∘ dg) ++
      ι2 .sep :: toksE ι2 ((d.map tokN).drop (p3 + 1)) := by
    rw [← hdy]; simp [hs8]
  have h8E : s8 KO.E = (ι1 .zero :: (Nat.bits (cl.getD p2 0).natAbs).map (ι1 ∘ dg)) ++
      Rw cl p2 := by simp [hs8, hs7, hs6, hs5]
  obtain ⟨P, t9, ht9, hP, e9, hhd⟩ := exec_sum KO.X KO.E KO.Y KO.Z KO.C1 KO.C2 KO.St
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    mkA (ι2 .sep :: toksE ι2 ((d.map tokN).drop (p1 + 1))) (Rw cl p2)
    (ι2 .sep :: toksE ι2 ((d.map tokN).drop (p3 + 1))) [] digA_sep2 (Rw_dig cl p2) digA_sep2
    digA_none (L + 2) ((Nat.bits (d.getD p1 0)).map (ι2 ∘ dg))
    (ι1 .zero :: (Nat.bits (cl.getD p2 0).natAbs).map (ι1 ∘ dg))
    ((Nat.bits (d.getD p3 0)).map (ι2 ∘ dg)) [] false false s8 (digs2 _)
    (by
      intro a ha
      rcases List.mem_cons.1 ha with rfl | ha
      · exact digA_zero
      · exact digs1 _ a ha)
    (digs2 _) (by simp) h8X h8E h8Y
    (by simp [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, hZ])
    (by simp [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, hC1, cst])
    (by simp [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, hC2, cst])
    (Or.inl (by
      simp only [List.length_map, List.length_cons, List.length_nil]
      have h1 : (Nat.bits (d.getD p1 0)).length ≤ L := le_trans hbx hL
      have h2 : (Nat.bits (d.getD p3 0)).length ≤ L := le_trans hby hL
      omega))
  have hs8St : s8 KO.St = [] := by simp [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, hSt]
  rw [hs8St, List.append_nil, dval_bits2, dval_zero_cons, dval_bits1, dval_bits2, dval_nil] at hhd
  simp only [Bool.toNat_false, add_zero, List.head?_nil] at hhd
  set s9 := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update s8 KO.X (ι2 .sep :: toksE ι2 ((d.map tokN).drop (p1 + 1))))
    KO.E (Rw cl p2)) KO.Y (ι2 .sep :: toksE ι2 ((d.map tokN).drop (p3 + 1)))) KO.Z []) KO.C1 [])
    KO.C2 []) KO.St (P ++ s8 KO.St) with hs9
  have hs9St : s9 KO.St = P := by simp [hs9, hs8St]
  have hs9FC : s9 KO.FC = s KO.FC := by simp [hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1]
  have e10 := exec_congr (exec_flagP KO.FC (fun h => decide (h KO.St = some (stSym false))) s9)
    (t' := Function.update s9 KO.FC
      (if d.getD p1 0 + 2 * (cl.getD p2 0).natAbs ≤ d.getD p3 0 then s KO.FC
        else mkA :: s KO.FC)) (by
      congr 1
      show (if decide ((s9 KO.St).head? = some (stSym false)) = true then mkA :: s9 KO.FC
        else s9 KO.FC) = _
      rw [hs9St, hs9FC, hhd]
      by_cases hc : d.getD p1 0 + 2 * (cl.getD p2 0).natAbs ≤ d.getD p3 0
      · have hn : ¬ (scRes (d.getD p1 0 + 2 * (cl.getD p2 0).natAbs) (d.getD p3 0) none =
            some (stSym false)) := by rw [scRes_false]; omega
        simp only [decide_eq_true_eq]; rw [if_neg hn, if_pos hc]
      · have hn : (scRes (d.getD p1 0 + 2 * (cl.getD p2 0).natAbs) (d.getD p3 0) none =
            some (stSym false)) := by rw [scRes_false]; omega
        simp only [decide_eq_true_eq]; rw [if_pos hn, if_neg hc])
  set s10 := Function.update s9 KO.FC
      (if d.getD p1 0 + 2 * (cl.getD p2 0).natAbs ≤ d.getD p3 0 then s KO.FC
        else mkA :: s KO.FC) with hs10
  obtain ⟨m11, hm11, e11⟩ := exec_clearG KO.X s10
  obtain ⟨m12, hm12, e12⟩ := exec_clearG KO.E (Function.update s10 KO.X [])
  obtain ⟨m13, hm13, e13⟩ := exec_clearG KO.Y (Function.update (Function.update s10 KO.X []) KO.E [])
  obtain ⟨m14, hm14, e14⟩ := exec_clearG KO.St
    (Function.update (Function.update (Function.update s10 KO.X []) KO.E []) KO.Y [])
  -- bounds
  have hX10 : (s10 KO.X).length ≤ L + 1 := by
    have := toksE_len_drop ι2 (d.map tokN) (p1 + 1); simp [hs10, hs9]; omega
  have hE10 : ((Function.update s10 KO.X []) KO.E).length ≤ L + 1 := by
    have h := le_trans (toksE_len_drop ι1 (cl.map digU) p2) hLc
    rw [hWs] at h
    simp only [List.length_append] at h
    simp [hs10, hs9]; omega
  have hY10 : ((Function.update (Function.update s10 KO.X []) KO.E []) KO.Y).length ≤ L + 1 := by
    have := toksE_len_drop ι2 (d.map tokN) (p3 + 1); simp [hs10, hs9]; omega
  have hSt10 : ((Function.update (Function.update (Function.update s10 KO.X []) KO.E []) KO.Y [])
      KO.St).length ≤ L + 2 := by simp [hs10, hs9, hs8St]; omega
  have hm1' : m1 ≤ 6 * L + 3 := by rw [hDD] at hm1; omega
  have hm2' : m2 ≤ 7 * L + 1 := by
    have : (s1 KO.X).length = (toksE ι2 (d.map tokN)).length := by simp [hs1, hDD, hX]
    omega
  have hm3' : m3 ≤ 6 * L + 3 := by
    have : (s2 KO.W0).length = (toksE ι1 (cl.map digU)).length := by simp [hs1, hs2, hW0]
    omega
  have hm4' : m4 ≤ L * (3 * L + 7) + 1 := by
    have : p2 * (3 * (toksE ι1 (cl.map digU)).length + 7) ≤ L * (3 * L + 7) :=
      Nat.mul_le_mul hp2 (by omega)
    omega
  have hm7' : m7 ≤ 6 * L + 3 := by
    have : (s6 KO.DD).length = (toksE ι2 (d.map tokN)).length := by
      simp [hs1, hs2, hs3, hs4, hs5, hs6, hDD]
    omega
  have hm8' : m8 ≤ 7 * L + 1 := by
    have : (s7 KO.Y).length = (toksE ι2 (d.map tokN)).length := by
      simp [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hDD, hY]
    omega
  refine ⟨_, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3
    (StackProg.Exec.seq e4 (StackProg.Exec.seq e5 (StackProg.Exec.seq e6 (StackProg.Exec.seq e7
    (StackProg.Exec.seq e8 (StackProg.Exec.seq e9 (StackProg.Exec.seq e10
    (StackProg.Exec.seq e11 (StackProg.Exec.seq e12 (StackProg.Exec.seq e13
      (exec_congr e14 ?_)))))))))))))⟩
  · have hsq := bndA L
    clear * - hsq hm1' hm2' hm3' hm4' hm5 hm7' hm8' ht9 hm11 hm12 hm13 hm14 hX10 hE10 hY10 hSt10
    omega
  · funext k
    cases k <;> simp [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, Function.update_apply,
      hX, hE, hY, hZ, hC1, hC2, hSt]

lemma len_encNats' (d : List ℕ) : d.length ≤ (encNats d).length := by
  induction d with
  | nil => simp
  | cons k d ih =>
    rw [encNats_cons, List.length_append, List.length_cons]
    have : 1 ≤ (encNat k).length := by
      rw [encNat_dg]; simp only [List.length_append, List.length_singleton]; omega
    omega

lemma len_toks_d (d : List ℕ) : d.length ≤ (toksE ι2 (d.map tokN)).length := by
  rw [← encNats_toks ι2 d]; simpa using len_encNats' d

/-! ### the pair block: flag `Bd` if tasks `i` and `j` overlap -/

def pairBody : SP :=
  .seq (copyProg KO.I3 KO.Q1 KO.sc) (.seq (copyProg KO.NI KO.Q2 KO.sc)
  (.seq (copyProg KO.J3 KO.Q3 KO.sc) (.seq cmpBlock
  (.seq (transferProg KO.FC (fun k => decide (k = KO.FA)))
  (.seq (copyProg KO.J3 KO.Q1 KO.sc) (.seq (copyProg KO.NJ KO.Q2 KO.sc)
  (.seq (copyProg KO.I3 KO.Q3 KO.sc) (.seq cmpBlock
  (.seq (flagP KO.Bd (fun h => (h KO.FA).isSome && (h KO.FC).isSome))
  (.seq (clearProg KO.FA) (clearProg KO.FC)))))))))))

/-- the non-overlap condition of two tasks given by their certificate and instance positions. -/
def okPair (cl : List ℤ) (d : List ℕ) (a b a' b' : ℕ) : Prop :=
  d.getD a 0 + 2 * (cl.getD b 0).natAbs ≤ d.getD a' 0 ∨
    d.getD a' 0 + 2 * (cl.getD b' 0).natAbs ≤ d.getD a 0

instance (cl : List ℤ) (d : List ℕ) (a b a' b' : ℕ) : Decidable (okPair cl d a b a' b') := by
  unfold okPair; infer_instance

set_option maxHeartbeats 8000000 in
lemma exec_pairBody (s : KO → List A) (cl : List ℤ) (d : List ℕ) (a b a' b' L : ℕ)
    (hW0 : s KO.W0 = toksE ι1 (cl.map digU)) (hDD : s KO.DD = toksE ι2 (d.map tokN))
    (hI3 : s KO.I3 = List.replicate a mkA) (hNI : s KO.NI = List.replicate b mkA)
    (hJ3 : s KO.J3 = List.replicate a' mkA) (hNJ : s KO.NJ = List.replicate b' mkA)
    (hQ1 : s KO.Q1 = []) (hQ2 : s KO.Q2 = []) (hQ3 : s KO.Q3 = [])
    (hFA : s KO.FA = []) (hFC : s KO.FC = [])
    (hX : s KO.X = []) (hE : s KO.E = []) (hY : s KO.Y = []) (hZ : s KO.Z = [])
    (hC1 : s KO.C1 = []) (hC2 : s KO.C2 = []) (hSt : s KO.St = []) (hsc : s KO.sc = [])
    (ha : a < d.length) (ha' : a' < d.length)
    (hLc : (toksE ι1 (cl.map digU)).length ≤ L) (hL : (toksE ι2 (d.map tokN)).length ≤ L)
    (hb : b ≤ L) (hb' : b' ≤ L) :
    ∃ m ≤ 60 * (L + 3) * (L + 3), pairBody.Exec s
      (Function.update s KO.Bd (if okPair cl d a b a' b' then s KO.Bd else mkA :: s KO.Bd)) m := by
  obtain ⟨m1, hm1, e1⟩ := exec_copy KO.I3 KO.Q1 KO.sc (by decide) (by decide) (by decide) s hsc
  set s1 := Function.update s KO.Q1 (s KO.I3 ++ s KO.Q1) with hs1
  obtain ⟨m2, hm2, e2⟩ := exec_copy KO.NI KO.Q2 KO.sc (by decide) (by decide) (by decide) s1
    (by simp [hs1, hsc])
  set s2 := Function.update s1 KO.Q2 (s1 KO.NI ++ s1 KO.Q2) with hs2
  obtain ⟨m3, hm3, e3⟩ := exec_copy KO.J3 KO.Q3 KO.sc (by decide) (by decide) (by decide) s2
    (by simp [hs1, hs2, hsc])
  set s3 := Function.update s2 KO.Q3 (s2 KO.J3 ++ s2 KO.Q3) with hs3
  obtain ⟨m4, hm4, e4⟩ := exec_cmpBlock s3 cl d a b a' L
    (by simp [hs1, hs2, hs3, hW0]) (by simp [hs1, hs2, hs3, hDD])
    (by simp [hs1, hs2, hs3, hI3, hQ1]) (by simp [hs1, hs2, hs3, hNI, hQ2])
    (by simp [hs1, hs2, hs3, hJ3, hQ3])
    (by simp [hs1, hs2, hs3, hX]) (by simp [hs1, hs2, hs3, hE]) (by simp [hs1, hs2, hs3, hY])
    (by simp [hs1, hs2, hs3, hZ]) (by simp [hs1, hs2, hs3, hC1]) (by simp [hs1, hs2, hs3, hC2])
    (by simp [hs1, hs2, hs3, hSt]) (by simp [hs1, hs2, hs3, hsc]) ha ha' hLc hL hb
  set c1 := d.getD a 0 + 2 * (cl.getD b 0).natAbs ≤ d.getD a' 0 with hc1
  set s4 := Function.update (Function.update (Function.update (Function.update s3 KO.Q1 [])
    KO.Q2 []) KO.Q3 []) KO.FC (if c1 then s3 KO.FC else mkA :: s3 KO.FC) with hs4
  have hs4FC : s4 KO.FC = if c1 then [] else [mkA] := by
    simp only [hs4, Function.update_self]; simp [hs1, hs2, hs3, hFC]
  obtain ⟨m5, hm5, e5⟩ := exec_transfer KO.FC (fun k => decide (k = KO.FA)) _ s4 rfl
  set s5 := transferStore KO.FC (fun k => decide (k = KO.FA)) s4 with hs5
  obtain ⟨m6, hm6, e6⟩ := exec_copy KO.J3 KO.Q1 KO.sc (by decide) (by decide) (by decide) s5
    (by simp [hs5, transferStore, hs4, hs1, hs2, hs3, hsc])
  set s6 := Function.update s5 KO.Q1 (s5 KO.J3 ++ s5 KO.Q1) with hs6
  obtain ⟨m7, hm7, e7⟩ := exec_copy KO.NJ KO.Q2 KO.sc (by decide) (by decide) (by decide) s6
    (by simp [hs6, hs5, transferStore, hs4, hs1, hs2, hs3, hsc])
  set s7 := Function.update s6 KO.Q2 (s6 KO.NJ ++ s6 KO.Q2) with hs7
  obtain ⟨m8, hm8, e8⟩ := exec_copy KO.I3 KO.Q3 KO.sc (by decide) (by decide) (by decide) s7
    (by simp [hs7, hs6, hs5, transferStore, hs4, hs1, hs2, hs3, hsc])
  set s8 := Function.update s7 KO.Q3 (s7 KO.I3 ++ s7 KO.Q3) with hs8
  obtain ⟨m9, hm9, e9⟩ := exec_cmpBlock s8 cl d a' b' a L
    (by simp [hs8, hs7, hs6, hs5, transferStore, hs4, hs1, hs2, hs3, hW0])
    (by simp [hs8, hs7, hs6, hs5, transferStore, hs4, hs1, hs2, hs3, hDD])
    (by simp [hs8, hs7, hs6, hs5, transferStore, hs4, hs1, hs2, hs3, hJ3])
    (by simp [hs8, hs7, hs6, hs5, transferStore, hs4, hs1, hs2, hs3, hNJ])
    (by simp [hs8, hs7, hs6, hs5, transferStore, hs4, hs1, hs2, hs3, hI3])
    (by simp [hs8, hs7, hs6, hs5, transferStore, hs4, hs1, hs2, hs3, hX])
    (by simp [hs8, hs7, hs6, hs5, transferStore, hs4, hs1, hs2, hs3, hE])
    (by simp [hs8, hs7, hs6, hs5, transferStore, hs4, hs1, hs2, hs3, hY])
    (by simp [hs8, hs7, hs6, hs5, transferStore, hs4, hs1, hs2, hs3, hZ])
    (by simp [hs8, hs7, hs6, hs5, transferStore, hs4, hs1, hs2, hs3, hC1])
    (by simp [hs8, hs7, hs6, hs5, transferStore, hs4, hs1, hs2, hs3, hC2])
    (by simp [hs8, hs7, hs6, hs5, transferStore, hs4, hs1, hs2, hs3, hSt])
    (by simp [hs8, hs7, hs6, hs5, transferStore, hs4, hs1, hs2, hs3, hsc]) ha' ha hLc hL hb'
  set c2 := d.getD a' 0 + 2 * (cl.getD b' 0).natAbs ≤ d.getD a 0 with hc2
  set s9 := Function.update (Function.update (Function.update (Function.update s8 KO.Q1 [])
    KO.Q2 []) KO.Q3 []) KO.FC (if c2 then s8 KO.FC else mkA :: s8 KO.FC) with hs9
  have hs9FA : s9 KO.FA = if c1 then [] else [mkA] := by
    simp [hs9, hs8, hs7, hs6, hs5, transferStore, hs4FC, hs4, hs1, hs2, hs3, hFA]
    split_ifs <;> simp [hFC]
  have hs9FC : s9 KO.FC = if c2 then [] else [mkA] := by
    simp only [hs9, Function.update_self]
    simp [hs8, hs7, hs6, hs5, transferStore]
  have hs9Bd : s9 KO.Bd = s KO.Bd := by
    simp [hs9, hs8, hs7, hs6, hs5, transferStore, hs4, hs1, hs2, hs3]
  have e10 := exec_congr (exec_flagP KO.Bd (fun h => (h KO.FA).isSome && (h KO.FC).isSome) s9)
    (t' := Function.update s9 KO.Bd (if okPair cl d a b a' b' then s KO.Bd else mkA :: s KO.Bd))
    (by
      congr 1
      simp only [hs9FA, hs9FC, hs9Bd]
      by_cases h1 : c1 <;> by_cases h2 : c2
      · have hk : okPair cl d a b a' b' := Or.inl h1
        simp [h1, h2, hk]
      · have hk : okPair cl d a b a' b' := Or.inl h1
        simp [h1, h2, hk]
      · have hk : okPair cl d a b a' b' := Or.inr h2
        simp [h1, h2, hk]
      · have hk : ¬okPair cl d a b a' b' := fun h => h.elim h1 h2
        simp [h1, h2, hk])
  set s10 := Function.update s9 KO.Bd (if okPair cl d a b a' b' then s KO.Bd else mkA :: s KO.Bd)
    with hs10
  obtain ⟨m11, hm11, e11⟩ := exec_clearG KO.FA s10
  obtain ⟨m12, hm12, e12⟩ := exec_clearG KO.FC (Function.update s10 KO.FA [])
  have hm11' : m11 ≤ 4 := by
    have : (s10 KO.FA).length ≤ 1 := by
      simp only [hs10, Function.update_apply, if_neg (show KO.FA ≠ KO.Bd by decide)]
      rw [hs9FA]; split_ifs <;> simp
    omega
  have hm12' : m12 ≤ 4 := by
    have : ((Function.update s10 KO.FA []) KO.FC).length ≤ 1 := by
      simp only [hs10, Function.update_apply, if_neg (show KO.FC ≠ KO.Bd by decide),
        if_neg (show KO.FC ≠ KO.FA by decide)]
      rw [hs9FC]; split_ifs <;> simp
    omega
  have hm5' : m5 ≤ 4 := by
    have : (s4 KO.FC).length ≤ 1 := by rw [hs4FC]; split_ifs <;> simp
    omega
  have hdL := len_toks_d d
  have haL : a ≤ L := by omega
  have ha'L : a' ≤ L := by omega
  have hm1' : m1 ≤ 6 * L + 3 := by simp [hI3] at hm1; omega
  have hm2' : m2 ≤ 6 * L + 3 := by simp [hs1, hNI] at hm2; omega
  have hm3' : m3 ≤ 6 * L + 3 := by simp [hs1, hs2, hJ3] at hm3; omega
  have hm6' : m6 ≤ 6 * L + 3 := by
    simp [hs6, hs5, transferStore, hs4, hs1, hs2, hs3, hJ3] at hm6; omega
  have hm7' : m7 ≤ 6 * L + 3 := by
    simp [hs7, hs6, hs5, transferStore, hs4, hs1, hs2, hs3, hNJ] at hm7; omega
  have hm8' : m8 ≤ 6 * L + 3 := by
    simp [hs8, hs7, hs6, hs5, transferStore, hs4, hs1, hs2, hs3, hI3] at hm8; omega
  refine ⟨_, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3
    (StackProg.Exec.seq e4 (StackProg.Exec.seq e5 (StackProg.Exec.seq e6 (StackProg.Exec.seq e7
    (StackProg.Exec.seq e8 (StackProg.Exec.seq e9 (StackProg.Exec.seq e10
    (StackProg.Exec.seq e11 (exec_congr e12 ?_)))))))))))⟩
  · have hsq := bndB L
    clear * - hsq hm1' hm2' hm3' hm4 hm5' hm6' hm7' hm8' hm9 hm11' hm12'
    omega
  · funext k
    cases k <;> simp [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, transferStore,
      Function.update_apply, hQ1, hQ2, hQ3, hFA, hFC]

/-! ### the inner loop over `j > i` -/

def innerBody : SP :=
  .seq (popProg KO.Jc) (.seq pairBody (.seq (pushProg KO.J3 mkA) (.seq (pushProg KO.J3 mkA)
    (.seq (pushProg KO.J3 mkA) (pushProg KO.NJ mkA)))))

def innerLoop : SP := .loop (fun h => (h KO.Jc).isSome) innerBody

/-- tasks `i` and `j` (0-based, `n` tasks) do not overlap. -/
def ovl (cl : List ℤ) (d : List ℕ) (n i j : ℕ) : Prop :=
  okPair cl d (3 * i + 1) (n + 2 + i) (3 * j + 1) (n + 2 + j)

instance (cl : List ℤ) (d : List ℕ) (n i j : ℕ) : Decidable (ovl cl d n i j) := by
  unfold ovl; infer_instance

set_option maxHeartbeats 8000000 in
lemma exec_innerLoop (s0 : KO → List A) (cl : List ℤ) (d : List ℕ) (n i m L : ℕ)
    (hW0 : s0 KO.W0 = toksE ι1 (cl.map digU)) (hDD : s0 KO.DD = toksE ι2 (d.map tokN))
    (hI3 : s0 KO.I3 = List.replicate (3 * i + 1) mkA)
    (hNI : s0 KO.NI = List.replicate (n + 2 + i) mkA)
    (hJ3 : s0 KO.J3 = List.replicate (3 * (i + 1) + 1) mkA)
    (hNJ : s0 KO.NJ = List.replicate (n + 2 + (i + 1)) mkA)
    (hJc : s0 KO.Jc = List.replicate m mkA)
    (hQ1 : s0 KO.Q1 = []) (hQ2 : s0 KO.Q2 = []) (hQ3 : s0 KO.Q3 = [])
    (hFA : s0 KO.FA = []) (hFC : s0 KO.FC = [])
    (hX : s0 KO.X = []) (hE : s0 KO.E = []) (hY : s0 KO.Y = []) (hZ : s0 KO.Z = [])
    (hC1 : s0 KO.C1 = []) (hC2 : s0 KO.C2 = []) (hSt : s0 KO.St = []) (hsc : s0 KO.sc = [])
    (him : i + 1 + m ≤ n) (hd : 3 * n ≤ d.length)
    (hLc : (toksE ι1 (cl.map digU)).length ≤ L) (hL : (toksE ι2 (d.map tokN)).length ≤ L)
    (hnL : n + 2 + n ≤ L) :
    ∃ s' t, t ≤ m * (60 * (L + 3) * (L + 3) + 14) + 1 ∧ innerLoop.Exec s0 s' t ∧
      ∃ b, s' = Function.update (Function.update (Function.update (Function.update s0
        KO.Jc []) KO.J3 (List.replicate (3 * (i + 1 + m) + 1) mkA))
        KO.NJ (List.replicate (n + 2 + (i + 1 + m)) mkA)) KO.Bd b ∧
      (b = [] ↔ (s0 KO.Bd = [] ∧ ∀ r < m, ovl cl d n i (i + 1 + r))) := by
  have key := exec_for KO.Jc innerBody mkA
    (fun r s => ∃ b, s = Function.update (Function.update (Function.update (Function.update s0
        KO.Jc (List.replicate (m - r) mkA)) KO.J3 (List.replicate (3 * (i + 1 + r) + 1) mkA))
        KO.NJ (List.replicate (n + 2 + (i + 1 + r)) mkA)) KO.Bd b ∧
      (b = [] ↔ (s0 KO.Bd = [] ∧ ∀ r' < r, ovl cl d n i (i + 1 + r'))))
    m (60 * (L + 3) * (L + 3) + 12) ?_ s0 ⟨s0 KO.Bd, ?_, by simp⟩ hJc
  · obtain ⟨s', t, ht, he, b, hs', hb⟩ := key
    refine ⟨s', t, ht, he, b, ?_, hb⟩
    rw [hs']; simp
  · intro r hr s ⟨b, hs, hb⟩ _
    have e1 := exec_pop KO.Jc s
    set s1 := Function.update s KO.Jc (s KO.Jc).tail with hs1
    obtain ⟨m2, hm2, e2⟩ := exec_pairBody s1 cl d (3 * i + 1) (n + 2 + i) (3 * (i + 1 + r) + 1)
      (n + 2 + (i + 1 + r)) L
      (by rw [hs1, hs]; simp [hW0]) (by rw [hs1, hs]; simp [hDD])
      (by rw [hs1, hs]; simp [hI3]) (by rw [hs1, hs]; simp [hNI])
      (by rw [hs1, hs]; simp) (by rw [hs1, hs]; simp)
      (by rw [hs1, hs]; simp [hQ1]) (by rw [hs1, hs]; simp [hQ2]) (by rw [hs1, hs]; simp [hQ3])
      (by rw [hs1, hs]; simp [hFA]) (by rw [hs1, hs]; simp [hFC])
      (by rw [hs1, hs]; simp [hX]) (by rw [hs1, hs]; simp [hE]) (by rw [hs1, hs]; simp [hY])
      (by rw [hs1, hs]; simp [hZ]) (by rw [hs1, hs]; simp [hC1]) (by rw [hs1, hs]; simp [hC2])
      (by rw [hs1, hs]; simp [hSt]) (by rw [hs1, hs]; simp [hsc])
      (by omega) (by omega) hLc hL (by omega) (by omega)
    set s2 := Function.update s1 KO.Bd (if okPair cl d (3 * i + 1) (n + 2 + i)
      (3 * (i + 1 + r) + 1) (n + 2 + (i + 1 + r)) then s1 KO.Bd else mkA :: s1 KO.Bd) with hs2
    have e3 := exec_pushG KO.J3 mkA s2
    have e4 := exec_pushG KO.J3 mkA (Function.update s2 KO.J3 (mkA :: s2 KO.J3))
    have e5 := exec_pushG KO.J3 mkA (Function.update (Function.update s2 KO.J3 (mkA :: s2 KO.J3))
      KO.J3 (mkA :: (Function.update s2 KO.J3 (mkA :: s2 KO.J3)) KO.J3))
    set s5 := Function.update (Function.update (Function.update s2 KO.J3 (mkA :: s2 KO.J3))
      KO.J3 (mkA :: (Function.update s2 KO.J3 (mkA :: s2 KO.J3)) KO.J3)) KO.J3
      (mkA :: (Function.update (Function.update s2 KO.J3 (mkA :: s2 KO.J3))
      KO.J3 (mkA :: (Function.update s2 KO.J3 (mkA :: s2 KO.J3)) KO.J3)) KO.J3) with hs5
    have e6 := exec_pushG KO.NJ mkA s5
    refine ⟨_, _, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3
      (StackProg.Exec.seq e4 (StackProg.Exec.seq e5 e6)))),
      ⟨if ovl cl d n i (i + 1 + r) then b else mkA :: b, ?_, ?_⟩, ?_⟩
    · omega
    · subst hs
      have q1 : 3 * (i + 1 + (r + 1)) + 1 = (3 * (i + 1 + r) + 1) + 1 + 1 + 1 := by ring
      have q2 : n + 2 + (i + 1 + (r + 1)) = n + 2 + (i + 1 + r) + 1 := by ring
      rw [q1, q2]
      funext k
      cases k <;> simp [hs1, hs2, hs5, ovl, Function.update_apply, List.tail_replicate, Nat.sub_sub,
        List.replicate_succ]
    · constructor
      · intro h
        by_cases hok : ovl cl d n i (i + 1 + r)
        · rw [if_pos hok] at h
          obtain ⟨h1, h2⟩ := hb.1 h
          refine ⟨h1, fun r' hr' => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hr' with hr' | rfl
          · exact h2 r' hr'
          · exact hok
        · rw [if_neg hok] at h; simp at h
      · rintro ⟨h1, h2⟩
        rw [if_pos (h2 r (by omega))]
        exact hb.2 ⟨h1, fun r' hr' => h2 r' (by omega)⟩
    · subst hs; simp [hs1, hs2, hs5, Function.update_apply, List.tail_replicate, Nat.sub_sub]
  · funext k; cases k <;> simp [Function.update_apply, hJc, hJ3, hNJ]

/-! ### the outer loop over `i` -/

def outerBody : SP :=
  .seq (popProg KO.Ic) (.seq (copyProg KO.Ic KO.Jc KO.sc) (.seq (copyProg KO.I3 KO.J3 KO.sc)
  (.seq (pushProg KO.J3 mkA) (.seq (pushProg KO.J3 mkA) (.seq (pushProg KO.J3 mkA)
  (.seq (copyProg KO.NI KO.NJ KO.sc) (.seq (pushProg KO.NJ mkA) (.seq innerLoop
  (.seq (clearProg KO.J3) (.seq (clearProg KO.NJ) (.seq (pushProg KO.I3 mkA)
  (.seq (pushProg KO.I3 mkA) (.seq (pushProg KO.I3 mkA) (pushProg KO.NI mkA))))))))))))))

def outerLoop : SP := .loop (fun h => (h KO.Ic).isSome) outerBody

set_option maxHeartbeats 8000000 in
lemma exec_outerLoop (r0 : KO → List A) (cl : List ℤ) (d : List ℕ) (n L : ℕ)
    (hW0 : r0 KO.W0 = toksE ι1 (cl.map digU)) (hDD : r0 KO.DD = toksE ι2 (d.map tokN))
    (hIc : r0 KO.Ic = List.replicate n mkA)
    (hI3 : r0 KO.I3 = List.replicate 1 mkA) (hNI : r0 KO.NI = List.replicate (n + 2) mkA)
    (hJ3 : r0 KO.J3 = []) (hNJ : r0 KO.NJ = []) (hJc : r0 KO.Jc = [])
    (hQ1 : r0 KO.Q1 = []) (hQ2 : r0 KO.Q2 = []) (hQ3 : r0 KO.Q3 = [])
    (hFA : r0 KO.FA = []) (hFC : r0 KO.FC = [])
    (hX : r0 KO.X = []) (hE : r0 KO.E = []) (hY : r0 KO.Y = []) (hZ : r0 KO.Z = [])
    (hC1 : r0 KO.C1 = []) (hC2 : r0 KO.C2 = []) (hSt : r0 KO.St = []) (hsc : r0 KO.sc = [])
    (hd : 3 * n ≤ d.length)
    (hLc : (toksE ι1 (cl.map digU)).length ≤ L) (hL : (toksE ι2 (d.map tokN)).length ≤ L)
    (hnL : 3 * n + 3 ≤ L) :
    ∃ s' t, t ≤ n * (n * (60 * (L + 3) * (L + 3) + 14) + 40 * L + 80) + 1 ∧
      outerLoop.Exec r0 s' t ∧
      ∃ b, s' = Function.update (Function.update (Function.update (Function.update r0
        KO.Ic []) KO.I3 (List.replicate (3 * n + 1) mkA)) KO.NI (List.replicate (n + 2 + n) mkA))
        KO.Bd b ∧
      (b = [] ↔ (r0 KO.Bd = [] ∧ ∀ i < n, ∀ r < n - i - 1, ovl cl d n i (i + 1 + r))) := by
  have key := exec_for KO.Ic outerBody mkA
    (fun t s => ∃ b, s = Function.update (Function.update (Function.update (Function.update r0
        KO.Ic (List.replicate (n - t) mkA)) KO.I3 (List.replicate (3 * t + 1) mkA))
        KO.NI (List.replicate (n + 2 + t) mkA)) KO.Bd b ∧
      (b = [] ↔ (r0 KO.Bd = [] ∧ ∀ i < t, ∀ r < n - i - 1, ovl cl d n i (i + 1 + r))))
    n (n * (60 * (L + 3) * (L + 3) + 14) + 40 * L + 78) ?_ r0 ⟨r0 KO.Bd, ?_, by simp⟩ hIc
  · obtain ⟨s', t, ht, he, b, hs', hb⟩ := key
    refine ⟨s', t, ht, he, b, ?_, hb⟩
    rw [hs']; simp
  · intro t ht s ⟨b, hs, hb⟩ _
    have e1 := exec_pop KO.Ic s
    set s1 := Function.update s KO.Ic (s KO.Ic).tail with hs1
    obtain ⟨m2, hm2, e2⟩ := exec_copy KO.Ic KO.Jc KO.sc (by decide) (by decide) (by decide) s1
      (by rw [hs1, hs]; simp [hsc])
    set s2 := Function.update s1 KO.Jc (s1 KO.Ic ++ s1 KO.Jc) with hs2
    obtain ⟨m3, hm3, e3⟩ := exec_copy KO.I3 KO.J3 KO.sc (by decide) (by decide) (by decide) s2
      (by rw [hs2, hs1, hs]; simp [hsc])
    set s3 := Function.update s2 KO.J3 (s2 KO.I3 ++ s2 KO.J3) with hs3
    have e4 := exec_pushG KO.J3 mkA s3
    set s4 := Function.update s3 KO.J3 (mkA :: s3 KO.J3) with hs4
    have e5 := exec_pushG KO.J3 mkA s4
    set s5 := Function.update s4 KO.J3 (mkA :: s4 KO.J3) with hs5
    have e6 := exec_pushG KO.J3 mkA s5
    set s6 := Function.update s5 KO.J3 (mkA :: s5 KO.J3) with hs6
    obtain ⟨m7, hm7, e7⟩ := exec_copy KO.NI KO.NJ KO.sc (by decide) (by decide) (by decide) s6
      (by rw [hs6, hs5, hs4, hs3, hs2, hs1, hs]; simp [hsc])
    set s7 := Function.update s6 KO.NJ (s6 KO.NI ++ s6 KO.NJ) with hs7
    have e8 := exec_pushG KO.NJ mkA s7
    set s8 := Function.update s7 KO.NJ (mkA :: s7 KO.NJ) with hs8
    have hS : ∀ k, k ≠ KO.Ic → k ≠ KO.I3 → k ≠ KO.NI → k ≠ KO.Bd → k ≠ KO.Jc → k ≠ KO.J3 →
        k ≠ KO.NJ → s8 k = r0 k := by
      intro k h1 h2 h3 h4 h5 h6 h7
      rw [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, hs]; simp [h1, h2, h3, h4, h5, h6, h7]
    obtain ⟨s9, m9, hm9, e9, b', hs9, hb'⟩ := exec_innerLoop s8 cl d n t (n - t - 1) L
      (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]; exact hW0)
      (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]; exact hDD)
      (by rw [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, hs]; simp)
      (by rw [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, hs]; simp)
      (by rw [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, hs]
          simp [hJ3, List.replicate_succ, show 3 * (t + 1) + 1 = 3 * t + 1 + 1 + 1 + 1 by ring])
      (by rw [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, hs]
          simp [hNJ, List.replicate_succ, show n + 2 + (t + 1) = n + 2 + t + 1 by ring])
      (by rw [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, hs]
          simp [hJc, List.tail_replicate, Nat.sub_sub])
      (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]; exact hQ1)
      (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]; exact hQ2)
      (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]; exact hQ3)
      (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]; exact hFA)
      (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]; exact hFC)
      (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]; exact hX)
      (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]; exact hE)
      (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]; exact hY)
      (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]; exact hZ)
      (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]; exact hC1)
      (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]; exact hC2)
      (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]; exact hSt)
      (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]; exact hsc)
      (by omega) hd hLc hL (by omega)
    obtain ⟨m10, hm10, e10⟩ := exec_clearG KO.J3 s9
    obtain ⟨m11, hm11, e11⟩ := exec_clearG KO.NJ (Function.update s9 KO.J3 [])
    set s11 := Function.update (Function.update s9 KO.J3 []) KO.NJ [] with hs11
    have e12 := exec_pushG KO.I3 mkA s11
    set s12 := Function.update s11 KO.I3 (mkA :: s11 KO.I3) with hs12
    have e13 := exec_pushG KO.I3 mkA s12
    set s13 := Function.update s12 KO.I3 (mkA :: s12 KO.I3) with hs13
    have e14 := exec_pushG KO.I3 mkA s13
    set s14 := Function.update s13 KO.I3 (mkA :: s13 KO.I3) with hs14
    have e15 := exec_pushG KO.NI mkA s14
    have hm2' : m2 ≤ 6 * n + 3 := by
      rw [hs1, hs] at hm2; simp at hm2; omega
    have hm3' : m3 ≤ 6 * L + 3 := by
      rw [hs2, hs1, hs] at hm3; simp at hm3; omega
    have hm7' : m7 ≤ 6 * L + 3 := by
      rw [hs6, hs5, hs4, hs3, hs2, hs1, hs] at hm7; simp at hm7; omega
    have hm10' : m10 ≤ 3 * L + 4 := by
      rw [hs9] at hm10; simp at hm10; omega
    have hm11' : m11 ≤ 3 * L + 4 := by
      rw [hs9] at hm11; simp at hm11; omega
    have hm9' : m9 ≤ n * (60 * (L + 3) * (L + 3) + 14) + 1 := by
      have : (n - t - 1) * (60 * (L + 3) * (L + 3) + 14) ≤ n * (60 * (L + 3) * (L + 3) + 14) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    refine ⟨_, _, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3
      (StackProg.Exec.seq e4 (StackProg.Exec.seq e5 (StackProg.Exec.seq e6 (StackProg.Exec.seq e7
      (StackProg.Exec.seq e8 (StackProg.Exec.seq e9 (StackProg.Exec.seq e10
      (StackProg.Exec.seq e11 (StackProg.Exec.seq e12 (StackProg.Exec.seq e13
      (StackProg.Exec.seq e14 e15))))))))))))), ⟨b', ?_, ?_⟩, ?_⟩
    · clear * - hm2' hm3' hm7' hm10' hm11' hm9' hnL
      omega
    · have q1 : 3 * (t + 1) + 1 = 3 * t + 1 + 1 + 1 + 1 := by ring
      have q2 : n + 2 + (t + 1) = n + 2 + t + 1 := by ring
      rw [q1, q2, hs14, hs13, hs12, hs11, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, hs]
      funext k
      cases k <;> simp [Function.update_apply, List.tail_replicate, Nat.sub_sub, hJ3, hNJ, hJc,
        List.replicate_succ]
    · have hBd : s8 KO.Bd = b := by rw [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, hs]; simp
      rw [hBd] at hb'
      rw [hb']
      constructor
      · rintro ⟨h0, h1⟩
        obtain ⟨h2, h3⟩ := hb.1 h0
        refine ⟨h2, fun i hi r hr => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact h3 i hi r hr
        · exact h1 r hr
      · rintro ⟨h2, h3⟩
        exact ⟨hb.2 ⟨h2, fun i hi r hr => h3 i (by omega) r hr⟩, fun r hr => h3 t (by omega) r hr⟩
    · rw [hs14, hs13, hs12, hs11, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, hs]
      simp [Function.update_apply, List.tail_replicate, Nat.sub_sub]
  · funext k; cases k <;> simp [Function.update_apply, hIc, hI3, hNI]

/-! ### the phase after a successful shape scan -/

def phaseO : SP :=
  .seq (transferProg KO.kC (fun k => decide (k = KO.W0)))
  (.seq (transferProg KO.kD (fun k => decide (k = KO.DD)))
  (.seq (pushProg KO.kd mkA) (.seq (pushProg KO.Np mkA) (.seq (pushProg KO.Np mkA)
  (.seq (pushProg KO.Np mkA) (.seq (divLoop KO.kd KO.Np KO.Y0 KO.N KO.Bd0 KO.sc mkA)
  (.seq (popProg KO.N)
  (.seq (copyProg KO.N KO.Ic KO.sc) (.seq (pushProg KO.I3 mkA)
  (.seq (copyProg KO.N KO.NI KO.sc) (.seq (pushProg KO.NI mkA) (.seq (pushProg KO.NI mkA)
  (.seq outerLoop (.branch (fun h => (h KO.Bd).isNone) skipP (clearProg KO.ko)))))))))))))))

/-- the non-overlap condition of the filter, indexed with `N := |d| / 3`. -/
def Gov (cl : List ℤ) (d : List ℕ) : Prop :=
  ∀ i < d.length / 3, ∀ j < d.length / 3, i < j →
    d.getD (3 * i + 1) 0 + 2 * (cl.getD (2 + d.length / 3 + i) 0).natAbs ≤ d.getD (3 * j + 1) 0 ∨
      d.getD (3 * j + 1) 0 + 2 * (cl.getD (2 + d.length / 3 + j) 0).natAbs ≤ d.getD (3 * i + 1) 0

lemma gov_iff (cl : List ℤ) (d : List ℕ) :
    Gov cl d ↔ ∀ i < d.length / 3, ∀ r < d.length / 3 - i - 1,
      ovl cl d (d.length / 3) i (i + 1 + r) := by
  unfold Gov ovl okPair
  constructor
  · intro h i hi r hr
    have := h i hi (i + 1 + r) (by omega) (by omega)
    rw [show d.length / 3 + 2 + i = 2 + d.length / 3 + i by ring,
      show d.length / 3 + 2 + (i + 1 + r) = 2 + d.length / 3 + (i + 1 + r) by ring]
    exact this
  · intro h i hi j hj hij
    obtain ⟨r, rfl⟩ : ∃ r, j = i + 1 + r := ⟨j - i - 1, by omega⟩
    have := h i hi r (by omega)
    rw [show d.length / 3 + 2 + i = 2 + d.length / 3 + i by ring,
      show d.length / 3 + 2 + (i + 1 + r) = 2 + d.length / 3 + (i + 1 + r) by ring] at this
    exact this

set_option maxHeartbeats 8000000 in
lemma exec_phaseO (s : KO → List A) (c : List ℤ) (d : List ℕ) (L : ℕ)
    (hkC : s KO.kC = ((encInts c).map ι1).reverse) (hkD : s KO.kD = ((encNats d).map ι2).reverse)
    (hkd : s KO.kd = List.replicate d.length mkA)
    (hW0 : s KO.W0 = []) (hDD : s KO.DD = []) (hN : s KO.N = []) (hNp : s KO.Np = [])
    (hY0 : s KO.Y0 = []) (hBd0 : s KO.Bd0 = []) (hIc : s KO.Ic = []) (hJc : s KO.Jc = [])
    (hI3 : s KO.I3 = []) (hNI : s KO.NI = []) (hJ3 : s KO.J3 = []) (hNJ : s KO.NJ = [])
    (hQ1 : s KO.Q1 = []) (hQ2 : s KO.Q2 = []) (hQ3 : s KO.Q3 = [])
    (hFA : s KO.FA = []) (hFC : s KO.FC = [])
    (hX : s KO.X = []) (hE : s KO.E = []) (hY : s KO.Y = []) (hZ : s KO.Z = [])
    (hC1 : s KO.C1 = []) (hC2 : s KO.C2 = []) (hSt : s KO.St = []) (hsc : s KO.sc = [])
    (hBd : s KO.Bd = [])
    (hLc : (encInts c).length ≤ L) (hLd : (encNats d).length ≤ L) (hdl : d.length ≤ L)
    (hko : (s KO.ko).length ≤ L) :
    ∃ t m, m ≤ 2000 * ((3 * L + 4) * (3 * L + 4) * (3 * L + 4) * (3 * L + 4)) ∧
      phaseO.Exec s t m ∧
      (Gov c d → t KO.ko = s KO.ko) ∧ (¬Gov c d → t KO.ko = []) := by
  set n := d.length / 3 with hn
  have hTC : (encInts c).map ι1 = toksE ι1 (c.map digU) := encInts_toks c
  have hTD : (encNats d).map ι2 = toksE ι2 (d.map tokN) := encNats_toks ι2 d
  have hlc : (toksE ι1 (c.map digU)).length ≤ L := by rw [← hTC]; simpa using hLc
  have hld : (toksE ι2 (d.map tokN)).length ≤ L := by rw [← hTD]; simpa using hLd
  obtain ⟨m1, hm1, e1⟩ := exec_transfer KO.kC (fun k => decide (k = KO.W0)) _ s rfl
  set s1 := Function.update (Function.update s KO.kC []) KO.W0 (toksE ι1 (c.map digU)) with hs1
  have e1' := exec_congr e1 (t' := s1)
    (by funext k; cases k <;> simp [hs1, transferStore, Function.update_apply, hkC, hW0, hTC])
  obtain ⟨m2, hm2, e2⟩ := exec_transfer KO.kD (fun k => decide (k = KO.DD)) _ s1 rfl
  set s2 := Function.update (Function.update s1 KO.kD []) KO.DD (toksE ι2 (d.map tokN)) with hs2
  have e2' := exec_congr e2 (t' := s2)
    (by funext k; cases k <;> simp [hs1, hs2, transferStore, Function.update_apply, hkD, hDD, hTD])
  have e3 := exec_pushG KO.kd mkA s2
  set s3 := Function.update s2 KO.kd (mkA :: s2 KO.kd) with hs3
  have e4 := exec_pushG KO.Np mkA s3
  set s4 := Function.update s3 KO.Np (mkA :: s3 KO.Np) with hs4
  have e5 := exec_pushG KO.Np mkA s4
  set s5 := Function.update s4 KO.Np (mkA :: s4 KO.Np) with hs5
  have e6 := exec_pushG KO.Np mkA s5
  set s6 := Function.update s5 KO.Np (mkA :: s5 KO.Np) with hs6
  obtain ⟨m7, hm7, e7⟩ := exec_div KO.kd KO.Np KO.Y0 KO.N KO.Bd0 KO.sc
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) mkA 3 (by norm_num) (d.length + 1) s6
    (by simp [hs6, hs5, hs4, hs3, hs2, hs1, hkd, List.replicate_succ])
    (by simp [hs6, hs5, hs4, hs3, hs2, hs1, hNp])
    (by simp [hs6, hs5, hs4, hs3, hs2, hs1, hY0])
    (by simp [hs6, hs5, hs4, hs3, hs2, hs1, hsc])
  set s7 := divPost KO.kd KO.N KO.Bd0 mkA s6 (d.length + 1) 3 with hs7
  have hs7N : s7 KO.N = List.replicate (n + 1) mkA := by
    simp [hs7, divPost, hs6, hs5, hs4, hs3, hs2, hs1, hN]; omega
  have e8 := exec_pop KO.N s7
  set s8 := Function.update s7 KO.N (s7 KO.N).tail with hs8
  have hs8N : s8 KO.N = List.replicate n mkA := by
    simp [hs8, hs7N, List.replicate_succ]
  obtain ⟨m9, hm9, e9⟩ := exec_copy KO.N KO.Ic KO.sc (by decide) (by decide) (by decide) s8
    (by simp [hs8, hs7, divPost, hs6, hs5, hs4, hs3, hs2, hs1, hsc])
  set s9 := Function.update s8 KO.Ic (s8 KO.N ++ s8 KO.Ic) with hs9
  have e10 := exec_pushG KO.I3 mkA s9
  set s10 := Function.update s9 KO.I3 (mkA :: s9 KO.I3) with hs10
  obtain ⟨m11, hm11, e11⟩ := exec_copy KO.N KO.NI KO.sc (by decide) (by decide) (by decide) s10
    (by simp [hs10, hs9, hs8, hs7, divPost, hs6, hs5, hs4, hs3, hs2, hs1, hsc])
  set s11 := Function.update s10 KO.NI (s10 KO.N ++ s10 KO.NI) with hs11
  have e12 := exec_pushG KO.NI mkA s11
  set s12 := Function.update s11 KO.NI (mkA :: s11 KO.NI) with hs12
  have e13 := exec_pushG KO.NI mkA s12
  set s13 := Function.update s12 KO.NI (mkA :: s12 KO.NI) with hs13
  have hdn : 3 * n ≤ d.length := by omega
  have hS : ∀ k, k ≠ KO.kC → k ≠ KO.W0 → k ≠ KO.kD → k ≠ KO.DD → k ≠ KO.kd → k ≠ KO.Np →
      k ≠ KO.N → k ≠ KO.Bd0 → k ≠ KO.Ic → k ≠ KO.I3 → k ≠ KO.NI → s13 k = s k := by
    intro k h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    simp [hs13, hs12, hs11, hs10, hs9, hs8, hs7, divPost, hs6, hs5, hs4, hs3, hs2, hs1,
      h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  obtain ⟨s14, m14, hm14, e14, b, hs14, hb⟩ := exec_outerLoop s13 c d n (3 * L + 3)
    (by simp [hs13, hs12, hs11, hs10, hs9, hs8, hs7, divPost, hs6, hs5, hs4, hs3, hs2, hs1])
    (by simp [hs13, hs12, hs11, hs10, hs9, hs8, hs7, divPost, hs6, hs5, hs4, hs3, hs2, hs1])
    (by simp [hs13, hs12, hs11, hs10, hs9, hs8N, hs8, hs7, divPost, hs6, hs5, hs4, hs3, hs2, hs1,
      hIc, hN, hn])
    (by simp [hs13, hs12, hs11, hs10, hs9, hs8, hs7, divPost, hs6, hs5, hs4, hs3, hs2, hs1, hI3])
    (by
      have : s10 KO.N = List.replicate n mkA := by simp [hs10, hs9, hs8N]
      simp only [hs13, hs12, hs11, Function.update_self, this]
      have h0 : s10 KO.NI = [] := by
        simp [hs10, hs9, hs8, hs7, divPost, hs6, hs5, hs4, hs3, hs2, hs1, hNI]
      rw [h0]; simp [List.replicate_succ])
    (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hJ3)
    (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hNJ)
    (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hJc)
    (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hQ1)
    (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hQ2)
    (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hQ3)
    (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hFA)
    (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hFC)
    (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hX)
    (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hE)
    (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hY)
    (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hZ)
    (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hC1)
    (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hC2)
    (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hSt)
    (by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hsc)
    hdn (by omega) (by omega) (by omega)
  have hko14 : s14 KO.ko = s KO.ko := by
    rw [hs14]; simp only [Function.update_apply]; simp
    exact hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hBd13 : s13 KO.Bd = [] := by
    rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hBd
  rw [hBd13] at hb
  have hG : Gov c d ↔ b = [] := by
    rw [gov_iff, hb]; simp [hn]
  -- bounds
  have hm1' : m1 ≤ 3 * L + 1 := by simp [hkC] at hm1; omega
  have hm2' : m2 ≤ 3 * L + 1 := by simp [hs1, hkD] at hm2; omega
  have hm7' : m7 ≤ (L + 1) * 48 + 1 := by
    have : (d.length + 1) * (12 * 3 + 12) ≤ (L + 1) * 48 := Nat.mul_le_mul_right _ (by omega)
    omega
  have hm9' : m9 ≤ 6 * L + 3 := by rw [hs8N] at hm9; simp at hm9; omega
  have hm11' : m11 ≤ 6 * L + 3 := by
    have : s10 KO.N = List.replicate n mkA := by simp [hs10, hs9, hs8N]
    rw [this] at hm11; simp at hm11; omega
  have hnL : n ≤ 3 * L + 3 := by omega
  have hob : m14 ≤ 1000 * ((3 * L + 4) * (3 * L + 4) * (3 * L + 4) * (3 * L + 4)) := by
    have e : 3 * L + 3 + 3 = 3 * L + 6 := by ring
    rw [e] at hm14
    have h1 : n * (60 * (3 * L + 6) * (3 * L + 6) + 14) ≤
        (3 * L + 4) * (60 * (3 * L + 6) * (3 * L + 6) + 14) := Nat.mul_le_mul_right _ (by omega)
    have h2 : n * (n * (60 * (3 * L + 6) * (3 * L + 6) + 14) + 40 * (3 * L + 3) + 80) ≤
        (3 * L + 4) * ((3 * L + 4) * (60 * (3 * L + 6) * (3 * L + 6) + 14) +
          40 * (3 * L + 3) + 80) :=
      Nat.mul_le_mul (by omega) (Nat.add_le_add_right (Nat.add_le_add_right h1 _) _)
    have h3 := bndC L
    clear * - h1 h2 h3 hm14
    omega
  have hP4 : 3 * L + 4 ≤ (3 * L + 4) * (3 * L + 4) * (3 * L + 4) * (3 * L + 4) := by
    have h1 : 1 ≤ (3 * L + 4) * (3 * L + 4) * (3 * L + 4) := Nat.one_le_iff_ne_zero.2 (by positivity)
    calc 3 * L + 4 = 1 * (3 * L + 4) := (one_mul _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ h1
  by_cases hbe : b = []
  · have e15 := exec_skipP (K := KO) s14
    refine ⟨s14, _, ?_, StackProg.Exec.seq e1' (StackProg.Exec.seq e2' (StackProg.Exec.seq e3
      (StackProg.Exec.seq e4 (StackProg.Exec.seq e5 (StackProg.Exec.seq e6 (StackProg.Exec.seq e7
      (StackProg.Exec.seq e8 (StackProg.Exec.seq e9 (StackProg.Exec.seq e10
      (StackProg.Exec.seq e11 (StackProg.Exec.seq e12 (StackProg.Exec.seq e13
      (StackProg.Exec.seq e14
        (StackProg.Exec.branchTrue (by rw [hs14]; simp [hbe]) e15)))))))))))))),
      fun _ => hko14, ?_⟩
    · clear * - hm1' hm2' hm7' hm9' hm11' hob hP4
      omega
    · intro hg; exact absurd (hG.2 hbe) hg
  · obtain ⟨m15, hm15, e15⟩ := exec_clearG KO.ko s14
    obtain ⟨x, l, hxl⟩ := List.exists_cons_of_ne_nil hbe
    refine ⟨_, _, ?_, StackProg.Exec.seq e1' (StackProg.Exec.seq e2' (StackProg.Exec.seq e3
      (StackProg.Exec.seq e4 (StackProg.Exec.seq e5 (StackProg.Exec.seq e6 (StackProg.Exec.seq e7
      (StackProg.Exec.seq e8 (StackProg.Exec.seq e9 (StackProg.Exec.seq e10
      (StackProg.Exec.seq e11 (StackProg.Exec.seq e12 (StackProg.Exec.seq e13
      (StackProg.Exec.seq e14
        (StackProg.Exec.branchFalse (by rw [hs14]; simp [hxl]) e15)))))))))))))), ?_,
      fun _ => by simp⟩
    · rw [hko14] at hm15
      clear * - hm1' hm2' hm7' hm9' hm11' hob hP4 hm15 hko
      omega
    · intro hg; exact absurd (hG.1 hg) hbe

/-! ### the whole program -/

lemma encNats_eq_encInts (d : List ℕ) : encNats d = encInts (d.map (fun k : ℕ => (k : ℤ))) := by
  induction d with
  | nil => simp [encNats, encInts]
  | cons k d ih =>
    rw [encNats_cons, List.map_cons, encInts_cons, ih]
    congr 1

lemma map_ι1_inj {l l' : List BSym} (h : l.map ι1 = l'.map ι1) : l = l' :=
  List.map_injective_iff.mpr ι1_inj h

lemma map_ι2_inj {l l' : List BSym} (h : l.map ι2 = l'.map ι2) : l = l' :=
  List.map_injective_iff.mpr ι2_inj h

lemma encNats_inj {d d' : List ℕ} (h : encNats d = encNats d') : d = d' := by
  rw [encNats_eq_encInts, encNats_eq_encInts] at h
  have := encInts_inj _ _ h
  exact List.map_injective_iff.mpr (fun a b hab => by exact_mod_cast hab) this

def mainProg : SP := .seq (copyProg KO.ki KO.ko KO.sc)
  (.seq (scanProg KO.ki KO.st δA (outA KO.kc KO.kd KO.kC KO.kD))
    (.branch (fun h => decide (h KO.st = some (dsA DS.T0))) phaseO skipP))

set_option maxHeartbeats 8000000 in
theorem mainT (u : List A) : ∃ t n, n ≤ 4000 * ((3 * u.length + 4) * (3 * u.length + 4) *
      (3 * u.length + 4) * (3 * u.length + 4)) ∧
    mainProg.Exec (fun j => if j = KO.ki then u else []) t n ∧
    ((∃ c d, u = Ew c d ∧ ¬Gov c d) → t KO.ko = []) ∧
    (¬(∃ c d, u = Ew c d ∧ ¬Gov c d) → t KO.ko = u) := by
  obtain ⟨n1, hn1, e1⟩ := exec_copy KO.ki KO.ko KO.sc (by decide) (by decide) (by decide)
    (fun j => if j = KO.ki then u else []) (by simp)
  have hn1' : n1 ≤ 6 * u.length + 3 := by simpa using hn1
  have e1' := exec_congr e1 (t' := fun j => if j = KO.ki ∨ j = KO.ko then u else [])
    (by funext k; cases k <;> simp [Function.update_apply])
  set s1 : KO → List A := fun j => if j = KO.ki ∨ j = KO.ko then u else [] with hs1
  obtain ⟨e2, hiff, hcont, hoth⟩ := scanA_result KO.ki KO.st KO.kc KO.kd KO.kC KO.kD
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) u s1 (by simp [hs1]) (by simp [hs1]) (by simp [hs1]) (by simp [hs1])
    (by simp [hs1]) (by simp [hs1])
  set s2 := scanRun KO.ki KO.st δA (outA KO.kc KO.kd KO.kC KO.kD) u s1 with hs2
  have hko2 : s2 KO.ko = u := by
    rw [hoth KO.ko (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [hs1]
  have hemp : ∀ k, k ≠ KO.ki → k ≠ KO.st → k ≠ KO.kc → k ≠ KO.kd → k ≠ KO.kC → k ≠ KO.kD →
      k ≠ KO.ko → s2 k = [] := by
    intro k h0 h1 h2 h3 h4 h5 h6
    rw [hoth k h0 h1 h2 h3 h4 h5]; simp [hs1, h0, h6]
  have hpow : 3 * u.length + 4 ≤ (3 * u.length + 4) * (3 * u.length + 4) * (3 * u.length + 4) *
      (3 * u.length + 4) := by
    have h2 : 1 ≤ (3 * u.length + 4) * (3 * u.length + 4) * (3 * u.length + 4) :=
      Nat.one_le_iff_ne_zero.2 (by positivity)
    calc 3 * u.length + 4 = 1 * (3 * u.length + 4) := (one_mul _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ h2
  by_cases hsh : ∃ c d, u = Ew c d
  · obtain ⟨c, d, hu⟩ := hsh
    obtain ⟨hkc, hkd, hkC, hkD⟩ := hcont c d hu
    have hlen : (encInts c).length + 1 + (encNats d).length = u.length := by
      rw [hu]; simp [Ew]; omega
    have hd1 := len_encNats' d
    have hst : decide ((s2 KO.st).head? = some (dsA DS.T0)) = true :=
      decide_eq_true (hiff.2 ⟨c, d, hu⟩)
    have he : ∀ k, k ≠ KO.ki ∧ k ≠ KO.st ∧ k ≠ KO.kc ∧ k ≠ KO.kd ∧ k ≠ KO.kC ∧ k ≠ KO.kD ∧
        k ≠ KO.ko → s2 k = [] := fun k ⟨h0, h1, h2, h3, h4, h5, h6⟩ => hemp k h0 h1 h2 h3 h4 h5 h6
    obtain ⟨t, m, hm, he, hg1, hg2⟩ := exec_phaseO s2 c d u.length hkC hkD hkd
      (he _ (by decide)) (he _ (by decide)) (he _ (by decide)) (he _ (by decide))
      (he _ (by decide)) (he _ (by decide)) (he _ (by decide)) (he _ (by decide))
      (he _ (by decide)) (he _ (by decide)) (he _ (by decide)) (he _ (by decide))
      (he _ (by decide)) (he _ (by decide)) (he _ (by decide)) (he _ (by decide))
      (he _ (by decide)) (he _ (by decide)) (he _ (by decide)) (he _ (by decide))
      (he _ (by decide)) (he _ (by decide)) (he _ (by decide)) (he _ (by decide))
      (he _ (by decide)) (he _ (by decide))
      (by omega) (by omega) (by omega) (by rw [hko2])
    have key : (∃ c0 d0, u = Ew c0 d0 ∧ ¬Gov c0 d0) ↔ ¬Gov c d := by
      constructor
      · rintro ⟨c0, d0, hu0, hg0⟩
        obtain ⟨-, -, hkC0, hkD0⟩ := hcont c0 d0 hu0
        have hcc : c0 = c :=
          encInts_inj _ _ (map_ι1_inj (List.reverse_inj.1 (hkC0.symm.trans hkC)))
        have hdd : d0 = d := encNats_inj (map_ι2_inj (List.reverse_inj.1 (hkD0.symm.trans hkD)))
        rw [← hcc, ← hdd]; exact hg0
      · intro h; exact ⟨c, d, hu, h⟩
    refine ⟨t, n1 + 1 + (3 * u.length + 1 + 1 + (1 + m)), ?_,
      StackProg.Exec.seq e1' (StackProg.Exec.seq e2 (StackProg.Exec.branchTrue hst he)), ?_, ?_⟩
    · clear * - hm hn1' hpow
      omega
    · intro h; exact hg2 (key.1 h)
    · intro h; rw [hg1 (by by_contra hg; exact h (key.2 hg)), hko2]
  · have hst : decide ((s2 KO.st).head? = some (dsA DS.T0)) = false :=
      decide_eq_false (fun h => hsh (hiff.1 h))
    have e3 := exec_skipP (K := KO) s2
    refine ⟨_, n1 + 1 + (3 * u.length + 1 + 1 + (1 + 1)), by omega,
      StackProg.Exec.seq e1' (StackProg.Exec.seq e2 (StackProg.Exec.branchFalse hst e3)), ?_, ?_⟩
    · rintro ⟨c, d, hu, -⟩; exact absurd ⟨c, d, hu⟩ hsh
    · intro _; exact hko2

theorem poly_gen (c d : ℕ) : ∃ K, ∀ n : ℕ, c * (n + 1) ^ d ≤ n ^ K + K := by
  refine ⟨c * (c * 2 ^ d + 1) ^ d + d + 1, fun n => ?_⟩
  by_cases hn : n ≤ c * 2 ^ d
  · have h1 : c * (n + 1) ^ d ≤ c * (c * 2 ^ d + 1) ^ d :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    omega
  · push Not at hn
    have hn1 : 1 ≤ n := by omega
    have h2 : (n + 1) ^ d ≤ (2 * n) ^ d := Nat.pow_le_pow_left (by omega) _
    have h3 : c * (n + 1) ^ d ≤ c * 2 ^ d * n ^ d := by
      calc c * (n + 1) ^ d ≤ c * (2 * n) ^ d := Nat.mul_le_mul_left _ h2
        _ = c * 2 ^ d * n ^ d := by rw [mul_pow, mul_assoc]
    have h4 : c * 2 ^ d * n ^ d ≤ n * n ^ d := Nat.mul_le_mul_right _ hn.le
    have h5 : n * n ^ d = n ^ (d + 1) := by ring
    have h6 : n ^ (d + 1) ≤ n ^ (c * (c * 2 ^ d + 1) ^ d + d + 1) :=
      Nat.pow_le_pow_right hn1 (by omega)
    omega

theorem E_ovl : ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K)
    (p : StackProg K (Option (BSym ⊕ BSym))) (ki ko : K) (k : ℕ), ∀ u,
    ∃ s n, n ≤ u.length ^ k + k ∧ p.Exec (fun j => if j = ki then u else []) s n ∧
      ((∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          ¬(∀ i < d.length / 3, ∀ j < d.length / 3, i < j →
            d.getD (3 * i + 1) 0 + 2 * (c.getD (2 + d.length / 3 + i) 0).natAbs ≤
                d.getD (3 * j + 1) 0 ∨
              d.getD (3 * j + 1) 0 + 2 * (c.getD (2 + d.length / 3 + j) 0).natAbs ≤
                d.getD (3 * i + 1) 0)) → s ko = []) ∧
      (¬(∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          ¬(∀ i < d.length / 3, ∀ j < d.length / 3, i < j →
            d.getD (3 * i + 1) 0 + 2 * (c.getD (2 + d.length / 3 + i) 0).natAbs ≤
                d.getD (3 * j + 1) 0 ∨
              d.getD (3 * j + 1) 0 + 2 * (c.getD (2 + d.length / 3 + j) 0).natAbs ≤
                d.getD (3 * i + 1) 0)) → s ko = u) := by
  obtain ⟨K, hK⟩ := poly_gen 1024000 4
  refine ⟨KO, inferInstance, inferInstance, mainProg, KO.ki, KO.ko, K, fun u => ?_⟩
  obtain ⟨t, n, hn, he, h1, h2⟩ := mainT u
  refine ⟨t, n, ?_, he, h1, h2⟩
  have h : 3 * u.length + 4 ≤ 4 * (u.length + 1) := by omega
  have hb : (3 * u.length + 4) * (3 * u.length + 4) * (3 * u.length + 4) * (3 * u.length + 4) ≤
      (4 * (u.length + 1)) * (4 * (u.length + 1)) * (4 * (u.length + 1)) * (4 * (u.length + 1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h h) h) h
  have he' : (4 * (u.length + 1)) * (4 * (u.length + 1)) * (4 * (u.length + 1)) *
      (4 * (u.length + 1)) = 256 * (u.length + 1) ^ 4 := by ring
  have := hK u.length
  clear * - hn hb he' this
  omega

end OvlB

theorem solution : ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K)
    (p : StackProg K (Option (BSym ⊕ BSym))) (ki ko : K) (k : ℕ), ∀ u,
    ∃ s n, n ≤ u.length ^ k + k ∧ p.Exec (fun j => if j = ki then u else []) s n ∧
      ((∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          ¬(∀ i < d.length / 3, ∀ j < d.length / 3, i < j →
            d.getD (3 * i + 1) 0 + 2 * (c.getD (2 + d.length / 3 + i) 0).natAbs ≤
                d.getD (3 * j + 1) 0 ∨
              d.getD (3 * j + 1) 0 + 2 * (c.getD (2 + d.length / 3 + j) 0).natAbs ≤
                d.getD (3 * i + 1) 0)) → s ko = []) ∧
      (¬(∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          ¬(∀ i < d.length / 3, ∀ j < d.length / 3, i < j →
            d.getD (3 * i + 1) 0 + 2 * (c.getD (2 + d.length / 3 + i) 0).natAbs ≤
                d.getD (3 * j + 1) 0 ∨
              d.getD (3 * j + 1) 0 + 2 * (c.getD (2 + d.length / 3 + j) 0).natAbs ≤
                d.getD (3 * i + 1) 0)) → s ko = u) :=
  OvlB.E_ovl
