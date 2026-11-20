-- Prove2me | solution 1 for DeletionHash.MixedEdit.count_generating_sets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:12:18.244598+00:00
-- url     : https://prove2.me/submissions/bc0a07d0-0982-45ed-9752-bc3e5bf03ceb

import Definitions.Def_DeletionHash_MixedEdit_Bubbles
import Definitions.Def_DeletionHash_MixedEdit_Generation
import Definitions.Def_DeletionHash_MixedEdit_Paths
import Definitions.Def_DeletionHash_MixedEdit_Regime
import Definitions.Def_DeletionHash_MixedEdit_SupportComponents
import Definitions.Def_DeletionHash_MixedEdit_UniqueWords
import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

-- Source module: RecoveryTransfer
namespace DeletionGeneralization.RecoveryTransfer
universe u
variable {α : Type u}

/-- The positive path obtained by replacing a known block of the negative path. -/
def splice (p : ℕ → α) (ell removed inserted : ℕ) (v : Fin inserted → α) (i : ℕ) : α :=
  if hleft : i < ell then p i
  else if h : i < ell+inserted then v ⟨i-ell, by omega⟩
  else p (i+removed-inserted)

/-- Move a positive k-seed to a negative k-seed; a crossing seed starts before the edit. -/
def seedOffset (ell removed inserted a k : ℕ) : ℕ :=
  if a+k ≤ ell then a
  else if ell+inserted ≤ a then a+removed-inserted
  else min a ell

theorem coverage (ell removed inserted a k b j : ℕ)
    (hv : inserted ≤ b) (hb : b ≤ k) (hj : j < k) :
    let d := seedOffset ell removed inserted a k
    let z := d+j
    (z < ell ∧ a ≤ z ∧ z < a+k) ∨
    (ell ≤ z ∧ z < ell+removed) ∨
    (ell+removed ≤ z ∧ a ≤ z+inserted-removed ∧ z+inserted-removed < a+k) ∨
    (d+k-b ≤ z ∧ z < d+k) := by
  dsimp only
  unfold seedOffset
  split_ifs with hbefore hafter
  · left
    omega
  · right; right; left
    omega
  · have hmin1 := min_le_left a ell
    have hmin2 := min_le_right a ell
    have hmin : min a ell=a ∨ min a ell=ell := min_choice a ell
    omega

theorem seed_in_bounds (ell removed inserted right a k : ℕ)
    (hright : k ≤ right) (ha : a+k ≤ ell+inserted+right) :
    seedOffset ell removed inserted a k+k ≤ ell+removed+right := by
  unfold seedOffset
  split_ifs with hbefore hafter
  · omega
  · omega
  · have h := min_le_right a ell
    omega

theorem transfer_agreement (p p' : ℕ → α) (ell removed inserted a k b : ℕ)
    (v : Fin inserted → α) (hv : inserted ≤ b) (hb : b ≤ k)
    (hremoved : ∀ i, i < removed → p (ell+i)=p' (ell+i))
    (hpositive : ∀ i, i < k →
      splice p ell removed inserted v (a+i)=splice p' ell removed inserted v (a+i))
    (hextra : ∀ i, i < b →
      p (seedOffset ell removed inserted a k+k-b+i)=
      p' (seedOffset ell removed inserted a k+k-b+i)) :
    ∀ i, i < k → p (seedOffset ell removed inserted a k+i)=
      p' (seedOffset ell removed inserted a k+i) := by
  intro i hi
  let d := seedOffset ell removed inserted a k
  change p (d+i)=p' (d+i)
  rcases coverage ell removed inserted a k b i hv hb hi with hpre | hmid | hpost | hend
  · have hz : a+(d+i-a)=d+i := by omega
    have h := hpositive (d+i-a) (by omega)
    rw [hz] at h
    simpa only [splice,dif_pos (show d+i < ell from hpre.1)] using h
  · have hz : ell+(d+i-ell)=d+i := by omega
    simpa only [hz] using hremoved (d+i-ell) (by omega)
  · let z := d+i+inserted-removed
    have hz : a+(z-a)=z := by dsimp [z];omega
    have h := hpositive (z-a) (by dsimp [z];omega)
    rw [hz] at h
    have hz1 : ¬z < ell := by dsimp [z];omega
    have hz2 : ¬z < ell+inserted := by dsimp [z];omega
    have hz3 : z+removed-inserted=d+i := by dsimp [z];omega
    simpa only [splice,dif_neg hz1,dif_neg hz2,hz3] using h
  · have hz : d+k-b+(d+i-(d+k-b))=d+i := by omega
    have h := hextra (d+i-(d+k-b)) (by omega)
    change p (d+k-b+(d+i-(d+k-b)))=p' (d+k-b+(d+i-(d+k-b))) at h
    simpa only [hz] using h

end DeletionGeneralization.RecoveryTransfer

-- Source module: RecoverySeed
namespace DeletionGeneralization.RecoverySeed
open RecoveryTransfer
universe u
variable {α : Type u}

/-- A finite seed decoder. Its inputs are only the recorded header, positive seed,
and b extension letters; it does not receive the unknown negative word. -/
def decode (ell removed inserted a k b : ℕ) (hv : inserted ≤ b) (hb : b ≤ k)
    (old : Fin removed → α) (bits : Fin k → α) (extra : Fin b → α) : Fin k → α :=
  fun i =>
    let d := seedOffset ell removed inserted a k
    let z := d+i.val
    if hpre : z < ell ∧ a ≤ z ∧ z < a+k then bits ⟨z-a,by omega⟩
    else if hmid : ell ≤ z ∧ z < ell+removed then old ⟨z-ell,by omega⟩
    else if hpost : ell+removed ≤ z ∧ a ≤ z+inserted-removed ∧ z+inserted-removed < a+k
      then bits ⟨z+inserted-removed-a,by omega⟩
    else extra ⟨z-(d+k-b),by
      have h := coverage ell removed inserted a k b i.val hv hb i.isLt
      dsimp only at h
      change (z < ell ∧ a ≤ z ∧ z < a+k) ∨
        (ell ≤ z ∧ z < ell+removed) ∨
        (ell+removed ≤ z ∧ a ≤ z+inserted-removed ∧ z+inserted-removed < a+k) ∨
        (d+k-b ≤ z ∧ z < d+k) at h
      omega⟩

theorem decode_correct (p : ℕ → α) (ell removed inserted a k b : ℕ)
    (v : Fin inserted → α) (hv : inserted ≤ b) (hb : b ≤ k)
    (old : Fin removed → α) (bits : Fin k → α) (extra : Fin b → α)
    (hold : ∀ i, old i=p (ell+i.val))
    (hbits : ∀ i, bits i=splice p ell removed inserted v (a+i.val))
    (hextra : ∀ i, extra i=p (seedOffset ell removed inserted a k+k-b+i.val)) :
    ∀ i, decode ell removed inserted a k b hv hb old bits extra i=
      p (seedOffset ell removed inserted a k+i.val) := by
  intro i
  unfold decode
  dsimp only
  split_ifs with hpre hmid hpost
  · rw [hbits]
    have ha : a+(seedOffset ell removed inserted a k+i.val-a)=
        seedOffset ell removed inserted a k+i.val := by omega
    rw [ha]
    exact dif_pos hpre.1
  · rw [hold]
    congr 1
    try dsimp only
    omega
  · rw [hbits]
    have ha : a+(seedOffset ell removed inserted a k+i.val+inserted-removed-a)=
        seedOffset ell removed inserted a k+i.val+inserted-removed := by omega
    rw [ha]
    have h1 : ¬seedOffset ell removed inserted a k+i.val+inserted-removed < ell := by omega
    have h2 : ¬seedOffset ell removed inserted a k+i.val+inserted-removed < ell+inserted := by omega
    simp only [splice,dif_neg h1,dif_neg h2]
    congr 1
    try dsimp only
    omega
  · rw [hextra]
    congr 1
    try dsimp only
    have h := coverage ell removed inserted a k b i.val hv hb i.isLt
    dsimp only at h
    omega

theorem exists_extension (p : ℕ → α) (ell removed inserted right a k b : ℕ)
    (v : Fin inserted → α) (hv : inserted ≤ b) (hb : b ≤ k)
    (hright : k ≤ right) (ha : a+k ≤ ell+inserted+right)
    (old : Fin removed → α) (bits : Fin k → α)
    (hold : ∀ i, old i=p (ell+i.val))
    (hbits : ∀ i, bits i=splice p ell removed inserted v (a+i.val)) :
    ∃ extra : Fin b → α,
      seedOffset ell removed inserted a k+k ≤ ell+removed+right ∧
      ∀ i, decode ell removed inserted a k b hv hb old bits extra i=
        p (seedOffset ell removed inserted a k+i.val) := by
  refine ⟨fun i => p (seedOffset ell removed inserted a k+k-b+i.val),
    seed_in_bounds ell removed inserted right a k hright ha,?_⟩
  exact decode_correct p ell removed inserted a k b v hv hb old bits _ hold hbits (fun _ => rfl)

end DeletionGeneralization.RecoverySeed

-- Source module: RecoveryMemory

/-!
Executable partial-word storage for the concrete recovery decoder.
Reads require every requested bit to be known. Writes check the finite word
bound and reject disagreements with previously known bits. Neither operation
receives the unknown target word; it appears only in their correctness proofs.
-/
namespace DeletionGeneralization.RecoveryMemory

universe u
variable {α : Type u} [DecidableEq α] [Inhabited α]

abbrev Memory (α : Type u) := ℕ → Option α
abbrev Bits (α : Type u) (len : ℕ) := Fin len → α

def empty : (Memory α) := fun _ => none

def Sound (s : (Memory α)) (p : (ℕ → α)) (m : ℕ) : Prop :=
  ∀ j, j < m → ∀ b, s j = some b → b = p j

def Extends (s t : (Memory α)) : Prop :=
  ∀ j b, s j = some b → t j = some b

def Matches {len : ℕ} (bits : Bits α len) (p : (ℕ → α)) (start : ℕ) : Prop :=
  ∀ i, bits i = p (start + i.val)

/-- Read finite data without a choice oracle or access to the target word. -/
def readBits (s : (Memory α)) (start len : ℕ) : Option (Bits α len) :=
  if ∀ i : Fin len, s (start + i.val) = some ((s (start + i.val)).getD default)
  then some (fun i => (s (start + i.val)).getD default)
  else none

def Compatible (s : (Memory α)) (start : ℕ) {len : ℕ} (bits : Bits α len) : Prop :=
  ∀ i, s (start + i.val) = none ∨ s (start + i.val) = some (bits i)

instance (s : (Memory α)) (start : ℕ) {len : ℕ} (bits : Bits α len) :
    Decidable (Compatible s start bits) := by
  unfold Compatible
  infer_instance

def putBits (s : (Memory α)) (start : ℕ) {len : ℕ} (bits : Bits α len) : (Memory α) :=
  fun j => if h : start ≤ j ∧ j < start + len
    then some (bits ⟨j - start, by omega⟩)
    else s j

/-- Checked write: reject out-of-bounds blocks and inconsistent known letters. -/
def writeBits (s : (Memory α)) (m start : ℕ) {len : ℕ} (bits : Bits α len) : Option (Memory α) :=
  if start + len ≤ m ∧ Compatible s start bits
  then some (putBits s start bits)
  else none

theorem empty_sound (p : (ℕ → α)) (m : ℕ) : Sound empty p m := by
  intro j hj b hb
  simp [empty] at hb

theorem readBits_eq_some_iff (s : (Memory α)) (start len : ℕ) (bits : Bits α len) :
    readBits s start len = some bits ↔
      ∀ i, s (start + i.val) = some (bits i) := by
  unfold readBits
  split
  · rename_i h
    constructor
    · intro heq
      have heq' := Option.some.inj heq
      intro i
      rw [← heq']
      exact h i
    · intro hb
      congr 1
      funext i
      simp [hb i]
  · rename_i h
    constructor
    · simp
    · intro hb
      apply False.elim
      apply h
      intro i
      simp [hb i]

theorem readBits_sound (s : (Memory α)) (p : (ℕ → α)) (m start len : ℕ)
    (hs : Sound s p m) (hbound : start + len ≤ m)
    (bits : Bits α len) (hread : readBits s start len = some bits) :
    Matches bits p start := by
  intro i
  exact hs (start + i.val) (by have := i.isLt; omega) (bits i)
    ((readBits_eq_some_iff s start len bits).mp hread i)

theorem compatible_of_sound (s : (Memory α)) (p : (ℕ → α)) (m start len : ℕ)
    (hs : Sound s p m) (hbound : start + len ≤ m)
    (bits : Bits α len) (hbits : Matches bits p start) :
    Compatible s start bits := by
  intro i
  cases h : s (start + i.val) with
  | none => exact Or.inl rfl
  | some b =>
    have hb := hs (start + i.val) (by have := i.isLt; omega) b h
    exact Or.inr (congrArg some (hb.trans (hbits i).symm))

theorem putBits_at (s : (Memory α)) (start len : ℕ) (bits : Bits α len) (i : Fin len) :
    putBits s start bits (start + i.val) = some (bits i) := by
  simp [putBits, i.isLt]

theorem putBits_extends (s : (Memory α)) (start len : ℕ) (bits : Bits α len)
    (hc : Compatible s start bits) : Extends s (putBits s start bits) := by
  intro j b hb
  unfold putBits
  split
  · rename_i h
    let i : Fin len := ⟨j - start, by omega⟩
    have hi : start + i.val = j := by dsimp [i]; omega
    have hc' := hc i
    rw [hi, hb] at hc'
    rcases hc' with hn | heq
    · contradiction
    · simpa [i] using heq.symm
  · exact hb

theorem putBits_sound (s : (Memory α)) (p : (ℕ → α)) (m start len : ℕ)
    (hs : Sound s p m) (bits : Bits α len) (hbits : Matches bits p start) :
    Sound (putBits s start bits) p m := by
  intro j hj b hb
  unfold putBits at hb
  split at hb
  · rename_i h
    have heq := Option.some.inj hb
    have hbit := hbits ⟨j - start, by omega⟩
    have hidx : start + (j - start) = j := by omega
    simpa [hidx, heq] using hbit
  · exact hs j hj b hb

theorem readBits_putBits (s : (Memory α)) (start len : ℕ) (bits : Bits α len) :
    readBits (putBits s start bits) start len = some bits := by
  apply (readBits_eq_some_iff _ _ _ _).mpr
  exact putBits_at s start len bits

theorem writeBits_success (s : (Memory α)) (p : (ℕ → α)) (m start len : ℕ)
    (hs : Sound s p m) (hbound : start + len ≤ m)
    (bits : Bits α len) (hbits : Matches bits p start) :
    writeBits s m start bits = some (putBits s start bits) := by
  simp [writeBits, hbound, compatible_of_sound s p m start len hs hbound bits hbits]

/-- Every successful checked write preserves all previously known bits. -/
theorem writeBits_extends (s t : (Memory α)) (m start len : ℕ) (bits : Bits α len)
    (hwrite : writeBits s m start bits = some t) : Extends s t := by
  unfold writeBits at hwrite
  split at hwrite
  · rename_i h
    cases Option.some.inj hwrite
    exact putBits_extends s start len bits h.2
  · contradiction

/-- Correct data written to correct memory remains correct and can be read back. -/
theorem writeBits_correct (s : (Memory α)) (p : (ℕ → α)) (m start len : ℕ)
    (hs : Sound s p m) (hbound : start + len ≤ m)
    (bits : Bits α len) (hbits : Matches bits p start) :
    ∃ t, writeBits s m start bits = some t ∧ Sound t p m ∧
      Extends s t ∧ readBits t start len = some bits := by
  refine ⟨putBits s start bits,
    writeBits_success s p m start len hs hbound bits hbits,
    putBits_sound s p m start len hs bits hbits, ?_, readBits_putBits s start len bits⟩
  exact putBits_extends s start len bits
    (compatible_of_sound s p m start len hs hbound bits hbits)


end DeletionGeneralization.RecoveryMemory

-- Source module: Recovery

/-!
Abstract recovery scheduling — partial formalization.
This models a combinatorial subproblem of `lem:resolve`, not that lemma.
There are no words, de Bruijn edges or signed rules in this module.
ConcreteProgress and ConcreteRecovery realize this scheduling on stored letters;
GeneratingRecovery derives the needed data from generating edited-word families.
The existence of a complete recovery trace is proved, not assumed as an
input hypothesis. Checked with Lean 4.34.0; ManuscriptCounting completes the
catalogue generating-set bound using this scheduling argument.
-/
namespace DeletionGeneralization.Recovery

abbrev Slot := Fin 3

def AdjSlot (a b : Slot) : Prop :=
  a.val + 1 = b.val ∨ b.val + 1 = a.val

inductive Reach {B : Type*} (adj : B → B → Prop) : B → B → Prop
  | refl (b : B) : Reach adj b b
  | tail {a b c : B} : Reach adj a b → adj b c → Reach adj a c

/-- `none` denotes x; `some a` denotes an earlier supplying bubble. -/
structure Data (B : Type*) where
  rank : B → ℕ
  source : B → Slot → Option B
  earlier : ∀ b w a, source b w = some a → rank a < rank b
  adjacent : B → B → Prop
  root : B → Prop
  rooted : ∀ b, ∃ r, root r ∧ Reach adjacent r b

structure State (B : Type*) where
  seed : B → Option Slot
  filled : Finset (B × Slot)

variable {B : Type*} [DecidableEq B]
namespace State

def Started (s : State B) (b : B) : Prop := s.seed b ≠ none

def Done (s : State B) (b : B) (w : Slot) : Prop := (b, w) ∈ s.filled

def Complete (s : State B) (b : B) : Prop := ∀ w, s.Done b w

def Ready (s : State B) (b : B) (w : Slot) : Prop :=
  s.seed b = some w ∨ ∃ v, s.Done b v ∧ AdjSlot v w

def start (s : State B) (b : B) (w : Slot) : State B :=
  ⟨Function.update s.seed b (some w), s.filled⟩

def fill (s : State B) (b : B) (w : Slot) : State B :=
  ⟨s.seed, insert (b, w) s.filled⟩

def WellFormed (M : Data B) (s : State B) : Prop :=
  (∀ b w, s.Done b w → s.Started b) ∧
  (∀ b, M.root b → s.Complete b)

theorem started_start (s : State B) (b : B) (w : Slot) :
    (s.start b w).Started b := by simp [Started, start]

theorem started_start_mono (s : State B) (b a : B) (w : Slot)
    (h : s.Started a) : (s.start b w).Started a := by
  by_cases hab : a = b
  · subst a
    exact started_start s b w
  · have hba : b ≠ a := Ne.symm hab
    simpa [Started, start, hab, hba] using h

theorem complete_start (s : State B) (b a : B) (w : Slot)
    (h : s.Complete a) : (s.start b w).Complete a := h

theorem complete_fill (s : State B) (b a : B) (w : Slot)
    (h : s.Complete a) : (s.fill b w).Complete a := by
  intro v
  exact Finset.mem_insert_of_mem (h v)

theorem ready_started (M : Data B) (s : State B)
    (hs : WellFormed M s) (b : B) (w : Slot) (h : s.Ready b w) :
    s.Started b := by
  rcases h with hseed | ⟨v, hv, _⟩
  · simp [Started, hseed]
  · exact hs.1 b v hv

theorem start_wellFormed (M : Data B) (s : State B)
    (hs : WellFormed M s) (b : B) (w : Slot) :
    WellFormed M (s.start b w) := by
  constructor
  · intro a v hav
    exact started_start_mono s b a w (hs.1 a v hav)
  · intro a ha
    exact complete_start s b a w (hs.2 a ha)

theorem fill_wellFormed (M : Data B) (s : State B)
    (hs : WellFormed M s) (b : B) (w : Slot) (hb : s.Started b) :
    WellFormed M (s.fill b w) := by
  constructor
  · intro a v hav
    have hmem : (a, v) ∈ insert (b, w) s.filled := hav
    rcases Finset.mem_insert.mp hmem with heq | hold
    · have hab : a = b := congrArg Prod.fst heq
      subst a
      exact hb
    · exact hs.1 a v hold
  · intro a ha
    exact complete_fill s b a w (hs.2 a ha)

/-- An incomplete started bubble has a ready unfilled window. -/
theorem frontier (s : State B) (b : B)
    (hb : s.Started b) (hi : ¬ s.Complete b) :
    ∃ w, s.Ready b w ∧ ¬ s.Done b w := by
  classical
  by_contra hn
  have hclosed : ∀ w, s.Ready b w → s.Done b w := by
    intro w hw
    by_contra hnot
    exact hn ⟨w, hw, hnot⟩
  cases hseed : s.seed b with
  | none => exact hb hseed
  | some v =>
    have hv : s.Done b v := hclosed v (Or.inl hseed)
    apply hi
    fin_cases v
    · have h1 : s.Done b 1 :=
        hclosed 1 (Or.inr ⟨0, hv, by norm_num [AdjSlot]⟩)
      have h2 : s.Done b 2 :=
        hclosed 2 (Or.inr ⟨1, h1, by norm_num [AdjSlot]⟩)
      intro w
      fin_cases w <;> assumption
    · have h0 : s.Done b 0 :=
        hclosed 0 (Or.inr ⟨1, hv, by norm_num [AdjSlot]⟩)
      have h2 : s.Done b 2 :=
        hclosed 2 (Or.inr ⟨1, hv, by norm_num [AdjSlot]⟩)
      intro w
      fin_cases w <;> assumption
    · have h1 : s.Done b 1 :=
        hclosed 1 (Or.inr ⟨2, hv, by norm_num [AdjSlot]⟩)
      have h0 : s.Done b 0 :=
        hclosed 0 (Or.inr ⟨1, h1, by norm_num [AdjSlot]⟩)
      intro w
      fin_cases w <;> assumption
end State

open State

/--
Abstract transitions. Any seed-window index is permitted in this model.
A concrete realization must choose one containing a REAL transferred
stretch, so an abstract trace is not automatically a valid decoding.
-/
inductive Step (M : Data B) : State B → State B → Prop
  | startAdjacent (s : State B) (a b : B) (w : Slot)
      (ha : s.Complete a) (hab : M.adjacent a b) (hb : ¬ s.Started b) :
      Step M s (s.start b w)
  | startSupplier (s : State B) (b a : B) (w v : Slot)
      (hr : s.Ready b w) (hn : ¬ s.Done b w)
      (hsrc : M.source b w = some a) (ha : ¬ s.Started a) :
      Step M s (s.start a v)
  | fillBase (s : State B) (b : B) (w : Slot)
      (hr : s.Ready b w) (hn : ¬ s.Done b w)
      (hsrc : M.source b w = none) : Step M s (s.fill b w)
  | fillSupplier (s : State B) (b a : B) (w : Slot)
      (hr : s.Ready b w) (hn : ¬ s.Done b w)
      (hsrc : M.source b w = some a) (ha : s.Complete a) :
      Step M s (s.fill b w)

theorem step_preserves (M : Data B) {s s' : State B}
    (h : Step M s s') (hs : s.WellFormed M) : s'.WellFormed M := by
  cases h with
  | startAdjacent a b w ha hab hb =>
      exact State.start_wellFormed M s hs b w
  | startSupplier b a w v hr hn hsrc ha =>
      exact State.start_wellFormed M s hs a v
  | fillBase b w hr hn hsrc =>
      exact State.fill_wellFormed M s hs b w
        (State.ready_started M s hs b w hr)
  | fillSupplier b a w hr hn hsrc ha =>
      exact State.fill_wellFormed M s hs b w
        (State.ready_started M s hs b w hr)

/-- Rank induction rules out incomplete started bubbles in a terminal state. -/
theorem terminal_started_complete (M : Data B) (s : State B)
    (hstop : ∀ s', ¬ Step M s s') : ∀ b, s.Started b → s.Complete b := by
  classical
  have aux : ∀ r : ℕ, ∀ b, M.rank b = r → s.Started b → s.Complete b := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro b hr hb
      by_contra hnot
      obtain ⟨w, hw, hmissing⟩ := State.frontier s b hb hnot
      cases hsrc : M.source b w with
      | none => exact hstop _ (Step.fillBase s b w hw hmissing hsrc)
      | some a =>
        by_cases ha : s.Started a
        · have hsmall : M.rank a < r := by
            have he := M.earlier b w a hsrc
            omega
          have hac : s.Complete a := ih (M.rank a) hsmall a rfl ha
          exact hstop _ (Step.fillSupplier s b a w hw hmissing hsrc hac)
        · exact hstop _ (Step.startSupplier s b a w 0 hw hmissing hsrc ha)
  intro b hb
  exact aux (M.rank b) b rfl hb

theorem terminal_complete (M : Data B) (s : State B)
    (hs : s.WellFormed M) (hstop : ∀ s', ¬ Step M s s') :
    ∀ b, s.Complete b := by
  classical
  have hstarted := terminal_started_complete M s hstop
  have along : ∀ {a b}, Reach M.adjacent a b →
      s.Complete a → s.Complete b := by
    intro a b hpath
    induction hpath with
    | refl => exact fun h => h
    | @tail b c hpath hadj ih =>
      intro ha
      have hb : s.Complete b := ih ha
      by_cases hc : s.Started c
      · exact hstarted c hc
      · exact False.elim (hstop _ (Step.startAdjacent s b c 0 hb hadj hc))
  intro b
  obtain ⟨r, hr, hpath⟩ := M.rooted b
  exact along hpath (hs.2 r hr)

theorem progress (M : Data B) (s : State B)
    (hs : s.WellFormed M) (hincomplete : ¬ ∀ b, s.Complete b) :
    ∃ s', Step M s s' := by
  classical
  by_contra hn
  have hstop : ∀ s', ¬ Step M s s' := by
    intro s' hstep
    exact hn ⟨s', hstep⟩
  exact hincomplete (terminal_complete M s hs hstop)

section Finite
variable [Fintype B]
namespace State

def startedSet (s : State B) : Finset B :=
  Finset.univ.filter (fun b => s.seed b ≠ none)

def score (s : State B) : ℕ := s.startedSet.card + s.filled.card

theorem score_le (s : State B) : s.score ≤ 4 * Fintype.card B := by
  have h1 : s.startedSet.card ≤ Fintype.card B := Finset.card_le_univ _
  have h2 : s.filled.card ≤ Fintype.card (B × Slot) := Finset.card_le_univ _
  have h3 : s.filled.card ≤ 3 * Fintype.card B := by
    simpa [Slot, Fintype.card_prod, Nat.mul_comm] using h2
  unfold score
  omega

theorem score_start (s : State B) (b : B) (w : Slot)
    (hb : ¬ s.Started b) : (s.start b w).score = s.score + 1 := by
  classical
  have heq : (s.start b w).startedSet = insert b s.startedSet := by
    apply Finset.ext
    intro a
    change (a ∈ Finset.univ.filter
      (fun x => Function.update s.seed b (some w) x ≠ none)) ↔
      a ∈ insert b (Finset.univ.filter (fun x => s.seed x ≠ none))
    rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    by_cases hab : a = b
    · subst a
      simp
    · have hba : b ≠ a := Ne.symm hab
      simp [hab, hba]
  have hnot : b ∉ s.startedSet := by
    simpa [startedSet, Started] using hb
  change (s.start b w).startedSet.card + s.filled.card = s.score + 1
  rw [heq, Finset.card_insert_of_notMem hnot]
  unfold score
  omega

theorem score_fill (s : State B) (b : B) (w : Slot)
    (hn : ¬ s.Done b w) : (s.fill b w).score = s.score + 1 := by
  have hnot : (b, w) ∉ s.filled := hn
  change s.startedSet.card + (insert (b, w) s.filled).card = s.score + 1
  rw [Finset.card_insert_of_notMem hnot]
  unfold score
  omega
end State

theorem step_score (M : Data B) {s s' : State B}
    (h : Step M s s') : s'.score = s.score + 1 := by
  cases h with
  | startAdjacent a b w ha hab hb => exact State.score_start s b w hb
  | startSupplier b a w v hr hn hsrc ha => exact State.score_start s a v ha
  | fillBase b w hr hn hsrc => exact State.score_fill s b w hn
  | fillSupplier b a w hr hn hsrc ha => exact State.score_fill s b w hn

inductive Trace (M : Data B) : ℕ → State B → State B → Prop
  | nil (s : State B) : Trace M 0 s s
  | cons {m : ℕ} {s s' s'' : State B} :
      Step M s s' → Trace M m s' s'' → Trace M (m + 1) s s''

/-- Abstract recovery, NOT the manuscript's counting lemma. -/
theorem bounded_recovery (M : Data B) (s : State B)
    (hs : s.WellFormed M) :
    ∃ m s', Trace M m s s' ∧ (∀ b, s'.Complete b) ∧
      m + s.score ≤ 4 * Fintype.card B := by
  classical
  let N := 4 * Fintype.card B
  have aux : ∀ d : ℕ, ∀ q : State B, N - q.score = d → q.WellFormed M →
      ∃ m q', Trace M m q q' ∧ (∀ b, q'.Complete b) ∧ m + q.score ≤ N := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro q hd hq
      by_cases hdone : ∀ b, q.Complete b
      · exact ⟨0, q, Trace.nil q, hdone, by
          have hbound := State.score_le q
          dsimp [N]
          omega⟩
      · obtain ⟨q', hstep⟩ := progress M q hq hdone
        have hq' : q'.WellFormed M := step_preserves M hstep hq
        have hscore : q'.score = q.score + 1 := step_score M hstep
        have hbound : q'.score ≤ N := State.score_le q'
        have hlt : N - q'.score < d := by omega
        obtain ⟨m, q'', htrace, hcomplete, hcost⟩ :=
          ih (N - q'.score) hlt q' rfl hq'
        exact ⟨m + 1, q'', Trace.cons hstep htrace, hcomplete, by omega⟩
  exact aux (N - s.score) s rfl hs

noncomputable def initial (M : Data B) : State B := by
  classical
  exact ⟨fun b => if M.root b then some 0 else none,
    Finset.univ.filter (fun p : B × Slot => M.root p.1)⟩

theorem initial_wellFormed (M : Data B) : (initial M).WellFormed M := by
  classical
  constructor
  · intro b w h
    have hr : M.root b := by simpa [State.Done, initial] using h
    simp [State.Started, initial, hr]
  · intro b hr w
    simp [State.Done, initial, hr]

/-- Starts with just the roots, not an assumed completely recovered state. -/
theorem recover_from_roots (M : Data B) :
    ∃ m s', Trace M m (initial M) s' ∧ (∀ b, s'.Complete b) ∧
      m ≤ 4 * Fintype.card B := by
  obtain ⟨m, s', ht, hc, hm⟩ :=
    bounded_recovery M (initial M) (initial_wellFormed M)
  exact ⟨m, s', ht, hc, by omega⟩
end Finite

end DeletionGeneralization.Recovery

-- Source module: RecoveryWindows
namespace DeletionGeneralization.RecoveryWindows
open RecoveryMemory Recovery
universe u
variable {α : Type u} [DecidableEq α] [Inhabited α]

def windowStart (D : ℕ) (w : Slot) : ℕ :=
  if w.val=0 then 0 else if w.val=1 then D/2 else D

theorem start_le (D : ℕ) (w : Slot) : windowStart D w ≤ D := by
  fin_cases w <;> simp [windowStart, Nat.div_le_self]

theorem overlap (D L k : ℕ) (v w : Slot) (hD : D+2*k ≤ 2*L)
    (hadj : AdjSlot v w) :
    max (windowStart D v) (windowStart D w)+k ≤ windowStart D v+L ∧
    max (windowStart D v) (windowStart D w)+k ≤ windowStart D w+L := by
  fin_cases v <;> fin_cases w <;> simp [AdjSlot,windowStart] at hadj ⊢ <;> omega

theorem cover_seed (D L k a : ℕ) (hD : D+2*k ≤ 2*L)
    (ha : a+k ≤ L+D) :
    ∃ w : Slot, windowStart D w ≤ a ∧ a+k ≤ windowStart D w+L := by
  by_cases hfirst : a+k ≤ L
  · exact ⟨0,by simp [windowStart];omega⟩
  by_cases hmiddle : a+k ≤ D/2+L
  · exact ⟨1,by simp [windowStart];omega⟩
  · exact ⟨2,by simp [windowStart];omega⟩

theorem cover_letter (D L a : ℕ) (hD : D ≤ 2*L) (ha : a < L+D) :
    ∃ w : Slot, windowStart D w ≤ a ∧ a < windowStart D w+L := by
  by_cases hfirst : a < L
  · exact ⟨0,by simp [windowStart];omega⟩
  by_cases hmiddle : a < D/2+L
  · exact ⟨1,by simp [windowStart];omega⟩
  · exact ⟨2,by simp [windowStart];omega⟩

def WindowKnown (s : Memory α) (start len : ℕ) : Prop :=
  ∃ bits, readBits s start len=some bits

def SeedKnown (s : Memory α) (start L k : ℕ) : Prop :=
  ∃ r bits, r+k ≤ L ∧ readBits s (start+r) k=some bits

theorem known_iff (s : Memory α) (start len : ℕ) :
    WindowKnown s start len ↔ ∀ i, i<len → ∃ b, s (start+i)=some b := by
  constructor
  · rintro ⟨bits,hread⟩ i hi
    exact ⟨bits ⟨i,hi⟩,(readBits_eq_some_iff s start len bits).mp hread ⟨i,hi⟩⟩
  · intro h
    refine ⟨fun i => (s (start+i.val)).getD default,?_⟩
    apply (readBits_eq_some_iff _ _ _ _).mpr
    intro i
    obtain ⟨b,hb⟩ := h i.val i.isLt
    simp [hb]

theorem subblock (s : Memory α) (a m b len : ℕ) (h : WindowKnown s a m)
    (hab : a ≤ b) (hbound : b+len ≤ a+m) : WindowKnown s b len := by
  apply (known_iff _ _ _).mpr
  intro i hi
  have hread := (known_iff _ _ _).mp h (b+i-a) (by omega)
  simpa [show a+(b+i-a)=b+i by omega] using hread

theorem known_mono (s t : Memory α) (start len : ℕ)
    (hext : Extends s t) (h : WindowKnown s start len) : WindowKnown t start len := by
  apply (known_iff _ _ _).mpr
  intro i hi
  obtain ⟨b,hb⟩ := (known_iff _ _ _).mp h i hi
  exact ⟨b,hext (start+i) b hb⟩

theorem seed_mono (s t : Memory α) (start L k : ℕ)
    (hext : Extends s t) (h : SeedKnown s start L k) : SeedKnown t start L k := by
  obtain ⟨r,bits,hr,hread⟩ := h
  obtain ⟨bits',hread'⟩ := known_mono s t (start+r) k hext ⟨bits,hread⟩
  exact ⟨r,bits',hr,hread'⟩

theorem adjacent_seed (s : Memory α) (D L k : ℕ) (v w : Slot)
    (hD : D+2*k ≤ 2*L) (hadj : AdjSlot v w)
    (hknown : WindowKnown s (windowStart D v) L) :
    SeedKnown s (windowStart D w) L k := by
  obtain ⟨ha,hb⟩ := overlap D L k v w hD hadj
  let a := max (windowStart D v) (windowStart D w)
  have hma : windowStart D v ≤ a := le_max_left _ _
  have hmb : windowStart D w ≤ a := le_max_right _ _
  obtain ⟨bits,hread⟩ := subblock s (windowStart D v) L a k hknown hma ha
  refine ⟨a-windowStart D w,bits,by dsimp [a];omega,?_⟩
  simpa [show windowStart D w+(a-windowStart D w)=a by omega] using hread

theorem seed_selects (s : Memory α) (D L k a : ℕ) (hD : D+2*k ≤ 2*L)
    (ha : a+k ≤ L+D) (hknown : WindowKnown s a k) :
    ∃ w : Slot, SeedKnown s (windowStart D w) L k := by
  obtain ⟨w,hwa,haw⟩ := cover_seed D L k a hD ha
  obtain ⟨bits,hread⟩ := hknown
  refine ⟨w,a-windowStart D w,bits,by omega,?_⟩
  simpa [show windowStart D w+(a-windowStart D w)=a by omega] using hread

theorem all_known (s : Memory α) (D L : ℕ) (hD : D ≤ 2*L)
    (hknown : ∀ w : Slot, WindowKnown s (windowStart D w) L) :
    WindowKnown s 0 (L+D) := by
  apply (known_iff _ _ _).mpr
  intro i hi
  obtain ⟨w,ha,hb⟩ := cover_letter D L i hD hi
  have h := (known_iff _ _ _).mp (hknown w) (i-windowStart D w) (by omega)
  simpa [show windowStart D w+(i-windowStart D w)=i by omega] using h

variable {B : Type*}

structure Realizes (s : State B) (mem : B → Memory α) (D : B → ℕ) (L k : ℕ) : Prop where
  seed_known : ∀ b w, s.seed b=some w → SeedKnown (mem b) (windowStart (D b) w) L k
  done_known : ∀ b w, s.Done b w → WindowKnown (mem b) (windowStart (D b) w) L

theorem Realizes.ready (s : State B) (mem : B → Memory α) (D : B → ℕ)
    (L k : ℕ) (hreal : Realizes s mem D L k) (b : B) (w : Slot)
    (hD : D b+2*k ≤ 2*L) (hr : s.Ready b w) :
    SeedKnown (mem b) (windowStart (D b) w) L k := by
  rcases hr with hseed | ⟨v,hv,hadj⟩
  · exact hreal.seed_known b w hseed
  · exact adjacent_seed (mem b) (D b) L k v w hD hadj (hreal.done_known b v hv)

theorem Realizes.complete (s : State B) (mem : B → Memory α) (D : B → ℕ)
    (L k : ℕ) (hreal : Realizes s mem D L k) (b : B)
    (hD : D b ≤ 2*L) (hc : s.Complete b) : WindowKnown (mem b) 0 (L+D b) :=
  all_known (mem b) (D b) L hD (fun w => hreal.done_known b w (hc w))

theorem Realizes.mono (s : State B) (mem mem' : B → Memory α) (D : B → ℕ) (L k : ℕ)
    (hreal : Realizes s mem D L k) (hext : ∀ b, Extends (mem b) (mem' b)) :
    Realizes s mem' D L k where
  seed_known b w h := seed_mono _ _ _ _ _ (hext b) (hreal.seed_known b w h)
  done_known b w h := known_mono _ _ _ _ (hext b) (hreal.done_known b w h)

theorem Realizes.start [DecidableEq B] (s : State B) (mem : B → Memory α)
    (D : B → ℕ) (L k : ℕ) (hreal : Realizes s mem D L k) (b : B) (w : Slot)
    (hseed : SeedKnown (mem b) (windowStart (D b) w) L k) :
    Realizes (s.start b w) mem D L k where
  seed_known a v h := by
    by_cases hab : a=b
    · subst a
      have hwv : w=v := by simpa [State.start] using h
      simpa [hwv] using hseed
    · have hba : b≠a := Ne.symm hab
      exact hreal.seed_known a v (by simpa [State.start,hab,hba] using h)
  done_known a v h := hreal.done_known a v h

theorem Realizes.fill [DecidableEq B] (s : State B) (mem : B → Memory α)
    (D : B → ℕ) (L k : ℕ) (hreal : Realizes s mem D L k) (b : B) (w : Slot)
    (hknown : WindowKnown (mem b) (windowStart (D b) w) L) :
    Realizes (s.fill b w) mem D L k where
  seed_known a v h := hreal.seed_known a v h
  done_known a v h := by
    rcases Finset.mem_insert.mp h with heq | hold
    · have hab : a=b := congrArg Prod.fst heq
      have hvw : v=w := congrArg Prod.snd heq
      subst a
      subst v
      exact hknown
    · exact hreal.done_known a v hold

end DeletionGeneralization.RecoveryWindows

-- Source module: RecoveryHeader
namespace DeletionGeneralization.RecoveryHeader
open RecoveryMemory RecoveryWindows RecoveryTransfer
universe u

structure Header (α : Type u) (L b : ℕ) where
  left : Fin L
  right : Fin L
  removed : Fin (b+1)
  inserted : Fin (b+1)
  old : Fin b → α
  new : Fin b → α
  deriving DecidableEq

instance {α : Type u} [Fintype α] {L b : ℕ} : Fintype (Header α L b) :=
  Fintype.ofEquiv (Fin L × Fin L × Fin (b+1) × Fin (b+1) × (Fin b → α) × (Fin b → α))
    { toFun := fun x => ⟨x.1,x.2.1,x.2.2.1,x.2.2.2.1,x.2.2.2.2.1,x.2.2.2.2.2⟩
      invFun := fun h => (h.left,h.right,h.removed,h.inserted,h.old,h.new)
      left_inv := by rintro ⟨a,c,d,e,f,g⟩;rfl
      right_inv := by intro h;cases h;rfl }

variable {α : Type u} [DecidableEq α] [Inhabited α] {L b : ℕ}

def oldLetters (h : Header α L b) : Fin h.removed.val → α :=
  fun i => h.old ⟨i.val,by have := h.removed.isLt;omega⟩

def newLetters (h : Header α L b) : Fin h.inserted.val → α :=
  fun i => h.new ⟨i.val,by have := h.inserted.isLt;omega⟩

def negativeLength (h : Header α L b) : ℕ := h.left.val+h.removed.val+h.right.val
def positiveLength (h : Header α L b) : ℕ := h.left.val+h.inserted.val+h.right.val
def extraLength (h : Header α L b) : ℕ := negativeLength h-L

def positive (h : Header α L b) (p : ℕ → α) : ℕ → α :=
  splice p h.left.val h.removed.val h.inserted.val (newLetters h)

def path (h : Header α L b) (p : ℕ → α) (side : Bool) : ℕ → α :=
  if side then positive h p else p

def pathLength (h : Header α L b) (side : Bool) : ℕ :=
  if side then positiveLength h else negativeLength h

def Valid (h : Header α L b) (k : ℕ) : Prop :=
  k ≤ h.right.val ∧ L ≤ negativeLength h ∧ extraLength h+2*k ≤ 2*L

def Correct (h : Header α L b) (p : ℕ → α) : Prop :=
  ∀ i, oldLetters h i=p (h.left.val+i.val)

def pad {len : ℕ} (bits : Fin len → α) : ℕ → α :=
  fun j => if hj : j < len then bits ⟨j,hj⟩ else default

theorem positive_congr (h : Header α L b) (p q : ℕ → α)
    (heq : ∀ i, i < negativeLength h → p i=q i) :
    ∀ i, i < positiveLength h → positive h p i=positive h q i := by
  intro i hi
  unfold positive splice
  split_ifs with hleft hmid
  · apply heq
    dsimp [negativeLength,positiveLength] at *
    omega
  · rfl
  · apply heq
    dsimp [negativeLength,positiveLength] at *
    omega

def readPath (h : Header α L b) (mem : Memory α) (side : Bool) (a len : ℕ) :
    Option (Fin len → α) :=
  if a+len ≤ pathLength h side then
    if side then
      (readBits mem 0 (negativeLength h)).map (fun bits i => positive h (pad bits) (a+i.val))
    else readBits mem a len
  else none

theorem readPath_complete (h : Header α L b) (p : ℕ → α) (mem : Memory α)
    (side : Bool) (a len : ℕ) (hs : Sound mem p (negativeLength h))
    (hknown : WindowKnown mem 0 (negativeLength h))
    (ha : a+len ≤ pathLength h side) :
    ∃ bits, readPath h mem side a len=some bits ∧
      ∀ i, bits i=path h p side (a+i.val) := by
  cases side with
  | false =>
    obtain ⟨bits,hread⟩ := subblock mem 0 (negativeLength h) a len hknown (by omega)
      (by simpa [pathLength] using ha)
    refine ⟨bits,by simpa [readPath,ha] using hread,?_⟩
    intro i
    exact readBits_sound mem p (negativeLength h) a len hs
      (by simpa [pathLength] using ha) bits hread i
  | true =>
    obtain ⟨neg,hread⟩ := hknown
    have heq : ∀ j, j < negativeLength h → pad neg j=p j := by
      intro j hj
      have hr := readBits_sound mem p (negativeLength h) 0 (negativeLength h) hs
        (by omega) neg hread ⟨j,hj⟩
      simpa [pad,hj] using hr
    refine ⟨fun i => positive h (pad neg) (a+i.val),?_,?_⟩
    · simp only [readPath,if_pos ha,Bool.true_eq,ite_true,hread,Option.map_some]
    · intro i
      exact positive_congr h (pad neg) p heq (a+i.val)
        (by have := i.isLt;simpa [pathLength] using (show a+i.val < positiveLength h by
          simp [pathLength] at ha;omega))

def transfer (h : Header α L b) (k a : ℕ) (hb : b ≤ k)
    (bits : Fin k → α) (extra : Fin b → α) : ℕ × (Fin k → α) :=
  (seedOffset h.left.val h.removed.val h.inserted.val a k,
   RecoverySeed.decode h.left.val h.removed.val h.inserted.val a k b
     (by have := h.inserted.isLt;omega) hb (oldLetters h) bits extra)

theorem transfer_correct (h : Header α L b) (k a : ℕ) (hb : b ≤ k)
    (p : ℕ → α) (hv : Valid h k) (hc : Correct h p)
    (bits : Fin k → α) (ha : a+k ≤ positiveLength h)
    (hbits : ∀ i, bits i=positive h p (a+i.val)) :
    ∃ extra : Fin b → α,
      (transfer h k a hb bits extra).1+k ≤ negativeLength h ∧
      ∀ i, (transfer h k a hb bits extra).2 i=p ((transfer h k a hb bits extra).1+i.val) := by
  exact RecoverySeed.exists_extension p h.left.val h.removed.val h.inserted.val h.right.val
    a k b (newLetters h) (by have := h.inserted.isLt;omega) hb hv.1 ha
    (oldLetters h) bits hc hbits

theorem geometry (h : Header α L b) (k : ℕ)
    (hL : L=3*(k+b+1))
    (hleft : L-1-k-b ≤ h.left.val) (hright : L-1-k-b ≤ h.right.val)
    (hlen : L ≤ negativeLength h) : Valid h k := by
  have hru := h.removed.isLt
  have hlu := h.left.isLt
  have hrr := h.right.isLt
  dsimp [Valid,extraLength,negativeLength] at *
  omega

end DeletionGeneralization.RecoveryHeader

-- Source module: RecoveryWords

/-!
Local word-recovery lemmas — partial formalization.
Target: Section 5, `lem:resolve`, of binary_existence_2t_minus_1.tex.
Checked with Lean 4.34.0; this file alone does not verify the counting lemma.
Finite words are represented by total letter functions with explicit bounds.
-/
namespace DeletionGeneralization.RecoveryWords

universe u
variable {α : Type u}
abbrev Letters (α : Type u) := ℕ → α

def Agree (x : Letters α) (a : ℕ) (y : Letters α) (b k : ℕ) : Prop :=
  ∀ i, i < k → x (a + i) = y (b + i)

def KUnique (x : Letters α) (n k : ℕ) : Prop :=
  ∀ a b, a + k ≤ n → b + k ≤ n → Agree x a x b k → a = b

/-- A known k-stretch at a fixed offset determines a window in x. -/
theorem unique_window_lookup
    (x : Letters α) (n k L a b r : ℕ)
    (hx : KUnique x n k) (ha : a + L ≤ n) (hb : b + L ≤ n)
    (hr : r + k ≤ L) (h : Agree x (a + r) x (b + r) k) : a = b := by
  have heq : a + r = b + r :=
    hx (a + r) (b + r) (by omega) (by omega) h
  omega


end DeletionGeneralization.RecoveryWords

-- Source module: RecoveryLookup

/-!
Executable lookup of a window in the fixed word from a finite seed.
The algorithm receives only the fixed word, bounds, and the seed bits.
The unknown target word occurs only in the correctness theorems.
-/
namespace DeletionGeneralization.RecoveryLookup

universe u
variable {α : Type u} [DecidableEq α] [Inhabited α]

open RecoveryWords

/-- A candidate is in bounds and has the supplied seed at the requested offset. -/
def Matches (x : Letters α) (n k L r : ℕ) (seed : Fin k → α) (a : ℕ) : Prop :=
  r + k ≤ L ∧ a + L ≤ n ∧ ∀ i : Fin k, x (a + r + i.val) = seed i

instance (x : Letters α) (n k L r : ℕ) (seed : Fin k → α) (a : ℕ) :
    Decidable (Matches x n k L r seed a) := by
  unfold Matches
  infer_instance

/-- Search the finitely many candidate window starts; no witness is an input. -/
def lookup (x : Letters α) (n k L r : ℕ) (seed : Fin k → α) : Option ℕ :=
  (List.range (n + 1)).find? (fun a => decide (Matches x n k L r seed a))

theorem lookup_sound (x : Letters α) (n k L r a : ℕ) (seed : Fin k → α)
    (h : lookup x n k L r seed = some a) : Matches x n k L r seed a := by
  have hp : decide (Matches x n k L r seed a) = true :=
    List.find?_some (p := fun b => decide (Matches x n k L r seed b)) h
  exact of_decide_eq_true hp

theorem lookup_exists (x : Letters α) (n k L r : ℕ) (seed : Fin k → α)
    (h : ∃ a, Matches x n k L r seed a) :
    ∃ a, lookup x n k L r seed = some a := by
  rcases h with ⟨a, ha⟩
  cases heq : lookup x n k L r seed with
  | some b => exact ⟨b, rfl⟩
  | none =>
    have hnone := List.find?_eq_none.mp heq
    have hamem : a ∈ List.range (n + 1) := by
      simp only [List.mem_range]
      have := ha.2.1
      omega
    have hfalse := hnone a hamem
    exact False.elim (hfalse (decide_eq_true ha))

theorem matches_unique (x : Letters α) (n k L r a b : ℕ) (seed : Fin k → α)
    (hx : KUnique x n k) (ha : Matches x n k L r seed a)
    (hb : Matches x n k L r seed b) : a = b := by
  apply unique_window_lookup x n k L a b r hx ha.2.1 hb.2.1 ha.1
  intro i hi
  exact (ha.2.2 ⟨i, hi⟩).trans (hb.2.2 ⟨i, hi⟩).symm

/-- Under k-uniqueness the bounded search returns exactly the matching start. -/
theorem lookup_eq_some_iff (x : Letters α) (n k L r a : ℕ) (seed : Fin k → α)
    (hx : KUnique x n k) :
    lookup x n k L r seed = some a ↔ Matches x n k L r seed a := by
  constructor
  · exact lookup_sound x n k L r a seed
  · intro ha
    obtain ⟨b, hb⟩ := lookup_exists x n k L r seed ⟨a, ha⟩
    have hab := matches_unique x n k L r a b seed hx ha
      (lookup_sound x n k L r b seed hb)
    simpa [hab] using hb

/-- Copy the entire located window as finite data. -/
def recoverWindow (x : Letters α) (n k L r : ℕ) (seed : Fin k → α) :
    Option (Fin L → α) :=
  (lookup x n k L r seed).map (fun a i => x (a + i.val))

/-- Any returned window really is an in-bounds window of the fixed word. -/
theorem recoverWindow_sound (x : Letters α) (n k L r : ℕ) (seed : Fin k → α)
    (bits : Fin L → α) (h : recoverWindow x n k L r seed = some bits) :
    ∃ a, Matches x n k L r seed a ∧ bits = fun i => x (a + i.val) := by
  unfold recoverWindow at h
  cases heq : lookup x n k L r seed with
  | none => simp [heq] at h
  | some a =>
    simp only [heq, Option.map_some, Option.some.injEq] at h
    exact ⟨a, lookup_sound x n k L r a seed heq, h.symm⟩

/-- A target window occurring in x is recovered exactly from its seed. -/
theorem recoverWindow_of_occurrence
    (x target : Letters α) (n k L r a w : ℕ) (seed : Fin k → α)
    (hx : KUnique x n k) (hr : r + k ≤ L) (ha : a + L ≤ n)
    (hocc : Agree x a target w L)
    (hseed : ∀ i : Fin k, seed i = target (w + r + i.val)) :
    recoverWindow x n k L r seed = some (fun i : Fin L => target (w + i.val)) := by
  have hmatch : Matches x n k L r seed a := by
    refine ⟨hr, ha, ?_⟩
    intro i
    have hi : r + i.val < L := by omega
    calc
      x (a + r + i.val) = target (w + r + i.val) := by
        simpa [Nat.add_assoc] using hocc (r + i.val) hi
      _ = seed i := (hseed i).symm
  have hlookup := (lookup_eq_some_iff x n k L r a seed hx).mpr hmatch
  unfold recoverWindow
  rw [hlookup]
  simp only [Option.map_some, Option.some.injEq]
  funext i
  exact hocc i.val i.isLt


end DeletionGeneralization.RecoveryLookup

-- Source module: RecoveryFill

/-!
Executable letter-level fill operations. Base-word fills discover the window
position from stored seed bits. Supplier fills copy stored bits at a recorded
offset. The target words and occurrence witnesses are proof parameters only.
These primitives are used by the bounded decoder proof in ConcreteRecovery.
-/
namespace DeletionGeneralization.RecoveryFill

universe u
variable {α : Type u} [DecidableEq α] [Inhabited α]

open RecoveryWords RecoveryMemory

/-- Fill a destination window by locating its known seed in the fixed word. -/
def fillFromBase (x : Letters α) (n k L : ℕ) (s : (Memory α)) (m start r : ℕ) :
    Option (Memory α) :=
  (readBits s (start + r) k).bind fun seed =>
    (RecoveryLookup.recoverWindow x n k L r seed).bind fun bits =>
      writeBits s m start bits

/-- Copy a bounded block of actual stored supplier data into checked memory. -/
def copyFromMemory (source : (Memory α)) (sourceLength sourceStart len : ℕ)
    (s : (Memory α)) (m start : ℕ) : Option (Memory α) :=
  if sourceStart + len ≤ sourceLength then
    (readBits source sourceStart len).bind fun bits => writeBits s m start bits
  else none

/-- Root records contain a position in x, so their whole negative path can be read. -/
def loadRoot (x : Letters α) (n a len : ℕ) (s : (Memory α)) (m : ℕ) : Option (Memory α) :=
  if a + len ≤ n then writeBits s m 0 (fun i : Fin len => x (a + i.val))
  else none

def Recovered (s t : (Memory α)) (p : Letters α) (m start len : ℕ) : Prop :=
  Sound t p m ∧ Extends s t ∧
    readBits t start len = some (fun i : Fin len => p (start + i.val))

/-- A valid base occurrence is filled exactly, using only its stored seed. -/
theorem fillFromBase_correct (x p : Letters α) (n k L : ℕ)
    (s : (Memory α)) (m start r : ℕ) (seed : Bits α k)
    (hx : KUnique x n k) (hs : Sound s p m)
    (hbound : start + L ≤ m) (hr : r + k ≤ L)
    (hread : readBits s (start + r) k = some seed)
    (hocc : ∃ a, a + L ≤ n ∧ Agree x a p start L) :
    ∃ t, fillFromBase x n k L s m start r = some t ∧
      Recovered s t p m start L := by
  obtain ⟨a, ha, hagree⟩ := hocc
  have hseed : RecoveryMemory.Matches seed p (start + r) :=
    readBits_sound s p m (start + r) k hs (by omega) seed hread
  have hlookup := RecoveryLookup.recoverWindow_of_occurrence
    x p n k L r a start seed hx hr ha hagree hseed
  let bits : Bits α L := fun i => p (start + i.val)
  obtain ⟨t, ht, hsound, hext, hknown⟩ :=
    writeBits_correct s p m start L hs hbound bits (fun _ => rfl)
  refine ⟨t, ?_, hsound, hext, hknown⟩
  simp only [fillFromBase, hread, Option.bind_some, hlookup]
  exact ht

/-- Supplier copying preserves truth when the recorded blocks really agree. -/
theorem copyFromMemory_correct (source s : (Memory α)) (q p : Letters α)
    (sourceLength sourceStart len m start : ℕ) (bits : Bits α len)
    (hsource : Sound source q sourceLength) (hs : Sound s p m)
    (hsourceBound : sourceStart + len ≤ sourceLength) (hbound : start + len ≤ m)
    (hread : readBits source sourceStart len = some bits)
    (hagree : Agree q sourceStart p start len) :
    ∃ t, copyFromMemory source sourceLength sourceStart len s m start = some t ∧
      Recovered s t p m start len := by
  have hbits : RecoveryMemory.Matches bits p start := by
    intro i
    exact (readBits_sound source q sourceLength sourceStart len hsource
      hsourceBound bits hread i).trans (hagree i.val i.isLt)
  obtain ⟨t, ht, hsound, hext, hknown⟩ :=
    writeBits_correct s p m start len hs hbound bits hbits
  refine ⟨t, ?_, hsound, hext, ?_⟩
  · simp only [copyFromMemory, if_pos hsourceBound, hread, Option.bind_some]
    exact ht
  · rw [hknown]
    congr 1
    funext i
    exact hbits i

theorem loadRoot_correct (x p : Letters α) (n a len : ℕ) (s : (Memory α)) (m : ℕ)
    (hs : Sound s p m) (ha : a + len ≤ n) (hbound : len ≤ m)
    (hocc : Agree x a p 0 len) :
    ∃ t, loadRoot x n a len s m = some t ∧ Recovered s t p m 0 len := by
  let bits : Bits α len := fun i => x (a + i.val)
  have hbits : RecoveryMemory.Matches bits p 0 := fun i => hocc i.val i.isLt
  obtain ⟨t, ht, hsound, hext, hknown⟩ :=
    writeBits_correct s p m 0 len hs (by omega) bits hbits
  refine ⟨t, ?_, hsound, hext, ?_⟩
  · simpa only [loadRoot, if_pos ha] using ht
  · rw [hknown]
    congr 1
    funext i
    exact hbits i

/-- Even arbitrary base-fill inputs cannot overwrite an already recorded bit. -/
theorem fillFromBase_extends (x : Letters α) (n k L : ℕ)
    (s t : (Memory α)) (m start r : ℕ)
    (h : fillFromBase x n k L s m start r = some t) : Extends s t := by
  unfold fillFromBase at h
  cases hseed : readBits s (start + r) k with
  | none => simp [hseed] at h
  | some seed =>
    simp only [hseed, Option.bind_some] at h
    cases hbits : RecoveryLookup.recoverWindow x n k L r seed with
    | none => simp [hbits] at h
    | some bits =>
      simp only [hbits, Option.bind_some] at h
      exact writeBits_extends s t m start L bits h


end DeletionGeneralization.RecoveryFill

-- Source module: RecoveryDecoder
namespace DeletionGeneralization.RecoveryDecoder
open RecoveryMemory RecoveryWindows RecoveryHeader
universe u
variable {α : Type u} [DecidableEq α] [Inhabited α] {B : Type*} [DecidableEq B] {L b : ℕ}

inductive Instruction (B : Type*) (α : Type u) (b : ℕ) where
  | start (source : B) (sourceSide : Bool) (sourceOffset : ℕ)
      (dest : B) (destSide : Bool) (destOffset : ℕ) (extra : Fin b → α)
  | fillBase (dest : B) (window : Recovery.Slot) (seedOffset : ℕ)
  | fillSupplier (source : B) (side : Bool) (sourceOffset : ℕ)
      (dest : B) (window : Recovery.Slot)

def start (h : Header α L b) (k : ℕ) (hbk : b ≤ k) (mem : Memory α)
    (side : Bool) (a : ℕ) (bits : Fin k → α) (extra : Fin b → α) : Option (Memory α) :=
  if side then
    let out := transfer h k a hbk bits extra
    writeBits mem (negativeLength h) out.1 out.2
  else writeBits mem (negativeLength h) a bits

def execute {L b : ℕ} (x : ℕ → α) (n k : ℕ) (hbk : b ≤ k)
    (header : B → Header α L b) (mem : B → Memory α) :
    Instruction B α b → Option (B → Memory α)
  | .start source ss so dest ds d extra =>
    (readPath (header source) (mem source) ss so k).bind fun bits =>
      (start (header dest) k hbk (mem dest) ds d bits extra).map (Function.update mem dest)
  | .fillBase dest w r =>
    (RecoveryFill.fillFromBase x n k L (mem dest) (negativeLength (header dest))
      (windowStart (extraLength (header dest)) w) r).map (Function.update mem dest)
  | .fillSupplier source side a dest w =>
    (readPath (header source) (mem source) side a L).bind fun bits =>
      (writeBits (mem dest) (negativeLength (header dest))
        (windowStart (extraLength (header dest)) w) bits).map (Function.update mem dest)

def run {L b : ℕ} (x : ℕ → α) (n k : ℕ) (hbk : b ≤ k)
    (header : B → Header α L b) : (B → Memory α) → List (Instruction B α b) → Option (B → Memory α)
  | mem, [] => some mem
  | mem, instr::rest => (execute x n k hbk header mem instr).bind fun next => run x n k hbk header next rest

def loadRoots {L b : ℕ} (x : ℕ → α) (n : ℕ) (header : B → Header α L b) :
    (B → Memory α) → List (B × ℕ) → Option (B → Memory α)
  | mem, [] => some mem
  | mem, (dest,a)::rest =>
    (RecoveryFill.loadRoot x n a (negativeLength (header dest))
      (mem dest) (negativeLength (header dest))).bind fun next =>
        loadRoots x n header (Function.update mem dest next) rest

def isStart {b : ℕ} : Instruction B α b → ℕ
  | .start .. => 1
  | _ => 0

def starts {b : ℕ} (ins : List (Instruction B α b)) : ℕ := (ins.map isStart).sum

def Bounded {b : ℕ} (L : ℕ) : Instruction B α b → Prop
  | .start _ _ a _ _ c _ => a < 3*L ∧ c < 3*L
  | .fillBase _ _ r => r < 3*L
  | .fillSupplier _ _ a _ _ => a < 3*L

end DeletionGeneralization.RecoveryDecoder

-- Source module: RecoveryPaths

/-!
Concrete contiguity of a word whose L-windows occur in a k-unique word.

This is the word-level step used to place a component's root negative path
inside x. It does not assume that the occurrence positions are consecutive:
that fact is proved from k-uniqueness and the overlaps of consecutive windows.
Finite lengths are explicit bounds on total letter functions, as in RecoveryWords.
-/

namespace DeletionGeneralization.RecoveryPaths

universe u
variable {α : Type u} [DecidableEq α] [Inhabited α]

open RecoveryWords

/-- A length-L window has a valid occurrence in the finite prefix of x. -/
def Occurs (x : Letters α) (n : ℕ) (p : Letters α) (i L : ℕ) : Prop :=
  ∃ a, a + L ≤ n ∧ Agree x a p i L

/-- Two consecutive L-windows must occur consecutively in a k-unique x. -/
theorem consecutive_occurrences
    (x p : Letters α) (n k L i a b : ℕ)
    (hx : KUnique x n k) (hk : k < L)
    (ha : a + L ≤ n) (hb : b + L ≤ n)
    (hleft : Agree x a p i L) (hright : Agree x b p (i + 1) L) :
    b = a + 1 := by
  have hmatch : Agree x (a + 1) x b k := by
    intro j hj
    have hl := hleft (j + 1) (by omega)
    have hr := hright j (by omega)
    calc
      x (a + 1 + j) = x (a + (j + 1)) := congrArg x (by omega)
      _ = p (i + (j + 1)) := hl
      _ = p (i + 1 + j) := congrArg p (by omega)
      _ = x (b + j) := hr.symm
  exact (hx (a + 1) b (by omega) (by omega) hmatch).symm

/--
All L-windows of p occurring in x forces the whole length-(L+D) word to
occur in x. This establishes contiguity rather than taking it as a premise.
-/
theorem all_windows_occur_implies_subword
    (x p : Letters α) (n k L D : ℕ)
    (hx : KUnique x n k) (hk : k < L)
    (hocc : ∀ i, i ≤ D → Occurs x n p i L) :
    ∃ a, a + (L + D) ≤ n ∧ Agree x a p 0 (L + D) := by
  obtain ⟨a, ha, hzero⟩ := hocc 0 (by omega)
  have aligned : ∀ i, i ≤ D →
      a + i + L ≤ n ∧ Agree x (a + i) p i L := by
    intro i
    induction i with
    | zero =>
      intro _
      simpa only [Nat.add_zero] using And.intro ha hzero
    | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      obtain ⟨b, hb, hnext⟩ := hocc (i + 1) hi
      have heq := consecutive_occurrences x p n k L i (a + i) b
        hx hk hprev.1 hb hprev.2 hnext
      constructor
      · omega
      · have hindex : a + (i + 1) = b := by omega
        simpa only [hindex] using hnext
  refine ⟨a, by have hlast := (aligned D le_rfl).1; omega, ?_⟩
  intro j hj
  let i := min j D
  have hiD : i ≤ D := Nat.min_le_right j D
  have hij : i ≤ j := Nat.min_le_left j D
  have hlocal : j - i < L := by
    dsimp [i]
    by_cases h : j ≤ D
    · rw [Nat.min_eq_left h]
      omega
    · rw [Nat.min_eq_right (by omega)]
      omega
  have heq := (aligned i hiD).2 (j - i) hlocal
  have hsource : a + i + (j - i) = a + j := by omega
  have htarget : i + (j - i) = 0 + j := by omega
  simpa only [hsource, htarget] using heq

/-- The full word occurrence is unique; no second root position is needed. -/
theorem subword_position_unique
    (x p : Letters α) (n k m a b : ℕ)
    (hx : KUnique x n k) (hkm : k ≤ m)
    (ha : a + m ≤ n) (hb : b + m ≤ n)
    (hleft : Agree x a p 0 m) (hright : Agree x b p 0 m) :
    a = b := by
  apply hx a b (by omega) (by omega)
  intro i hi
  exact (hleft i (by omega)).trans (hright i (by omega)).symm


end DeletionGeneralization.RecoveryPaths

-- Source module: RecoveryRoots

/-!
Concrete selection of a root in every component of a family of word paths.

The paths carry actual letters and finite lengths. Generating means that each
negative L-window occurs in x or on an earlier family's path. Adjacency is
defined by equal, in-bounds (L-1)-letter stretches, not an assumed supplier
closure. Least rank therefore supplies a member whose whole negative path
occurs in a k-unique x. This does not yet define manuscript rules or a decoder.
-/

namespace DeletionGeneralization.RecoveryRoots

universe u
variable {α : Type u} [DecidableEq α] [Inhabited α]

open RecoveryWords

/-- Side false is negative; side true is positive. Each side has length L+extra. -/
structure Family (α : Type u) (B : Type*) where
  rank : B → ℕ
  path : B → Bool → Letters α
  extra : B → Bool → ℕ

namespace Family

/-- Every negative window occurs in x or in an earlier path of the family. -/
def Generating {B : Type*} (F : Family α B) (x : Letters α) (n L : ℕ) : Prop :=
  ∀ b i, i ≤ F.extra b false →
    RecoveryPaths.Occurs x n (F.path b false) i L ∨
      ∃ a side j, F.rank a < F.rank b ∧ j ≤ F.extra a side ∧
        Agree (F.path b false) i (F.path a side) j L

/-- Actual common vertices, with valid offsets on the two finite word paths. -/
def Adjacent {B : Type*} (F : Family α B) (L : ℕ) (a b : B) : Prop :=
  ∃ sideA sideB i j,
    i ≤ F.extra a sideA + 1 ∧ j ≤ F.extra b sideB + 1 ∧
    i + (L - 1) ≤ L + F.extra a sideA ∧
    j + (L - 1) ≤ L + F.extra b sideB ∧
    Agree (F.path a sideA) i (F.path b sideB) j (L - 1)

/-- Undirected connectedness of the actual common-vertex relation. -/
def Connected {B : Type*} (F : Family α B) (L : ℕ) : B → B → Prop :=
  Relation.EqvGen (F.Adjacent L)

/-- Sharing an entire valid gram also gives a common de Bruijn vertex. -/
theorem supplier_adjacent {B : Type*} (F : Family α B) (L : ℕ)
    (b a : B) (side : Bool) (i j : ℕ)
    (hi : i ≤ F.extra b false) (hj : j ≤ F.extra a side)
    (hgram : Agree (F.path b false) i (F.path a side) j L) :
    F.Adjacent L b a := by
  refine ⟨false, side, i, j, by omega, by omega, by omega, by omega, ?_⟩
  intro q hq
  exact hgram q (by omega)

/-- Natural-number rank has a least value in every nonempty component. -/
theorem exists_minimal_in_component {B : Type*} (F : Family α B) (L : ℕ) (b : B) :
    ∃ r, F.Connected L r b ∧
      ∀ a, F.Connected L a b → F.rank r ≤ F.rank a := by
  classical
  let P : ℕ → Prop := fun k => ∃ a, F.Connected L a b ∧ F.rank a = k
  have hex : ∃ k, P k := ⟨F.rank b, b, Relation.EqvGen.refl b, rfl⟩
  obtain ⟨r, hr, hrank⟩ := Nat.find_spec hex
  refine ⟨r, hr, ?_⟩
  intro a ha
  have hle : Nat.find hex ≤ F.rank a := Nat.find_min' hex ⟨a, ha, rfl⟩
  omega

/-- Every component has a member whose negative windows all occur in x.
No rootedness or supplier-closure hypothesis is assumed. -/
theorem component_root_windows {B : Type*} (F : Family α B)
    (x : Letters α) (n L : ℕ) (hgen : F.Generating x n L) (b : B) :
    ∃ r, F.Connected L r b ∧
      ∀ i, i ≤ F.extra r false → RecoveryPaths.Occurs x n (F.path r false) i L := by
  obtain ⟨r, hr, hmin⟩ := F.exists_minimal_in_component L b
  refine ⟨r, hr, ?_⟩
  intro i hi
  rcases hgen r i hi with hx | ⟨a, side, j, hearlier, hj, hgram⟩
  · exact hx
  · have hadj : F.Adjacent L r a := F.supplier_adjacent L r a side i j hi hj hgram
    have haconn : F.Connected L a b :=
      Relation.EqvGen.trans a r b
        (Relation.EqvGen.symm r a (Relation.EqvGen.rel r a hadj)) hr
    have hle := hmin a haconn
    omega

/-- A component root's entire negative word is a genuine contiguous subword of x. -/
theorem component_root_subword {B : Type*} (F : Family α B)
    (x : Letters α) (n k L : ℕ) (hx : KUnique x n k) (hk : k < L)
    (hgen : F.Generating x n L) (b : B) :
    ∃ r a, F.Connected L r b ∧
      a + (L + F.extra r false) ≤ n ∧
      Agree x a (F.path r false) 0 (L + F.extra r false) := by
  obtain ⟨r, hr, hwindows⟩ := F.component_root_windows x n L hgen b
  obtain ⟨a, ha, hagree⟩ := RecoveryPaths.all_windows_occur_implies_subword
    x (F.path r false) n k L (F.extra r false) hx hk hwindows
  exact ⟨r, a, hr, ha, hagree⟩


end Family

end DeletionGeneralization.RecoveryRoots

-- Source module: RecoveryModel
namespace DeletionGeneralization.RecoveryModel
open RecoveryWords RecoveryMemory RecoveryWindows RecoveryHeader RecoveryDecoder
universe u
variable {α : Type u} [DecidableEq α] [Inhabited α] {B : Type*}

structure Model (B : Type*) (α : Type u) (x : ℕ → α) (n k L b : ℕ) where
  header : B → Header α L b
  negative : B → ℕ → α
  schedule : Recovery.Data B
  bk : b ≤ k
  valid : ∀ a, Valid (header a) k
  correct : ∀ a, Correct (header a) (negative a)
  base_occurrence : ∀ a w, schedule.source a w=none →
    ∃ j, j+L ≤ n ∧ Agree x j (negative a) (windowStart (extraLength (header a)) w) L
  supplier_occurrence : ∀ a w s, schedule.source a w=some s →
    ∃ side j, j+L ≤ pathLength (header s) side ∧
      Agree (negative a) (windowStart (extraLength (header a)) w)
        (path (header s) (negative s) side) j L
  adjacent_seed : ∀ a c, schedule.adjacent a c →
    ∃ sa sc i j, i+k ≤ pathLength (header a) sa ∧ j+k ≤ pathLength (header c) sc ∧
      Agree (path (header a) (negative a) sa) i (path (header c) (negative c) sc) j k
  root_occurrence : ∀ a, schedule.root a →
    ∃ j, j+negativeLength (header a) ≤ n ∧ Agree x j (negative a) 0 (negativeLength (header a))

variable {x : ℕ → α} {n k L b : ℕ}

def Model.Sound (M : Model B α x n k L b) (mem : B → Memory α) : Prop :=
  ∀ a, RecoveryMemory.Sound (mem a) (M.negative a) (negativeLength (M.header a))

def Model.Realizes (M : Model B α x n k L b) (s : Recovery.State B) (mem : B → Memory α) : Prop :=
  RecoveryWindows.Realizes s mem (fun a => extraLength (M.header a)) L k

structure Model.Invariant [DecidableEq B] (M : Model B α x n k L b)
    (s : Recovery.State B) (mem : B → Memory α) : Prop where
  wellFormed : s.WellFormed M.schedule
  sound : M.Sound mem
  realizes : M.Realizes s mem

theorem Model.length_eq (M : Model B α x n k L b) (a : B) :
    L+extraLength (M.header a)=negativeLength (M.header a) := by
  have h := (M.valid a).2.1
  unfold extraLength
  omega

theorem Model.window_bound (M : Model B α x n k L b) (a : B) (w : Recovery.Slot) :
    windowStart (extraLength (M.header a)) w+L ≤ negativeLength (M.header a) := by
  have h := start_le (extraLength (M.header a)) w
  have heq := M.length_eq a
  omega

theorem Model.complete_known (M : Model B α x n k L b) (s : Recovery.State B)
    (mem : B → Memory α) (hr : M.Realizes s mem) (a : B) (hc : s.Complete a) :
    WindowKnown (mem a) 0 (negativeLength (M.header a)) := by
  rw [←M.length_eq a]
  exact hr.complete s mem _ L k a (by have h := (M.valid a).2.2;omega) hc

theorem Model.sound_update [DecidableEq B] (M : Model B α x n k L b)
    (mem : B → Memory α) (hs : M.Sound mem) (a : B) (next : Memory α)
    (hn : RecoveryMemory.Sound next (M.negative a) (negativeLength (M.header a))) :
    M.Sound (Function.update mem a next) := by
  intro c
  by_cases hca : c=a
  · subst c
    simpa using hn
  · simpa [Function.update,hca] using hs c

theorem Model.path_lt (M : Model B α x n k L b) (a : B) (side : Bool) :
    pathLength (M.header a) side < 3*L := by
  have hleft := (M.header a).left.isLt
  have hright := (M.header a).right.isLt
  have hu := (M.header a).removed.isLt
  have hv := (M.header a).inserted.isLt
  have hk := (M.valid a).2.2
  have hb := M.bk
  cases side <;> simp only [pathLength,Bool.false_eq_true,ite_false,ite_true,
    negativeLength,positiveLength] <;> omega

theorem Model.offset_lt (M : Model B α x n k L b) (a : B) (side : Bool)
    (i len : ℕ) (h : i+len ≤ pathLength (M.header a) side) : i < 3*L := by
  have hh := M.path_lt a side
  omega

end DeletionGeneralization.RecoveryModel

-- Source module: RecoveryProgress
namespace DeletionGeneralization.RecoveryProgress
open RecoveryWords RecoveryMemory RecoveryWindows RecoveryHeader RecoveryDecoder RecoveryModel Recovery
universe u
variable {α : Type u} [DecidableEq α] [Inhabited α]
variable {B : Type*} [DecidableEq B] {x : ℕ → α} {n k L b : ℕ}

theorem start_correct (h : Header α L b) (p : ℕ → α) (mem : Memory α)
    (k : ℕ) (hbk : b ≤ k) (hv : Valid h k) (hc : Correct h p)
    (hs : Sound mem p (negativeLength h)) (side : Bool) (a : ℕ)
    (bits : Fin k → α) (ha : a+k ≤ pathLength h side)
    (hbits : ∀ i, bits i=path h p side (a+i.val)) :
    ∃ w extra next, start h k hbk mem side a bits extra=some next ∧
      Sound next p (negativeLength h) ∧ Extends mem next ∧
      SeedKnown next (windowStart (extraLength h) w) L k := by
  have hlen : L+extraLength h=negativeLength h := by
    have h := hv.2.1
    unfold extraLength
    omega
  cases side with
  | false =>
    obtain ⟨next,hn,hsound,hext,hread⟩ := writeBits_correct mem p (negativeLength h) a k
      hs ha bits hbits
    obtain ⟨w,hw⟩ := seed_selects next (extraLength h) L k a hv.2.2
      (by simpa [hlen,pathLength] using ha) ⟨bits,hread⟩
    exact ⟨w,fun _ => default,next,by simpa [start] using hn,hsound,hext,hw⟩
  | true =>
    obtain ⟨extra,hbound,hmatch⟩ := transfer_correct h k a hbk p hv hc bits ha hbits
    let out := transfer h k a hbk bits extra
    obtain ⟨next,hn,hsound,hext,hread⟩ := writeBits_correct mem p (negativeLength h) out.1 k
      hs hbound out.2 hmatch
    obtain ⟨w,hw⟩ := seed_selects next (extraLength h) L k out.1 hv.2.2
      (by simpa only [hlen] using hbound) ⟨out.2,hread⟩
    exact ⟨w,extra,next,by simpa only [start,ite_true] using hn,hsound,hext,hw⟩

theorem execute_start (M : Model B α x n k L b) (s : State B) (mem : B → Memory α)
    (hi : M.Invariant s mem) (source : B) (ss : Bool) (so : ℕ)
    (dest : B) (ds : Bool) (d : ℕ) (bits : Fin k → α)
    (hread : readPath (M.header source) (mem source) ss so k=some bits)
    (hbound : d+k ≤ pathLength (M.header dest) ds)
    (hmatch : ∀ i, bits i=path (M.header dest) (M.negative dest) ds (d+i.val)) :
    ∃ w extra mem',
      execute x n k M.bk M.header mem (.start source ss so dest ds d extra)=some mem' ∧
      M.Invariant (s.start dest w) mem' := by
  obtain ⟨w,extra,next,hn,hsound,hext,hseed⟩ := start_correct (M.header dest) (M.negative dest)
    (mem dest) k M.bk (M.valid dest) (M.correct dest) (hi.sound dest) ds d bits hbound hmatch
  have hext' : ∀ a, Extends (mem a) (Function.update mem dest next a) := by
    intro a
    by_cases ha : a=dest
    · subst a;simpa using hext
    · simpa [Function.update,ha] using (show Extends (mem a) (mem a) from fun _ _ h => h)
  have hreal := hi.realizes.mono s mem (Function.update mem dest next) _ L k hext'
  refine ⟨w,extra,Function.update mem dest next,?_,?_⟩
  · simp only [execute,hread,Option.bind_some,hn,Option.map_some]
  · refine ⟨State.start_wellFormed M.schedule s hi.wellFormed dest w,
      M.sound_update mem hi.sound dest next hsound,?_⟩
    apply hreal.start s _ _ L k dest w
    simpa using hseed

theorem fill_invariant (M : Model B α x n k L b) (s : State B) (mem : B → Memory α)
    (hi : M.Invariant s mem) (dest : B) (w : Slot) (next : Memory α)
    (hstep : Step M.schedule s (s.fill dest w))
    (hs : Sound next (M.negative dest) (negativeLength (M.header dest)))
    (hext : Extends (mem dest) next)
    (hknown : WindowKnown next (windowStart (extraLength (M.header dest)) w) L) :
    M.Invariant (s.fill dest w) (Function.update mem dest next) := by
  have hext' : ∀ a, Extends (mem a) (Function.update mem dest next a) := by
    intro a
    by_cases ha : a=dest
    · subst a;simpa using hext
    · simpa [Function.update,ha] using (show Extends (mem a) (mem a) from fun _ _ h => h)
  have hreal := hi.realizes.mono s mem (Function.update mem dest next) _ L k hext'
  refine ⟨step_preserves M.schedule hstep hi.wellFormed,
    M.sound_update mem hi.sound dest next hs,?_⟩
  apply hreal.fill s _ _ L k dest w
  simpa using hknown

theorem lift_step [Fintype B] (M : Model B α x n k L b) (hx : KUnique x n k)
    (s : State B) (mem : B → Memory α) (hi : M.Invariant s mem)
    {q : State B} (step : Step M.schedule s q) :
    ∃ q' mem' instruction,
      Step M.schedule s q' ∧ execute x n k M.bk M.header mem instruction=some mem' ∧
      M.Invariant q' mem' ∧
      q'.startedSet.card=s.startedSet.card+isStart instruction ∧ Bounded L instruction := by
  cases step with
  | startAdjacent a c w ha hac hc =>
    obtain ⟨sa,sc,i,j,hib,hjb,hagree⟩ := M.adjacent_seed a c hac
    obtain ⟨bits,hread,hmatch⟩ := readPath_complete (M.header a) (M.negative a) (mem a) sa i k
      (hi.sound a) (M.complete_known s mem hi.realizes a ha) hib
    have htarget : ∀ z, bits z=path (M.header c) (M.negative c) sc (j+z.val) :=
      fun z => (hmatch z).trans (hagree z.val z.isLt)
    obtain ⟨v,extra,mem',hex,hinv⟩ := execute_start M s mem hi a sa i c sc j bits hread hjb htarget
    refine ⟨s.start c v,mem',.start a sa i c sc j extra,
      Step.startAdjacent s a c v ha hac hc,hex,hinv,?_,?_⟩
    · have hscore := State.score_start s c v hc
      change (s.start c v).startedSet.card=s.startedSet.card+1
      change (s.start c v).startedSet.card+s.filled.card=s.startedSet.card+s.filled.card+1 at hscore
      omega
    · exact ⟨M.offset_lt a sa i k hib,M.offset_lt c sc j k hjb⟩
  | startSupplier c a w v hr hn hsrc ha =>
    obtain ⟨r,seed,hrb,hrd⟩ := hi.realizes.ready s mem _ L k c w (M.valid c).2.2 hr
    obtain ⟨side,j,hjb,hagree⟩ := M.supplier_occurrence c w a hsrc
    have hwindow := M.window_bound c w
    have hsource : windowStart (extraLength (M.header c)) w+r+k ≤ negativeLength (M.header c) := by omega
    have htarget : j+r+k ≤ pathLength (M.header a) side := by omega
    have hmatch := readBits_sound (mem c) (M.negative c) (negativeLength (M.header c))
      (windowStart (extraLength (M.header c)) w+r) k (hi.sound c) hsource seed hrd
    have hm : ∀ z, seed z=path (M.header a) (M.negative a) side (j+r+z.val) := by
      intro z
      have hz : r+z.val < L := by have := z.isLt;omega
      exact (hmatch z).trans (by simpa only [Nat.add_assoc] using hagree (r+z.val) hz)
    have hread : readPath (M.header c) (mem c) false
        (windowStart (extraLength (M.header c)) w+r) k=some seed := by
      simpa [readPath,pathLength,hsource] using hrd
    obtain ⟨v',extra,mem',hex,hinv⟩ := execute_start M s mem hi c false
      (windowStart (extraLength (M.header c)) w+r) a side (j+r) seed hread htarget hm
    refine ⟨s.start a v',mem',.start c false (windowStart (extraLength (M.header c)) w+r)
      a side (j+r) extra,Step.startSupplier s c a w v' hr hn hsrc ha,hex,hinv,?_,?_⟩
    · have hscore := State.score_start s a v' ha
      change (s.start a v').startedSet.card=s.startedSet.card+1
      change (s.start a v').startedSet.card+s.filled.card=s.startedSet.card+s.filled.card+1 at hscore
      omega
    · exact ⟨M.offset_lt c false _ k hsource,M.offset_lt a side _ k htarget⟩
  | fillBase c w hr hn hsrc =>
    obtain ⟨r,seed,hrb,hrd⟩ := hi.realizes.ready s mem _ L k c w (M.valid c).2.2 hr
    obtain ⟨next,hex,hsound,hext,hknown⟩ := RecoveryFill.fillFromBase_correct x (M.negative c)
      n k L (mem c) (negativeLength (M.header c)) (windowStart (extraLength (M.header c)) w)
      r seed hx (hi.sound c) (M.window_bound c w) hrb hrd (M.base_occurrence c w hsrc)
    have hstep := Step.fillBase s c w hr hn hsrc
    refine ⟨s.fill c w,Function.update mem c next,.fillBase c w r,hstep,?_,?_,?_,?_⟩
    · simp only [execute,hex,Option.map_some]
    · exact fill_invariant M s mem hi c w next hstep hsound hext ⟨_,hknown⟩
    · rfl
    · change r < 3*L
      have hL := (M.header c).left.isLt
      omega
  | fillSupplier c a w hr hn hsrc ha =>
    obtain ⟨side,j,hjb,hagree⟩ := M.supplier_occurrence c w a hsrc
    obtain ⟨bits,hread,hmatch⟩ := readPath_complete (M.header a) (M.negative a) (mem a)
      side j L (hi.sound a) (M.complete_known s mem hi.realizes a ha) hjb
    have hm : Matches bits (M.negative c) (windowStart (extraLength (M.header c)) w) :=
      fun z => (hmatch z).trans (hagree z.val z.isLt).symm
    obtain ⟨next,hex,hsound,hext,hknown⟩ := writeBits_correct (mem c) (M.negative c)
      (negativeLength (M.header c)) (windowStart (extraLength (M.header c)) w) L
      (hi.sound c) (M.window_bound c w) bits hm
    have hstep := Step.fillSupplier s c a w hr hn hsrc ha
    refine ⟨s.fill c w,Function.update mem c next,.fillSupplier a side j c w,hstep,?_,?_,?_,?_⟩
    · simp only [execute,hread,Option.bind_some,hex,Option.map_some]
    · exact fill_invariant M s mem hi c w next hstep hsound hext ⟨_,hknown⟩
    · rfl
    · exact M.offset_lt a side j L hjb

end DeletionGeneralization.RecoveryProgress

-- Source module: RecoveryInitialization
namespace DeletionGeneralization.RecoveryInitialization
open RecoveryWords RecoveryMemory RecoveryWindows RecoveryHeader RecoveryDecoder RecoveryModel Recovery
universe u
variable {α : Type u} [DecidableEq α] [Inhabited α]
variable {B : Type*} [DecidableEq B] {x : ℕ → α} {n k L b : ℕ}

def ValidRoots (M : Model B α x n k L b) (records : List (B × ℕ)) : Prop :=
  ∀ a j, (a,j) ∈ records → j+negativeLength (M.header a) ≤ n ∧
    Agree x j (M.negative a) 0 (negativeLength (M.header a))

theorem load_correct (M : Model B α x n k L b) (records : List (B × ℕ))
    (mem : B → Memory α) (hs : M.Sound mem) (hv : ValidRoots M records) :
    ∃ result, loadRoots x n M.header mem records=some result ∧ M.Sound result ∧
      (∀ a, Extends (mem a) (result a)) ∧
      ∀ a j, (a,j) ∈ records → WindowKnown (result a) 0 (negativeLength (M.header a)) := by
  induction records generalizing mem with
  | nil =>
    exact ⟨mem,rfl,hs,fun _ _ _ h => h,by simp⟩
  | cons record rest ih =>
    rcases record with ⟨a,j⟩
    have ho := hv a j (by simp)
    obtain ⟨next,hn,hsound,hext,hread⟩ := RecoveryFill.loadRoot_correct x (M.negative a) n j
      (negativeLength (M.header a)) (mem a) (negativeLength (M.header a))
      (hs a) ho.1 le_rfl ho.2
    have hnext := M.sound_update mem hs a next hsound
    have htail : ValidRoots M rest := fun c z hz => hv c z (by simp [hz])
    obtain ⟨result,hresult,hrsound,hrext,hrknown⟩ := ih (Function.update mem a next) hnext htail
    have hstep : ∀ c, Extends (mem c) (Function.update mem a next c) := by
      intro c
      by_cases hca : c=a
      · subst c;simpa using hext
      · simpa [Function.update,hca] using (show Extends (mem c) (mem c) from fun _ _ h => h)
    refine ⟨result,?_,hrsound,fun c z v hz => hrext c z v (hstep c z v hz),?_⟩
    · simpa only [loadRoots,hn,Option.bind_some] using hresult
    · intro c z hz
      rcases List.mem_cons.mp hz with heq | hrest
      · cases heq
        apply known_mono (Function.update mem a next a) (result a) 0
          (negativeLength (M.header a)) (hrext a)
        simpa using (show WindowKnown next 0 (negativeLength (M.header a)) from ⟨_,hread⟩)
      · exact hrknown c z hrest

noncomputable def rootCount [Fintype B] (M : Model B α x n k L b) : ℕ := by
  classical
  exact (Finset.univ.filter M.schedule.root).card

theorem roots_exist [Fintype B] (M : Model B α x n k L b) :
    ∃ records : List (B × ℕ), records.length=rootCount M ∧ ValidRoots M records ∧
      ∀ a, M.schedule.root a → ∃ j, (a,j) ∈ records := by
  classical
  let roots := Finset.univ.filter M.schedule.root
  let pos : B → ℕ := fun a => if hr : M.schedule.root a then Classical.choose (M.root_occurrence a hr) else 0
  let records := roots.toList.map (fun a => (a,pos a))
  have hpos : ∀ a, M.schedule.root a →
      pos a+negativeLength (M.header a) ≤ n ∧
      Agree x (pos a) (M.negative a) 0 (negativeLength (M.header a)) := by
    intro a ha
    dsimp [pos]
    rw [dif_pos ha]
    exact Classical.choose_spec (M.root_occurrence a ha)
  refine ⟨records,by simp [records,roots,rootCount],?_,?_⟩
  · intro a j hmem
    obtain ⟨c,hc,heq⟩ := List.mem_map.mp hmem
    have hroot : M.schedule.root c := by simpa [roots] using hc
    have hh := hpos c hroot
    cases heq
    exact hh
  · intro a ha
    exact ⟨pos a,List.mem_map.mpr ⟨a,by simpa [roots] using ha,rfl⟩⟩

theorem initialization [Fintype B] (M : Model B α x n k L b) :
    ∃ records mem, records.length=rootCount M ∧
      loadRoots x n M.header (fun _ => empty) records=some mem ∧ ValidRoots M records ∧
      M.Invariant (initial M.schedule) mem := by
  classical
  obtain ⟨records,hlen,hvalid,hroots⟩ := roots_exist M
  have hempty : M.Sound (fun _ => empty) := fun a =>
    empty_sound (M.negative a) (negativeLength (M.header a))
  obtain ⟨mem,hload,hsound,_,hknown⟩ := load_correct M records (fun _ => empty) hempty hvalid
  have hroot : ∀ a, M.schedule.root a → WindowKnown (mem a) 0 (negativeLength (M.header a)) := by
    intro a ha
    obtain ⟨j,hj⟩ := hroots a ha
    exact hknown a j hj
  refine ⟨records,mem,hlen,hload,hvalid,initial_wellFormed M.schedule,hsound,?_,?_⟩
  · intro a w hseed
    by_cases ha : M.schedule.root a
    · have hw : w=0 := by simpa [initial,ha] using hseed.symm
      subst w
      have hkL : k ≤ L := by have h := (M.valid a).2.2;omega
      have hk : k ≤ negativeLength (M.header a) := by have h := (M.valid a).2.1;omega
      obtain ⟨bits,hread⟩ := subblock (mem a) 0 (negativeLength (M.header a)) 0 k
        (hroot a ha) le_rfl (by omega)
      exact ⟨0,bits,by omega,by simpa [windowStart] using hread⟩
    · simp [initial,ha] at hseed
  · intro a w hdone
    have ha : M.schedule.root a := by simpa [State.Done,initial] using hdone
    exact subblock (mem a) 0 (negativeLength (M.header a)) (windowStart (extraLength (M.header a)) w)
      L (hroot a ha) (by omega) (by simpa using M.window_bound a w)

end DeletionGeneralization.RecoveryInitialization

-- Source module: RecoveryRun
namespace DeletionGeneralization.RecoveryRun
open RecoveryWords RecoveryMemory RecoveryWindows RecoveryHeader RecoveryDecoder RecoveryModel Recovery
universe u
variable {α : Type u} [DecidableEq α] [Inhabited α]
variable {B : Type*} [Fintype B] [DecidableEq B] {x : ℕ → α} {n k L b : ℕ}

theorem bounded (M : Model B α x n k L b) (hx : KUnique x n k)
    (s : State B) (mem : B → Memory α) (hi : M.Invariant s mem) :
    ∃ ins mem' q, run x n k M.bk M.header mem ins=some mem' ∧
      M.Invariant q mem' ∧ (∀ a, q.Complete a) ∧
      ins.length+s.score ≤ 4*Fintype.card B ∧
      starts ins+s.startedSet.card=q.startedSet.card ∧ (∀ i ∈ ins, Bounded L i) := by
  classical
  let N := 4*Fintype.card B
  have aux : ∀ d : ℕ, ∀ s : State B, ∀ mem : B → Memory α,
      N-s.score=d → M.Invariant s mem →
      ∃ ins mem' q, run x n k M.bk M.header mem ins=some mem' ∧
        M.Invariant q mem' ∧ (∀ a, q.Complete a) ∧
        ins.length+s.score ≤ N ∧ starts ins+s.startedSet.card=q.startedSet.card ∧ (∀ i ∈ ins, Bounded L i) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro s mem hd hi
      by_cases hdone : ∀ a, s.Complete a
      · refine ⟨[],mem,s,rfl,hi,hdone,?_,?_,by simp⟩
        · simpa [N] using State.score_le s
        · simp [starts]
      · obtain ⟨q,hstep⟩ := progress M.schedule s hi.wellFormed hdone
        obtain ⟨q',mem',instr,hstep',hex,hinv,hstarts,hinsBound⟩ := RecoveryProgress.lift_step M hx s mem hi hstep
        have hscore := step_score M.schedule hstep'
        have hbound : q'.score ≤ N := State.score_le q'
        have hlt : N-q'.score < d := by omega
        obtain ⟨ins,mem'',q'',hrun,hfinal,hcomplete,hcost,hcount,hbounds⟩ :=
          ih (N-q'.score) hlt q' mem' rfl hinv
        refine ⟨instr::ins,mem'',q'',?_,hfinal,hcomplete,?_,?_,?_⟩
        · simp only [run,hex,Option.bind_some]
          exact hrun
        · simp only [List.length_cons]
          omega
        · simp only [starts,List.map_cons,List.sum_cons] at hcount ⊢
          omega
        · intro i hi
          rcases List.mem_cons.mp hi with rfl | hi
          · exact hinsBound
          · exact hbounds i hi
  exact aux (N-s.score) s mem rfl hi

def finish (header : B → Header α L b) (mem : B → Memory α) :
    Option ((a : B) → Fin (negativeLength (header a)) → α) :=
  if ∀ a, (readBits (mem a) 0 (negativeLength (header a))).isSome then
    some (fun a => (readBits (mem a) 0 (negativeLength (header a))).getD (fun _ => default))
  else none

theorem finish_correct (M : Model B α x n k L b) (mem : B → Memory α)
    (hs : M.Sound mem) (hk : ∀ a, WindowKnown (mem a) 0 (negativeLength (M.header a))) :
    finish M.header mem=some (fun a i => M.negative a i.val) := by
  have heq : ∀ a, readBits (mem a) 0 (negativeLength (M.header a))=
      some (fun i => M.negative a i.val) := by
    intro a
    obtain ⟨bits,hread⟩ := hk a
    have hb : bits=(fun i => M.negative a i.val) := by
      funext i
      simpa only [Nat.zero_add] using readBits_sound (mem a) (M.negative a)
        (negativeLength (M.header a)) 0 (negativeLength (M.header a)) (hs a)
        (by omega) bits hread i
    simpa only [hb] using hread
  simp [finish,heq]

def decode (x : ℕ → α) (n k : ℕ) (hbk : b ≤ k) (header : B → Header α L b)
    (roots : List (B × ℕ)) (ins : List (Instruction B α b)) :
    Option ((a : B) → Fin (negativeLength (header a)) → α) :=
  (loadRoots x n header (fun _ => empty) roots).bind fun mem =>
    (run x n k hbk header mem ins).bind (finish header)

theorem exists_record (M : Model B α x n k L b) (hx : KUnique x n k) :
    ∃ roots ins, roots.length=RecoveryInitialization.rootCount M ∧
      (∀ r ∈ roots, r.2 < n) ∧
      ins.length ≤ 4*Fintype.card B ∧ starts ins ≤ Fintype.card B ∧
      (∀ i ∈ ins, Bounded L i) ∧
      decode x n k M.bk M.header roots ins=some (fun a i => M.negative a i.val) := by
  obtain ⟨roots,mem,hroots,hload,hvalid,hi⟩ := RecoveryInitialization.initialization M
  obtain ⟨ins,mem',q,hrun,hinv,hdone,hlen,hstarts,hbounds⟩ := bounded M hx (initial M.schedule) mem hi
  have hcard : q.startedSet.card ≤ Fintype.card B := Finset.card_le_univ _
  refine ⟨roots,ins,hroots,?_,by omega,by omega,hbounds,?_⟩
  · rintro ⟨a,j⟩ hj
    have h := (hvalid a j hj).1
    have hl := (M.valid a).2.1
    have hpos := (M.header a).left.isLt
    dsimp only
    omega
  · simp only [decode,hload,Option.bind_some,hrun]
    apply finish_correct M mem' hinv.sound
    intro a
    exact M.complete_known q mem' hinv.realizes a (hdone a)

end DeletionGeneralization.RecoveryRun

-- Source module: RecoveryFamily
namespace DeletionGeneralization.RecoveryFamily
open RecoveryWords RecoveryHeader RecoveryWindows RecoveryRoots RecoveryModel
universe u
variable {α : Type u} [DecidableEq α] [Inhabited α]

structure EditedFamily (B : Type*) (α : Type u) (k L d : ℕ) where
  header : B → Header α L d
  negative : B → ℕ → α
  rank : B → ℕ
  bk : d ≤ k
  k_lt : k < L
  valid : ∀ a, Valid (header a) k
  correct : ∀ a, Correct (header a) (negative a)
  positive_lower : ∀ a, L ≤ positiveLength (header a)

variable {B : Type*} {k L d : ℕ}

def EditedFamily.family (E : EditedFamily B α k L d) : Family α B where
  rank := E.rank
  path a side := path (E.header a) (E.negative a) side
  extra a side := pathLength (E.header a) side-L

theorem EditedFamily.path_length_eq (E : EditedFamily B α k L d) (a : B) (side : Bool) :
    pathLength (E.header a) side=L+E.family.extra a side := by
  have hn := (E.valid a).2.1
  have hp := E.positive_lower a
  cases side <;> simp [family,pathLength] <;> omega

theorem EditedFamily.negative_extra (E : EditedFamily B α k L d) (a : B) :
    E.family.extra a false=extraLength (E.header a) := rfl

def componentSetoid (F : Family α B) (L : ℕ) : Setoid B where
  r := F.Connected L
  iseqv := ⟨fun b => Relation.EqvGen.refl b,
    fun h => Relation.EqvGen.symm _ _ h,
    fun h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂⟩

abbrev Components (E : EditedFamily B α k L d) := Quotient (componentSetoid E.family L)

theorem component_has_root (E : EditedFamily B α k L d) (x : Letters α) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n L)
    (C : Components E) :
    ∃ b, Quotient.mk (componentSetoid E.family L) b = C ∧
      ∃ a, a + negativeLength (E.header b) ≤ n ∧
        Agree x a (E.negative b) 0 (negativeLength (E.header b)) := by
  induction C using Quotient.inductionOn with
  | _ b =>
    obtain ⟨r, a, hr, ha, hagree⟩ := E.family.component_root_subword
      x n k L hx E.k_lt hg b
    have hlen : L + E.family.extra r false = negativeLength (E.header r) :=
      (E.path_length_eq r false).symm
    rw [hlen] at ha hagree
    refine ⟨r, Quotient.sound hr, a, ?_, ?_⟩
    · exact ha
    · exact hagree

noncomputable def selectedRoot (E : EditedFamily B α k L d) (x : Letters α) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n L)
    (C : Components E) : B := Classical.choose (component_has_root E x n hx hg C)

theorem selectedRoot_spec (E : EditedFamily B α k L d) (x : Letters α) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n L)
    (C : Components E) :
    let b := selectedRoot E x n hx hg C
    Quotient.mk (componentSetoid E.family L) b = C ∧
      ∃ a, a + negativeLength (E.header b) ≤ n ∧
        Agree x a (E.negative b) 0 (negativeLength (E.header b)) :=
  Classical.choose_spec (component_has_root E x n hx hg C)

def SourceValid (E : EditedFamily B α k L d) (x : Letters α) (n : ℕ)
    (b : B) (w : Recovery.Slot) (source : Option B) : Prop :=
  match source with
  | none => ∃ a, a + L ≤ n ∧
      Agree x a (E.negative b)
        (windowStart (extraLength (E.header b)) w) L
  | some a => E.rank a < E.rank b ∧
      ∃ side j, j + L ≤ pathLength (E.header a) side ∧
        Agree (E.negative b)
          (windowStart (extraLength (E.header b)) w)
          (path (E.header a) (E.negative a) side) j L

theorem source_exists (E : EditedFamily B α k L d) (x : Letters α) (n : ℕ)
    (hg : E.family.Generating x n L) (b : B) (w : Recovery.Slot) :
    ∃ source, SourceValid E x n b w source := by
  have hvalid : windowStart (extraLength (E.header b)) w ≤ E.family.extra b false :=
    start_le _ w
  rcases hg b _ hvalid with hbase | ⟨a, side, j, hearlier, hj, hagree⟩
  · exact ⟨none, hbase⟩
  · refine ⟨some a, hearlier, side, j, ?_, hagree⟩
    rw [E.path_length_eq a side]
    omega

noncomputable def source (E : EditedFamily B α k L d) (x : Letters α) (n : ℕ)
    (hg : E.family.Generating x n L) (b : B) (w : Recovery.Slot) : Option B :=
  Classical.choose (source_exists E x n hg b w)

theorem source_spec (E : EditedFamily B α k L d) (x : Letters α) (n : ℕ)
    (hg : E.family.Generating x n L) (b : B) (w : Recovery.Slot) :
    SourceValid E x n b w (source E x n hg b w) :=
  Classical.choose_spec (source_exists E x n hg b w)

theorem adjacent_symm (F : Family α B) (L : ℕ) {a b : B} (h : F.Adjacent L a b) :
    F.Adjacent L b a := by
  obtain ⟨sa, sb, i, j, hi, hj, hbi, hbj, hagree⟩ := h
  exact ⟨sb, sa, j, i, hj, hi, hbj, hbi, fun q hq => (hagree q hq).symm⟩

private theorem reach_trans {adj : B → B → Prop} {a b c : B}
    (hab : Recovery.Reach adj a b) (hbc : Recovery.Reach adj b c) :
    Recovery.Reach adj a c := by
  induction hbc with
  | refl => exact hab
  | tail hbc hcd ih => exact Recovery.Reach.tail ih hcd

theorem connected_reach (F : Family α B) (L : ℕ) {a b : B} (h : F.Connected L a b) :
    Recovery.Reach (F.Adjacent L) a b := by
  have aux : ∀ {a b}, F.Connected L a b →
      Recovery.Reach (F.Adjacent L) a b ∧ Recovery.Reach (F.Adjacent L) b a := by
    intro a b h
    induction h with
    | rel a b h => exact ⟨Recovery.Reach.tail (Recovery.Reach.refl a) h,
        Recovery.Reach.tail (Recovery.Reach.refl b) (adjacent_symm F L h)⟩
    | refl a => exact ⟨Recovery.Reach.refl a, Recovery.Reach.refl a⟩
    | symm a b h ih => exact ⟨ih.2, ih.1⟩
    | trans a b c hab hbc ihab ihbc =>
      exact ⟨reach_trans ihab.1 ihbc.1, reach_trans ihbc.2 ihab.2⟩
  exact (aux h).1

noncomputable def schedule (E : EditedFamily B α k L d) (x : Letters α) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n L) : Recovery.Data B where
  rank := E.rank
  source := source E x n hg
  earlier b w a h := by
    have hs := source_spec E x n hg b w
    rw [h] at hs
    exact hs.1
  adjacent := E.family.Adjacent L
  root b := ∃ C, selectedRoot E x n hx hg C = b
  rooted b := by
    let C : Components E := Quotient.mk _ b
    let r := selectedRoot E x n hx hg C
    refine ⟨r, ⟨C, rfl⟩, connected_reach E.family L ?_⟩
    exact Quotient.exact (selectedRoot_spec E x n hx hg C).1

/-- Derive recovery semantics from genuine generating word paths. -/
noncomputable def model (E : EditedFamily B α k L d) (x : Letters α) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n L) : Model B α x n k L d where
  header := E.header
  negative := E.negative
  schedule := schedule E x n hx hg
  bk := E.bk
  valid := E.valid
  correct := E.correct
  base_occurrence a w h := by
    have hs := source_spec E x n hg a w
    change source E x n hg a w=none at h
    rw [h] at hs
    exact hs
  supplier_occurrence a w c h := by
    have hs := source_spec E x n hg a w
    change source E x n hg a w=some c at h
    rw [h] at hs
    exact hs.2
  adjacent_seed a c h := by
    obtain ⟨sa,sc,i,j,hi,hj,hbi,hbj,hagree⟩ := h
    have hk := E.k_lt
    refine ⟨sa,sc,i,j,?_,?_,?_⟩
    · rw [E.path_length_eq a sa]
      omega
    · rw [E.path_length_eq c sc]
      omega
    · intro q hq
      exact hagree q (by omega)
  root_occurrence a h := by
    obtain ⟨C,rfl⟩ := h
    exact (selectedRoot_spec E x n hx hg C).2

noncomputable instance [Fintype B] (E : EditedFamily B α k L d) :
    Fintype (Components E) := Fintype.ofFinite _

noncomputable def rootEquiv (E : EditedFamily B α k L d) (x : Letters α) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n L) :
    Components E ≃ {a // (model E x n hx hg).schedule.root a} where
  toFun C := ⟨selectedRoot E x n hx hg C,C,rfl⟩
  invFun a := Quotient.mk (componentSetoid E.family L) a.val
  left_inv C := (selectedRoot_spec E x n hx hg C).1
  right_inv a := by
    apply Subtype.ext
    obtain ⟨C,hC⟩ := a.property
    change selectedRoot E x n hx hg (Quotient.mk (componentSetoid E.family L) a.val)=a.val
    rw [←hC,(selectedRoot_spec E x n hx hg C).1]

theorem root_count [Fintype B] [DecidableEq B]
    (E : EditedFamily B α k L d) (x : Letters α) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n L) :
    RecoveryInitialization.rootCount (model E x n hx hg)=Fintype.card (Components E) := by
  classical
  unfold RecoveryInitialization.rootCount
  rw [←Fintype.card_subtype]
  exact (Fintype.card_congr (rootEquiv E x n hx hg)).symm

theorem exists_record [Fintype B] [DecidableEq B]
    (E : EditedFamily B α k L d) (x : Letters α) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n L) :
    ∃ roots ins, roots.length=Fintype.card (Components E) ∧
      (∀ r ∈ roots, r.2 < n) ∧
      ins.length ≤ 4*Fintype.card B ∧ RecoveryDecoder.starts ins ≤ Fintype.card B ∧
      (∀ i ∈ ins, RecoveryDecoder.Bounded L i) ∧
      RecoveryRun.decode x n k E.bk E.header roots ins=some (fun a i => E.negative a i.val) := by
  obtain ⟨roots,ins,hr,hpositions,hl,hs,hbounds,hd⟩ := RecoveryRun.exists_record (model E x n hx hg) hx
  exact ⟨roots,ins,hr.trans (root_count E x n hx hg),hpositions,hl,hs,hbounds,hd⟩

end DeletionGeneralization.RecoveryFamily

-- Source module: RecoveryList
namespace DeletionGeneralization.RecoveryList
open DeletionHash.MixedEdit RecoveryHeader
universe u
variable {α : Type u} [DecidableEq α] [Inhabited α]

def total (s : List α) : ℕ → α := fun j => s[j]?.getD default

theorem total_append (A B : List α) (i : ℕ) :
    total (A++B) i=if i < A.length then total A i else total B (i-A.length) := by
  simp only [total,List.getElem?_append]
  split_ifs <;> rfl

theorem splice_words (A U V B : List α) :
    RecoveryTransfer.splice (total (A++U++B)) A.length U.length V.length
      (fun i => total V i.val)=total (A++V++B) := by
  funext i
  by_cases hl : i < A.length
  · have hp : i < A.length+U.length := by omega
    simp [RecoveryTransfer.splice,total_append,List.append_assoc,hl]
  · by_cases hm : i < A.length+V.length
    · have hv : i-A.length < V.length := by omega
      simp [RecoveryTransfer.splice,total_append,List.append_assoc,hl,hm,hv]
    · have hx : ¬i+U.length-V.length < A.length := by omega
      have hy : ¬i+U.length-V.length-A.length < U.length := by omega
      have hz : ¬i-A.length < V.length := by omega
      have heq : i+U.length-V.length-A.length-U.length=i-A.length-V.length := by omega
      simp [RecoveryTransfer.splice,total_append,List.append_assoc,hl,hm,hx,hy,hz,heq]

def boundedLetters (s : List α) (b : ℕ) : Fin b → α := fun i => total s i.val

def header {L b : ℕ} (A U V B : List α)
    (hA : A.length < L) (hB : B.length < L) (hU : U.length ≤ b) (hV : V.length ≤ b) :
    Header α L b :=
  ⟨⟨A.length,hA⟩,⟨B.length,hB⟩,⟨U.length,by omega⟩,⟨V.length,by omega⟩,
    boundedLetters U b,boundedLetters V b⟩

theorem header_correct {L b : ℕ} (A U V B : List α)
    (hA : A.length < L) (hB : B.length < L) (hU : U.length ≤ b) (hV : V.length ≤ b) :
    Correct (header A U V B hA hB hU hV) (total (A++U++B)) := by
  intro i
  have hi : i.val < U.length := i.isLt
  simp [Correct,oldLetters,header,boundedLetters,List.append_assoc,total_append,hi]

theorem header_positive {L b : ℕ} (A U V B : List α)
    (hA : A.length < L) (hB : B.length < L) (hU : U.length ≤ b) (hV : V.length ≤ b) :
    positive (header A U V B hA hB hU hV) (total (A++U++B))=total (A++V++B) := by
  exact splice_words A U V B

theorem bubble_header {k L b : ℕ} (hL : L=3*(k+b+1)) (hb : b < k)
    {P Q : List α} (h : Bubble k L b P Q) :
    ∃ H : Header α L b,
      negativeLength H=P.length ∧ positiveLength H=Q.length ∧
      Valid H k ∧ Correct H (total P) ∧ positive H (total P)=total Q := by
  obtain ⟨A,U,V,B,hP,hQ,hne,hU,hV,hAl,hAu,hBl,hBu⟩ := h.1
  have hA : A.length < L := by omega
  have hB : B.length < L := by omega
  let H := header A U V B hA hB hU hV
  have hneg : negativeLength H=P.length := by simp [H,header,negativeLength,hP,Nat.add_assoc]
  have hpos : positiveLength H=Q.length := by simp [H,header,positiveLength,hQ,Nat.add_assoc]
  refine ⟨H,hneg,hpos,?_,?_,?_⟩
  · apply geometry H k hL hAl hBl
    rw [hneg]
    exact h.2.1
  · rw [hP]
    exact header_correct A U V B hA hB hU hV
  · rw [hP,hQ]
    exact header_positive A U V B hA hB hU hV

end DeletionGeneralization.RecoveryList

-- Source module: OverlapCollision
/- Adapted from Eyal En Gad, deletion-codes-lean, commit 24d093a4 (Apache-2.0). Alphabet generalization preserves the original reconstruction proof. -/
namespace DeletionGeneralization.OverlapCollision
variable (α : Type*) [Fintype α]
abbrev Bits (n : ℕ) := Fin n → α
def padBits {n : ℕ} (x : Bits α n) (i : ℕ) : Option α :=
  if hi : i < n then some (x ⟨i, hi⟩) else none
def Agree (p : ℕ → Option α) (a : ℕ) (q : ℕ → Option α) (b k : ℕ) : Prop :=
  ∀ i, i < k → p (a+i) = q (b+i)
/-- Actual length-n words over an arbitrary finite alphabet whose indicated length-k windows agree. -/
abbrev Collision (n k a b : ℕ) :=
  {x : Bits α n // Agree α (padBits α x) a (padBits α x) b k}

noncomputable instance collisionFintype (n k a b : ℕ) :
    Fintype (Collision α n k a b) := by
  classical
  unfold Collision
  infer_instance

/-- Indices outside the later interval `[b,b+k)`, in their original order. -/
def keptIndex (n k b : ℕ) (hb : b + k ≤ n) (i : Fin (n - k)) : Fin n :=
  if h : i.val < b then ⟨i.val, by omega⟩
  else ⟨i.val + k, by omega⟩

/-- Remove exactly the later substring; retain n-k actual letters. -/
def encode (n k b : ℕ) (hb : b + k ≤ n) (x : Bits α n) : Bits α (n - k) :=
  fun i => x (keptIndex n k b hb i)

/-- Equality of encodings preserves each letter outside the removed interval. -/
theorem encode_eq_at (n k b : ℕ) (hb : b + k ≤ n)
    (x y : Bits α n) (heq : encode α n k b hb x = encode α n k b hb y)
    (j : ℕ) (hj : j < n) (hout : j < b ∨ b + k ≤ j) :
    padBits α x j = padBits α y j := by
  rcases hout with hbefore | hafter
  · have hj' : j < n - k := by omega
    have hh := congrFun heq (⟨j, hj'⟩ : Fin (n - k))
    simpa only [encode, keptIndex, dif_pos hbefore, padBits, dif_pos hj, Option.some.injEq] using hh
  · have hj' : j - k < n - k := by omega
    have hbefore : ¬j - k < b := by omega
    have hrestore : j - k + k = j := by omega
    have hh := congrFun heq (⟨j - k, hj'⟩ : Fin (n - k))
    simpa only [encode, keptIndex, dif_neg hbefore, hrestore,
      padBits, dif_pos hj, Option.some.injEq] using hh

/-- A collision reconstructs each deleted letter from a strictly earlier letter.
No disjointness of the two windows is used. -/
theorem encode_injective_of_agree (n k a b : ℕ) (hab : a < b)
    (hb : b + k ≤ n) (x y : Bits α n)
    (hx : Agree α (padBits α x) a (padBits α x) b k)
    (hy : Agree α (padBits α y) a (padBits α y) b k)
    (heq : encode α n k b hb x = encode α n k b hb y) : x = y := by
  have hall : ∀ j, j < n → padBits α x j = padBits α y j := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj
      by_cases hbefore : j < b
      · exact encode_eq_at α n k b hb x y heq j hj (Or.inl hbefore)
      by_cases hafter : b + k ≤ j
      · exact encode_eq_at α n k b hb x y heq j hj (Or.inr hafter)
      have hoffset : j - b < k := by omega
      have hearlier : a + (j - b) < j := by omega
      have hearlier_bound : a + (j - b) < n := by omega
      have hrestore : b + (j - b) = j := by omega
      have hxcopy := hx (j - b) hoffset
      have hycopy := hy (j - b) hoffset
      rw [hrestore] at hxcopy hycopy
      exact hxcopy.symm.trans ((ih (a + (j - b)) hearlier hearlier_bound).trans hycopy)
  funext j
  simpa only [padBits, dif_pos j.isLt, Option.some.injEq] using hall j.val j.isLt

def collisionEncode (n k a b : ℕ) (hb : b + k ≤ n) :
    Collision α n k a b → Bits α (n - k) :=
  fun x => encode α n k b hb x.val

theorem collisionEncode_injective (n k a b : ℕ) (hab : a < b)
    (hb : b + k ≤ n) : Function.Injective (collisionEncode α n k a b hb) := by
  intro x y heq
  apply Subtype.ext
  exact encode_injective_of_agree α n k a b hab hb x.val y.val x.property y.property heq

/-- The concrete collision set has at most q^(n-k) members, even when the
windows overlap. The earlier window bound follows already from a<b and hb. -/
theorem collision_card_le (n k a b : ℕ) (hab : a < b)
    (_ha : a + k ≤ n) (hb : b + k ≤ n) :
    Fintype.card (Collision α n k a b) ≤ Fintype.card α ^ (n - k) := by
  calc
    Fintype.card (Collision α n k a b) ≤ Fintype.card (Bits α (n - k)) :=
      Fintype.card_le_of_injective (collisionEncode α n k a b hb)
        (collisionEncode_injective α n k a b hab hb)
    _ = Fintype.card α ^ (n - k) := by simp [Bits]

end DeletionGeneralization.OverlapCollision

-- Source module: FinitePairUnion

/-!
A finite union bound over actual pairs of distinct ordered positions a < b.
Their number is derived by an explicit equivalence with a triangular sigma
type; no pair-count or union-cardinality inequality is assumed.
-/
namespace DeletionGeneralization.FinitePairUnion

open scoped BigOperators
open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev OrderedPair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- Choose the larger position b, then one of its b smaller positions. -/
def orderedPairEquiv (n : ℕ) : OrderedPair n ≃ Σ b : Fin n, Fin b.val where
  toFun p := ⟨p.val.2, ⟨p.val.1.val, p.property⟩⟩
  invFun p := ⟨(⟨p.2.val, p.2.isLt.trans p.1.isLt⟩, p.1), p.2.isLt⟩
  left_inv := by rintro ⟨⟨a, b⟩, hab⟩; rfl
  right_inv := by rintro ⟨b, a⟩; rfl

/-- The number of pairs a < b among n positions is exactly choose n 2,
including the empty cases n = 0 and n = 1. -/
theorem ordered_pair_card (n : ℕ) : Fintype.card (OrderedPair n) = n.choose 2 := by
  rw [Fintype.card_congr (orderedPairEquiv n), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id, Nat.choose_two_right]

/-- A union of events indexed by a < b has at most choose n 2 times the
maximum event size. The counted set contains each outcome only once. -/
theorem ordered_pair_union_bound {α : Type*} [Fintype α] [DecidableEq α]
    (n M : ℕ) (P : Fin n → Fin n → α → Prop)
    (hcount : ∀ a b, a < b → (univ.filter (P a b)).card ≤ M) :
    (univ.filter (fun x => ∃ a b, a < b ∧ P a b x)).card ≤ n.choose 2 * M := by
  let events : OrderedPair n → Finset α := fun p => univ.filter (P p.val.1 p.val.2)
  have hcover : univ.filter (fun x => ∃ a b, a < b ∧ P a b x) =
      (univ : Finset (OrderedPair n)).biUnion events := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, events]
    constructor
    · rintro ⟨a, b, hab, hx⟩
      exact ⟨⟨(a, b), hab⟩, hx⟩
    · rintro ⟨p, hx⟩
      exact ⟨p.val.1, p.val.2, p.property, hx⟩
  rw [hcover]
  calc
    ((univ : Finset (OrderedPair n)).biUnion events).card ≤
        (univ : Finset (OrderedPair n)).card * M :=
      Finset.card_biUnion_le_card_mul _ events M
        (fun p _ => hcount p.val.1 p.val.2 p.property)
    _ = n.choose 2 * M := by rw [Finset.card_univ, ordered_pair_card]


end

end DeletionGeneralization.FinitePairUnion

-- Source module: UniqueWordCount
namespace DeletionGeneralization.UniqueWordCount
open OverlapCollision
variable (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α]
attribute [local instance] Classical.propDecidable

def KUnique (p : ℕ → Option α) (n k : ℕ) : Prop :=
  ∀ a b, a+k ≤ n → b+k ≤ n → Agree α p a p b k → a=b
noncomputable def uniqueWords (n k : ℕ) : Finset (Bits α n) := by
  classical
  exact Finset.univ.filter (fun x => KUnique α (padBits α x) n k)

noncomputable def nonuniqueWords (n k : ℕ) : Finset (Bits α n) := by
  classical
  exact Finset.univ.filter (fun x => ¬ KUnique α (padBits α x) n k)

/-- Both starting positions are actual valid windows in the finite word. -/
def RepeatedWindow {n : ℕ} (k : ℕ) (a b : Fin n) (x : Bits α n) : Prop :=
  a.val + k ≤ n ∧ b.val + k ≤ n ∧ Agree α (padBits α x) a.val (padBits α x) b.val k

theorem not_unique_iff_pair {n k : ℕ} (hk : 1 ≤ k) (x : Bits α n) :
    ¬ KUnique α (padBits α x) n k ↔
      ∃ a b : Fin n, a < b ∧ RepeatedWindow α k a b x := by
  classical
  constructor
  · intro hx
    simp only [KUnique, not_forall] at hx
    obtain ⟨a, b, ha, hb, hab, hne⟩ := hx
    have han : a < n := by omega
    have hbn : b < n := by omega
    by_cases hlt : a < b
    · exact ⟨⟨a, han⟩, ⟨b, hbn⟩, hlt, ha, hb, hab⟩
    · refine ⟨⟨b, hbn⟩, ⟨a, han⟩, ?_, hb, ha, ?_⟩
      · change b < a
        omega
      · intro i hi
        exact (hab i hi).symm
  · rintro ⟨a, b, hlt, ha, hb, hab⟩ hx
    have heq := hx a.val b.val ha hb hab
    exact (Nat.ne_of_lt hlt) heq

theorem family_partition (n k : ℕ) :
    (uniqueWords α n k).card + (nonuniqueWords α n k).card = Fintype.card α ^ n := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Bits α n))) (fun x => KUnique α (padBits α x) n k)
  simpa only [uniqueWords, nonuniqueWords, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin] using h

theorem unique_of_length_lt {n k : ℕ} (hk : n < k) (x : Bits α n) :
    KUnique α (padBits α x) n k := by
  intro a b ha hb hab
  omega

theorem uniqueWords_eq_univ_of_length_lt {n k : ℕ} (hk : n < k) :
    uniqueWords α n k = Finset.univ := by
  classical
  ext x
  simp only [uniqueWords, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact unique_of_length_lt α hk x

theorem card_uniqueWords_of_length_lt {n k : ℕ} (hk : n < k) :
    (uniqueWords α n k).card = Fintype.card α ^ n := by
  rw [uniqueWords_eq_univ_of_length_lt α hk]
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]

/-- A fixed pair contributes at most 2^(n-k) words, with overlapping and
out-of-bounds pairs both handled explicitly. -/
theorem repeatedWindow_card_le (n k : ℕ) (a b : Fin n) (hab : a < b) :
    (Finset.univ.filter (RepeatedWindow α k a b)).card ≤ Fintype.card α ^ (n - k) := by
  classical
  by_cases ha : a.val + k ≤ n
  · by_cases hb : b.val + k ≤ n
    · have heq : (Finset.univ.filter (RepeatedWindow α k a b)).card =
          Fintype.card (OverlapCollision.Collision α n k a.val b.val) := by
        rw [Fintype.card_subtype]
        congr 1
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, RepeatedWindow, ha, hb, true_and]
      rw [heq]
      exact OverlapCollision.collision_card_le α n k a.val b.val hab ha hb
    · have hz : Finset.univ.filter (RepeatedWindow α k a b) = ∅ := by
        ext x
        simp [RepeatedWindow, hb]
      rw [hz]
      exact Nat.zero_le _
  · have hz : Finset.univ.filter (RepeatedWindow α k a b) = ∅ := by
      ext x
      simp [RepeatedWindow, ha]
    rw [hz]
    exact Nat.zero_le _

/-- Union bound on the actual nonunique family, counted once per word. -/
theorem nonunique_card_le (n k : ℕ) (hk : 1 ≤ k) :
    (nonuniqueWords α n k).card ≤ n.choose 2 * Fintype.card α ^ (n - k) := by
  classical
  have h := FinitePairUnion.ordered_pair_union_bound n (Fintype.card α ^ (n - k))
    (RepeatedWindow α k) (repeatedWindow_card_le α n k)
  simpa only [nonuniqueWords, not_unique_iff_pair α hk] using h

theorem scaled_nonunique_card_le (n k : ℕ) (hk : 1 ≤ k) :
    (nonuniqueWords α n k).card * Fintype.card α ^ k ≤ n.choose 2 * Fintype.card α ^ n := by
  by_cases hkn : k ≤ n
  · have h := Nat.mul_le_mul_right (Fintype.card α ^ k) (nonunique_card_le α n k hk)
    have hp : Fintype.card α ^ (n - k) * Fintype.card α ^ k = Fintype.card α ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hkn]
    simpa only [Nat.mul_assoc, hp] using h
  · have h := family_partition α n k
    rw [card_uniqueWords_of_length_lt α (by omega)] at h
    have hz : (nonuniqueWords α n k).card = 0 := by omega
    simp only [hz, Nat.zero_mul, Nat.zero_le]

/-- The manuscript's union-bound estimate, with the cardinality of the
actual k-unique family and no assumed collision-probability premise. -/
theorem card_unique_lower_bound (n k : ℕ) (hk : 1 ≤ k) :
    (1 - (n.choose 2 : ℚ) / (Fintype.card α : ℚ) ^ k) * (Fintype.card α : ℚ) ^ n ≤
      (uniqueWords α n k).card := by
  have hpow : (0 : ℚ) < Fintype.card α ^ k := pow_pos (by exact_mod_cast Fintype.card_pos (α := α)) _
  have hscaled : ((nonuniqueWords α n k).card : ℚ) * (Fintype.card α : ℚ) ^ k ≤
      (n.choose 2 : ℚ) * (Fintype.card α : ℚ) ^ n := by
    exact_mod_cast scaled_nonunique_card_le α n k hk
  have hbad : ((nonuniqueWords α n k).card : ℚ) ≤
      (n.choose 2 : ℚ) / (Fintype.card α : ℚ) ^ k * (Fintype.card α : ℚ) ^ n := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hpow).mpr hscaled
  have hpart : ((uniqueWords α n k).card : ℚ) + (nonuniqueWords α n k).card = (Fintype.card α : ℚ) ^ n := by
    exact_mod_cast family_partition α n k
  nlinarith

theorem card_unique_lower_bound_real (n k : ℕ) (hk : 1 ≤ k) :
    (1 - (n.choose 2 : ℝ) / (Fintype.card α : ℝ) ^ k) * (Fintype.card α : ℝ) ^ n ≤
      (uniqueWords α n k).card := by
  have h : (((1 - (n.choose 2 : ℚ) / (Fintype.card α : ℚ) ^ k) * (Fintype.card α : ℚ) ^ n : ℚ) : ℝ) ≤
      (((uniqueWords α n k).card : ℚ) : ℝ) := by
    exact_mod_cast card_unique_lower_bound α n k hk
  simpa only [Rat.cast_mul, Rat.cast_sub, Rat.cast_one, Rat.cast_div,
    Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat] using h

end DeletionGeneralization.UniqueWordCount

-- Source module: UniqueBridge
namespace DeletionGeneralization.UniqueBridge
open DeletionHash.MixedEdit
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

theorem window_as_ofFn {n k a : ℕ} (x : Word α n) (ha : a+k ≤ n) :
    window k (letters x) a = List.ofFn (fun i : Fin k => x ⟨a+i.val, by omega⟩) := by
  apply List.ext_getElem
  · simp only [window, letters, List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro i hi hj
    simp only [window, letters, List.getElem_take, List.getElem_drop, List.getElem_ofFn]

theorem window_eq_iff {n k a b : ℕ} (x : Word α n)
    (ha : a+k ≤ n) (hb : b+k ≤ n) :
    window k (letters x) a = window k (letters x) b ↔
      OverlapCollision.Agree α (OverlapCollision.padBits α x) a
        (OverlapCollision.padBits α x) b k := by
  rw [window_as_ofFn x ha, window_as_ofFn x hb, List.ofFn_inj]
  constructor
  · intro h i hi
    have he := congrFun h (⟨i, hi⟩ : Fin k)
    simpa only [OverlapCollision.padBits, dif_pos (show a+i<n by omega),
      dif_pos (show b+i<n by omega), Option.some.injEq] using he
  · intro h
    funext i
    have he := h i.val i.isLt
    simpa only [OverlapCollision.padBits, dif_pos (show a+i.val<n by omega),
      dif_pos (show b+i.val<n by omega), Option.some.injEq] using he

theorem unique_iff {n k : ℕ} (x : Word α n) :
    IsUnique k (letters x) ↔ UniqueWordCount.KUnique α (OverlapCollision.padBits α x) n k := by
  unfold IsUnique windows starts
  rw [List.nodup_map_iff_inj_on List.nodup_range]
  simp only [List.mem_range, letters, List.length_ofFn]
  constructor
  · intro h a b ha hb hab
    have hkn : k ≤ n := by omega
    apply h a (by simp only [if_pos hkn]; omega) b (by simp only [if_pos hkn]; omega)
    exact (window_eq_iff x ha hb).mpr hab
  · intro h a ha b hb hab
    by_cases hkn : k ≤ n
    · simp only [if_pos hkn] at ha hb
      exact h a b (by omega) (by omega) ((window_eq_iff x (by omega) (by omega)).mp hab)
    · simp only [if_neg hkn] at ha
      omega

theorem family_eq (n k : ℕ) : uniqueFamily α n k = UniqueWordCount.uniqueWords α n k := by
  classical
  ext x
  simp only [uniqueFamily, UniqueWordCount.uniqueWords, Finset.mem_filter,
    Finset.mem_univ, true_and, unique_iff]

end DeletionGeneralization.UniqueBridge

-- Source module: WordPaths
namespace DeletionGeneralization.WordPaths
open OverlapCollision UniqueWordCount
variable (α : Type*)
/-- A length-L window has a valid occurrence in the finite prefix of x. -/
def Occurs (x : (ℕ → Option α)) (n : ℕ) (p : (ℕ → Option α)) (i L : ℕ) : Prop :=
  ∃ a, a + L ≤ n ∧ Agree α x a p i L

/-- Two consecutive L-windows must occur consecutively in a k-unique x. -/
theorem consecutive_occurrences
    (x p : (ℕ → Option α)) (n k L i a b : ℕ)
    (hx : KUnique α x n k) (hk : k < L)
    (ha : a + L ≤ n) (hb : b + L ≤ n)
    (hleft : Agree α x a p i L) (hright : Agree α x b p (i + 1) L) :
    b = a + 1 := by
  have hmatch : Agree α x (a + 1) x b k := by
    intro j hj
    have hl := hleft (j + 1) (by omega)
    have hr := hright j (by omega)
    calc
      x (a + 1 + j) = x (a + (j + 1)) := congrArg x (by omega)
      _ = p (i + (j + 1)) := hl
      _ = p (i + 1 + j) := congrArg p (by omega)
      _ = x (b + j) := hr.symm
  exact (hx (a + 1) b (by omega) (by omega) hmatch).symm

/--
All L-windows of p occurring in x forces the whole length-(L+D) word to
occur in x. This establishes contiguity rather than taking it as a premise.
-/
theorem all_windows_occur_implies_subword
    (x p : (ℕ → Option α)) (n k L D : ℕ)
    (hx : KUnique α x n k) (hk : k < L)
    (hocc : ∀ i, i ≤ D → Occurs α x n p i L) :
    ∃ a, a + (L + D) ≤ n ∧ Agree α x a p 0 (L + D) := by
  obtain ⟨a, ha, hzero⟩ := hocc 0 (by omega)
  have aligned : ∀ i, i ≤ D →
      a + i + L ≤ n ∧ Agree α x (a + i) p i L := by
    intro i
    induction i with
    | zero =>
      intro _
      simpa only [Nat.add_zero] using And.intro ha hzero
    | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      obtain ⟨b, hb, hnext⟩ := hocc (i + 1) hi
      have heq := consecutive_occurrences α x p n k L i (a + i) b
        hx hk hprev.1 hb hprev.2 hnext
      constructor
      · omega
      · have hindex : a + (i + 1) = b := by omega
        simpa only [hindex] using hnext
  refine ⟨a, by have hlast := (aligned D le_rfl).1; omega, ?_⟩
  intro j hj
  let i := min j D
  have hiD : i ≤ D := Nat.min_le_right j D
  have hij : i ≤ j := Nat.min_le_left j D
  have hlocal : j - i < L := by
    dsimp [i]
    by_cases h : j ≤ D
    · rw [Nat.min_eq_left h]
      omega
    · rw [Nat.min_eq_right (by omega)]
      omega
  have heq := (aligned i hiD).2 (j - i) hlocal
  have hsource : a + i + (j - i) = a + j := by omega
  have htarget : i + (j - i) = 0 + j := by omega
  simpa only [hsource, htarget] using heq

/-- The full word occurrence is unique; no second root position is needed. -/
theorem subword_position_unique
    (x p : (ℕ → Option α)) (n k m a b : ℕ)
    (hx : KUnique α x n k) (hkm : k ≤ m)
    (ha : a + m ≤ n) (hb : b + m ≤ n)
    (hleft : Agree α x a p 0 m) (hright : Agree α x b p 0 m) :
    a = b := by
  apply hx a b (by omega) (by omega)
  intro i hi
  exact (hleft i (by omega)).trans (hright i (by omega)).symm

end DeletionGeneralization.WordPaths

-- Source module: SpectrumPath
namespace DeletionGeneralization.SpectrumPath
open DeletionHash.MixedEdit UniqueBridge
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

theorem nonzero_iff_mem (L : ℕ) (x : List α) (g : Gram α L) :
    spectrum L x g ≠ 0 ↔ List.ofFn g ∈ windows L x := by
  simp [DeletionHash.MixedEdit.spectrum, List.count_eq_zero]

theorem windows_mem_iff {n L : ℕ} (x : Word α n) (g : Gram α L) :
    List.ofFn g ∈ windows L (letters x) ↔
      ∃ a, a+L ≤ n ∧ window L (letters x) a = List.ofFn g := by
  unfold windows starts
  simp only [List.mem_map, List.mem_range, letters, List.length_ofFn]
  constructor
  · rintro ⟨a, ha, hg⟩
    by_cases h : L ≤ n
    · simp only [if_pos h] at ha
      exact ⟨a, by omega, hg⟩
    · simp only [if_neg h] at ha
      omega
  · rintro ⟨a, ha, hg⟩
    refine ⟨a, ?_, hg⟩
    rw [if_pos (show L ≤ n by omega)]
    omega

theorem spectrum_boolean {n L : ℕ} (y : Word α n)
    (hy : IsUnique (L-1) (letters y)) :
    ∀ g, spectrum L (letters y) g = 0 ∨ spectrum L (letters y) g = 1 := by
  have hsmall := (unique_iff y).mp hy
  have hlarge : IsUnique L (letters y) := (unique_iff y).mpr (by
    intro a b ha hb hab
    apply hsmall a b (by omega) (by omega)
    intro i hi
    exact hab i (by omega))
  intro g
  have hc := (List.nodup_iff_count_le_one.mp hlarge) (List.ofFn g)
  unfold DeletionHash.MixedEdit.spectrum
  omega

theorem spells {n L : ℕ} (y : Word α n) (hL : 1 ≤ L)
    (hy : IsUnique (L-1) (letters y)) : SpellsSimplePath L (letters y) := by
  refine ⟨hy, ?_, fun g => nonzero_iff_mem L (letters y) g⟩
  intro i hi
  have hiL : i+L ≤ n := by
    simp only [starts, letters, List.length_ofFn, List.mem_range] at hi
    split_ifs at hi <;> omega
  let g : Gram α L := fun j => y ⟨i+j.val, by omega⟩
  refine ⟨g, (window_as_ofFn y hiL).symm, ?_, ?_⟩
  · rw [window_as_ofFn y (show i+(L-1) ≤ n by omega)]
    rfl
  · rw [window_as_ofFn y (show i+1+(L-1) ≤ n by omega)]
    apply congrArg List.ofFn
    funext j
    dsimp [gramSuffix, g]
    congr 1
    apply Fin.ext
    dsimp
    omega

theorem recovers {n L : ℕ} (y z : Word α n) (hL : 1 ≤ L) (hn : L ≤ n)
    (hy : IsUnique (L-1) (letters y))
    (hs : spectrum L (letters z) = spectrum L (letters y)) : z=y := by
  have hw : ∀ i, i ≤ n-L → WordPaths.Occurs α (OverlapCollision.padBits α y) n
      (OverlapCollision.padBits α z) i L := by
    intro i hi
    have hiL : i+L ≤ n := by omega
    let g : Gram α L := fun j => z ⟨i+j.val, by omega⟩
    have hmem : List.ofFn g ∈ windows L (letters z) :=
      (windows_mem_iff z g).mpr ⟨i, hiL, window_as_ofFn z hiL⟩
    have hz := (nonzero_iff_mem L (letters z) g).mpr hmem
    rw [hs] at hz
    obtain ⟨a, ha, he⟩ := (windows_mem_iff y g).mp ((nonzero_iff_mem L (letters y) g).mp hz)
    rw [window_as_ofFn y ha, List.ofFn_inj] at he
    refine ⟨a, ha, ?_⟩
    intro j hj
    have h := congrFun he (⟨j,hj⟩ : Fin L)
    simpa only [OverlapCollision.padBits, dif_pos (show a+j<n by omega),
      dif_pos (show i+j<n by omega), Option.some.injEq, g] using h
  obtain ⟨a, ha, he⟩ := WordPaths.all_windows_occur_implies_subword α
    (OverlapCollision.padBits α y) (OverlapCollision.padBits α z) n (L-1) L (n-L)
    ((unique_iff y).mp hy) (by omega) hw
  have hl : L+(n-L)=n := by omega
  rw [hl] at ha he
  have ha0 : a=0 := by omega
  subst a
  funext j
  have h := (he j.val j.isLt).symm
  simpa only [OverlapCollision.padBits, Nat.zero_add, dif_pos j.isLt, Option.some.injEq] using h

end DeletionGeneralization.SpectrumPath

-- Source module: WindowTools
namespace DeletionGeneralization.WindowTools
open DeletionHash.MixedEdit
universe u
variable {α : Type u}

theorem window_window (x : List α) (a h i k : ℕ) (hi : i+k ≤ h) :
    window k (window h x a) i = window k x (a+i) := by
  apply List.ext_getElem
  · simp only [window, List.length_take, List.length_drop]
    omega
  · intro j hj hk
    simp only [window, List.getElem_take, List.getElem_drop, Nat.add_assoc]

theorem window_take (x : List α) (h i k : ℕ) (hi : i+k ≤ h) :
    window k (x.take h) i = window k x i := by
  simpa only [window, List.drop_zero, Nat.zero_add] using window_window x 0 h i k hi

theorem window_of_append (X P Y : List α) :
    window P.length (X++P++Y) X.length = P := by
  simp [window, List.drop_append]

theorem windows_length (k : ℕ) (x : List α) : (windows k x).length = x.length+1-k := by
  simp only [windows, starts, List.length_map, List.length_range]
  split_ifs <;> omega

theorem windows_get (k : ℕ) (x : List α) (i : ℕ) (hi : i < (windows k x).length) :
    (windows k x)[i] = window k x i := by
  simp [windows, starts, List.getElem_map, List.getElem_range]

theorem unique_positions {k : ℕ} {x : List α} :
    IsUnique k x ↔ ∀ a b, a+k ≤ x.length → b+k ≤ x.length →
      window k x a = window k x b → a=b := by
  unfold IsUnique windows starts
  rw [List.nodup_map_iff_inj_on List.nodup_range]
  simp only [List.mem_range]
  constructor
  · intro h a b ha hb he
    have hk : k ≤ x.length := by omega
    apply h a (by rw [if_pos hk]; omega) b (by rw [if_pos hk]; omega) he
  · intro h a ha b hb he
    by_cases hk : k ≤ x.length
    · simp only [if_pos hk] at ha hb
      exact h a b (by omega) (by omega) he
    · simp [hk] at ha

theorem unique_subwindow {k : ℕ} {x : List α} (hx : IsUnique k x)
    (a h : ℕ) (ha : a+h ≤ x.length) : IsUnique k (window h x a) := by
  apply unique_positions.mpr
  intro i j hi hj he
  have hlen : (window h x a).length=h := by
    simp only [window, List.length_take, List.length_drop]
    omega
  rw [hlen] at hi hj
  rw [window_window x a h i k hi, window_window x a h j k hj] at he
  have h := unique_positions.mp hx (a+i) (a+j) (by omega) (by omega) he
  omega

theorem spells_list [Fintype α] [DecidableEq α] [Nonempty α]
    (L : ℕ) (x : List α) (hL : 1 ≤ L) (hx : IsUnique (L-1) x) :
    SpellsSimplePath L x := by
  let y : Word α x.length := fun i => x.get i
  have hy : letters y=x := by simp [letters,y]
  have h := SpectrumPath.spells y hL (by rwa [hy])
  simpa only [hy] using h


theorem first_of_window (x P : List α) (a m : ℕ)
    (he : window P.length x a=P) (hm : m ≤ P.length) :
    P.take m=window m x a := by
  have h := window_window x a P.length 0 m (by omega)
  rw [he] at h
  simpa only [window,List.drop_zero,Nat.add_zero] using h

theorem last_of_window (x P : List α) (a m : ℕ)
    (he : window P.length x a=P) (hm : m ≤ P.length) :
    P.drop (P.length-m)=window m x (a+(P.length-m)) := by
  have h := window_window x a P.length (P.length-m) m (by omega)
  rw [he] at h
  have hd : (P.drop (P.length-m)).length=m := by simp only [List.length_drop]; omega
  have ht : (P.drop (P.length-m)).take m=P.drop (P.length-m) := by
    apply List.take_of_length_le
    omega
  simpa only [window,ht] using h


end DeletionGeneralization.WindowTools

-- Source module: BubbleSupport
namespace DeletionGeneralization.BubbleSupport
open DeletionHash.MixedEdit WindowTools
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem mem_windows (x : List α) (k i : ℕ) (hi : i+k ≤ x.length) :
    window k x i ∈ windows k x := by
  apply List.mem_map.mpr
  refine ⟨i,?_,rfl⟩
  simp only [starts,List.mem_range,if_pos (show k ≤ x.length by omega)]
  omega

theorem occurrence {L : ℕ} (P : List α) (hP : SpellsSimplePath L P) (g : Gram α L)
    (hg : List.ofFn g ∈ windows L P) :
    ∃ i, i+L ≤ P.length ∧ List.ofFn g=window L P i ∧
      List.ofFn (gramPrefix g)=window (L-1) P i ∧
      List.ofFn (gramSuffix g)=window (L-1) P (i+1) := by
  obtain ⟨i,hi,hgi⟩ := List.mem_map.mp hg
  obtain ⟨g',hg',hp,hs⟩ := hP.2.1 i hi
  have he : g'=g := List.ofFn_inj.mp (hg'.trans hgi)
  subst g'
  refine ⟨i,?_,hgi.symm,hp,hs⟩
  simp only [starts,List.mem_range] at hi
  split_ifs at hi <;> omega

theorem window_last (P : List α) (m : ℕ) (hm : m ≤ P.length) :
    window m P (P.length-m)=P.drop (P.length-m) := by
  unfold window
  apply List.take_of_length_le
  simp only [List.length_drop]
  omega

theorem prefix_not_last {L : ℕ} (P : List α) (hP : SpellsSimplePath L P) (hL : 1 ≤ L)
    (g : Gram α L) (hg : List.ofFn g ∈ windows L P) :
    List.ofFn (gramPrefix g) ≠ P.drop (P.length-(L-1)) := by
  obtain ⟨i,hi,hg,hpre,hsuf⟩ := occurrence P hP g hg
  intro he
  have hm : L-1 ≤ P.length := by omega
  have h := unique_positions.mp hP.1 i (P.length-(L-1)) (by omega) (by omega)
    (hpre.symm.trans (he.trans (window_last P (L-1) hm).symm))
  omega

theorem suffix_not_first {L : ℕ} (P : List α) (hP : SpellsSimplePath L P) (hL : 1 ≤ L)
    (g : Gram α L) (hg : List.ofFn g ∈ windows L P) :
    List.ofFn (gramSuffix g) ≠ P.take (L-1) := by
  obtain ⟨i,hi,hg,hpre,hsuf⟩ := occurrence P hP g hg
  intro he
  have h := unique_positions.mp hP.1 (i+1) 0 (by omega) (by omega)
    (by simpa only [window,List.drop_zero] using hsuf.symm.trans he)
  omega

theorem endpoint_mem {L : ℕ} (P : List α) (hP : SpellsSimplePath L P) (hL : 1 ≤ L)
    (g : Gram α L) (hg : List.ofFn g ∈ windows L P) :
    gramPrefix g ∈ PathVertices L P ∧ gramSuffix g ∈ PathVertices L P := by
  obtain ⟨i,hi,hg,hpre,hsuf⟩ := occurrence P hP g hg
  constructor
  · change List.ofFn (gramPrefix g) ∈ windows (L-1) P
    rw [hpre]
    exact mem_windows P (L-1) i (by omega)
  · change List.ofFn (gramSuffix g) ∈ windows (L-1) P
    rw [hsuf]
    exact mem_windows P (L-1) (i+1) (by omega)

theorem gram_spans_whole {L : ℕ} (P : List α) (hP : SpellsSimplePath L P) (hL : 1 ≤ L)
    (g : Gram α L) (hg : List.ofFn g ∈ windows L P)
    (hp : List.ofFn (gramPrefix g)=P.take (L-1))
    (hs : List.ofFn (gramSuffix g)=P.drop (P.length-(L-1))) :
    List.ofFn g=P := by
  obtain ⟨i,hi,hg,hpre,hsuf⟩ := occurrence P hP g hg
  have hi0 : i=0 := unique_positions.mp hP.1 i 0 (by omega) (by omega)
    (by simpa only [window,List.drop_zero] using hpre.symm.trans hp)
  have hiend := unique_positions.mp hP.1 (i+1) (P.length-(L-1)) (by omega) (by omega)
    (hsuf.symm.trans (hs.trans (window_last P (L-1) (by omega)).symm))
  have hlen : P.length=L := by omega
  simpa only [hi0,window,List.drop_zero,← hlen,List.take_length] using hg

theorem bubble_words_ne {k L b : ℕ} {P Q : List α} (hB : Bubble k L b P Q) : P ≠ Q := by
  obtain ⟨A,U,V,B,hP,hQ,hne,_⟩ := hB.1
  intro he
  rw [hP,hQ] at he
  exact hne (by simpa using he)

theorem bubble_grams_disjoint {k L b : ℕ} {P Q : List α}
    (hB : Bubble k L b P Q) (hL : 1 ≤ L) (g : Gram α L) :
    ¬ (List.ofFn g ∈ windows L P ∧ List.ofFn g ∈ windows L Q) := by
  intro ⟨hgP,hgQ⟩
  obtain ⟨hform,hPl,hPu,hQl,hQu,hfirst,hlast,hpathP,hpathQ,hmeet⟩ := hB
  have ep := endpoint_mem P hpathP hL g hgP
  have eq := endpoint_mem Q hpathQ hL g hgQ
  have hp := hmeet (gramPrefix g) ep.1 eq.1
  have hs := hmeet (gramSuffix g) ep.2 eq.2
  have hp' : List.ofFn (gramPrefix g)=P.take (L-1) :=
    hp.resolve_right (prefix_not_last P hpathP hL g hgP)
  have hs' : List.ofFn (gramSuffix g)=P.drop (P.length-(L-1)) :=
    hs.resolve_left (suffix_not_first P hpathP hL g hgP)
  have hP := gram_spans_whole P hpathP hL g hgP hp' hs'
  have hQ := gram_spans_whole Q hpathQ hL g hgQ (hp'.trans hfirst) (hs'.trans hlast)
  apply bubble_words_ne ⟨hform,hPl,hPu,hQl,hQu,hfirst,hlast,hpathP,hpathQ,hmeet⟩
  exact hP.symm.trans hQ

theorem spectrum_boolean {L : ℕ} (P : List α) (hP : SpellsSimplePath L P) :
    ∀ g, spectrum L P g=0 ∨ spectrum L P g=1 := by
  have hlarge : IsUnique L P := unique_positions.mpr (by
    intro i j hi hj he
    apply unique_positions.mp hP.1 i j (by omega) (by omega)
    have h := congrArg (List.take (L-1)) he
    simpa only [window,List.take_take,Nat.min_eq_left (show L-1 ≤ L by omega)] using h)
  intro g
  have h := List.nodup_iff_count_le_one.mp hlarge (List.ofFn g)
  unfold DeletionHash.MixedEdit.spectrum
  omega


theorem nonzero_iff_mem (L : ℕ) (P : List α) (g : Gram α L) :
    spectrum L P g ≠ 0 ↔ List.ofFn g ∈ windows L P := by
  simp [DeletionHash.MixedEdit.spectrum,List.count_eq_zero]

theorem difference_support {k L b : ℕ} {P Q : List α} (hB : Bubble k L b P Q)
    (hL : 1 ≤ L) (g : Gram α L) :
    (spectrum L Q-spectrum L P) g ≠ 0 ↔
      List.ofFn g ∈ windows L P ∨ List.ofFn g ∈ windows L Q := by
  have hcopy := hB
  obtain ⟨_,_,_,_,_,_,_,hP,hQ,_⟩ := hcopy
  have hp := spectrum_boolean P hP g
  have hq := spectrum_boolean Q hQ g
  have hn := bubble_grams_disjoint hB hL g
  rw [← nonzero_iff_mem L P g,← nonzero_iff_mem L Q g] at hn ⊢
  change (spectrum L Q g-spectrum L P g ≠ 0) ↔ _
  rcases hp with hp | hp <;> rcases hq with hq | hq <;> simp_all

theorem difference_values {k L b : ℕ} {P Q : List α} (hB : Bubble k L b P Q)
    (g : Gram α L) :
    (spectrum L Q-spectrum L P) g=0 ∨
      (spectrum L Q-spectrum L P) g=1 ∨ (spectrum L Q-spectrum L P) g= -1 := by
  have hcopy := hB
  obtain ⟨_,_,_,_,_,_,_,hP,hQ,_⟩ := hcopy
  have hp := spectrum_boolean P hP g
  have hq := spectrum_boolean Q hQ g
  change spectrum L Q g-spectrum L P g=0 ∨
    spectrum L Q g-spectrum L P g=1 ∨ spectrum L Q g-spectrum L P g= -1
  omega

theorem difference_endpoint {k L b : ℕ} {P Q : List α} (hB : Bubble k L b P Q)
    (hL : 1 ≤ L) (g : Gram α L) (hg : (spectrum L Q-spectrum L P) g ≠ 0) :
    gramPrefix g ∈ bubbleVertices L P Q ∧ gramSuffix g ∈ bubbleVertices L P Q := by
  have hcopy := hB
  obtain ⟨_,_,_,_,_,_,_,hP,hQ,_⟩ := hcopy
  rcases (difference_support hB hL g).mp hg with hg | hg
  · have he := endpoint_mem P hP hL g hg
    exact ⟨Or.inl he.1,Or.inl he.2⟩
  · have he := endpoint_mem Q hQ hL g hg
    exact ⟨Or.inr he.1,Or.inr he.2⟩


end DeletionGeneralization.BubbleSupport

-- Source module: CatalogueSupport
namespace DeletionGeneralization.CatalogueSupport
open DeletionHash.MixedEdit BubbleSupport
universe u v
variable {α : Type u} [Fintype α] [DecidableEq α]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

theorem distinct_piece_zero {k L b : ℕ} (B : ι → List α × List α)
    (hB : ∀ i, Bubble k L b (B i).1 (B i).2)
    (hdis : ∀ i j, i ≠ j → Disjoint (bubbleVertices L (B i).1 (B i).2)
      (bubbleVertices L (B j).1 (B j).2))
    (hL : 1 ≤ L) (i j : ι) (hij : i ≠ j) (g : Gram α L)
    (hi : (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0) :
    (spectrum L (B j).2-spectrum L (B j).1) g = 0 := by
  by_contra hj
  have hp := (difference_endpoint (hB i) hL g hi).1
  have hq := (difference_endpoint (hB j) hL g hj).1
  exact Set.disjoint_left.mp (hdis i j hij) hp hq

theorem sum_piece_eq {k L b : ℕ} (B : ι → List α × List α)
    (hB : ∀ i, Bubble k L b (B i).1 (B i).2)
    (hdis : ∀ i j, i ≠ j → Disjoint (bubbleVertices L (B i).1 (B i).2)
      (bubbleVertices L (B j).1 (B j).2))
    (hL : 1 ≤ L) (i : ι) (g : Gram α L)
    (hi : (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0) :
    (∑ j, (spectrum L (B j).2-spectrum L (B j).1)) g =
      (spectrum L (B i).2-spectrum L (B i).1) g := by
  rw [Finset.sum_apply]
  apply Finset.sum_eq_single i
  · intro j hj hji
    exact distinct_piece_zero B hB hdis hL i j hji.symm g hi
  · simp

theorem sum_support {k L b : ℕ} (B : ι → List α × List α)
    (hB : ∀ i, Bubble k L b (B i).1 (B i).2)
    (hdis : ∀ i j, i ≠ j → Disjoint (bubbleVertices L (B i).1 (B i).2)
      (bubbleVertices L (B j).1 (B j).2))
    (hL : 1 ≤ L) (g : Gram α L) :
    (∑ j, (spectrum L (B j).2-spectrum L (B j).1)) g ≠ 0 ↔
      ∃ j, (spectrum L (B j).2-spectrum L (B j).1) g ≠ 0 := by
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    apply h
    rw [Finset.sum_apply]
    exact Finset.sum_eq_zero (fun i hi => hn i)
  · rintro ⟨i,hi⟩
    rwa [sum_piece_eq B hB hdis hL i g hi]

theorem catalogue_values {k L t b : ℕ} (w : Spectrum α L)
    (hw : w ∈ Catalogue k L t b) (hL : 1 ≤ L) (g : Gram α L) :
    w g=0 ∨ w g=1 ∨ w g= -1 := by
  obtain ⟨B,hB,hdis,rfl⟩ := hw
  by_cases hn : ∃ i, (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0
  · obtain ⟨i,hi⟩ := hn
    rw [sum_piece_eq B hB hdis hL i g hi]
    exact difference_values (hB i) g
  · left
    push_neg at hn
    rw [Finset.sum_apply]
    exact Finset.sum_eq_zero (fun i hi => hn i)

theorem parity_zero_iff {k L t b : ℕ} (w : Spectrum α L)
    (hw : w ∈ Catalogue k L t b) (hL : 1 ≤ L) (g : Gram α L) :
    parity w g=0 ↔ w g=0 := by
  rcases catalogue_values w hw hL g with h | h | h <;> simp [parity,h]

theorem relation_support_subset {k L t b : ℕ} (w : Spectrum α L)
    (hw : w ∈ Catalogue k L t b) (hL : 1 ≤ L) (I : Finset (Spectrum α L))
    (hrel : parity w=∑ z ∈ I, parity z) :
    supportUnion {w} ⊆ supportUnion I := by
  intro g hg
  obtain ⟨v,hv,hvg⟩ := hg
  have hvw : v=w := Finset.mem_singleton.mp hv
  subst v
  by_contra hnone
  have hz : ∀ z ∈ I, z g=0 := by
    intro z hz
    by_contra hzg
    exact hnone ⟨z,hz,hzg⟩
  have hp : parity w g ≠ 0 := by
    intro hp
    exact hvg ((parity_zero_iff w hw hL g).mp hp)
  apply hp
  have hc := congrFun hrel g
  simp only [Finset.sum_apply] at hc
  rw [hc]
  apply Finset.sum_eq_zero
  intro z hzi
  simp [parity,hz z hzi]

end DeletionGeneralization.CatalogueSupport

-- Source module: SupportPaths
namespace DeletionGeneralization.SupportPaths
open DeletionHash.MixedEdit BubbleSupport WindowTools
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem mem_starts (P : List α) (L i : ℕ) (hi : i+L ≤ P.length) : i ∈ starts L P := by
  simp only [starts,List.mem_range,if_pos (show L ≤ P.length by omega)]
  omega

theorem vertices_incident {L : ℕ} (F : Finset (Spectrum α L)) (P : List α)
    (hP : SpellsSimplePath L P) (hL : 1 ≤ L) (hlen : L ≤ P.length)
    (hedges : ∀ g, List.ofFn g ∈ windows L P → g ∈ supportUnion F)
    (v : Gram α (L-1)) (hv : v ∈ PathVertices L P) : v ∈ incidentVertices F := by
  obtain ⟨i,hi,he⟩ := List.mem_map.mp hv
  have him : i+(L-1) ≤ P.length := by
    simp only [starts,List.mem_range,if_pos (show L-1 ≤ P.length by omega)] at hi
    omega
  by_cases hil : i+L ≤ P.length
  · obtain ⟨g,hg,hpre,hsuf⟩ := hP.2.1 i (mem_starts P L i hil)
    refine ⟨g,hedges g (by rw [hg]; exact mem_windows P L i hil),Or.inl ?_⟩
    exact List.ofFn_inj.mp (he.symm.trans hpre.symm)
  · have hipos : 1 ≤ i := by omega
    have hib : i-1+L ≤ P.length := by omega
    obtain ⟨g,hg,hpre,hsuf⟩ := hP.2.1 (i-1) (mem_starts P L (i-1) hib)
    have hidx : i-1+1=i := by omega
    rw [hidx] at hsuf
    refine ⟨g,hedges g (by rw [hg]; exact mem_windows P L (i-1) hib),Or.inr ?_⟩
    exact List.ofFn_inj.mp (he.symm.trans hsuf.symm)

theorem edge_reachable {L : ℕ} (F : Finset (Spectrum α L))
    (v w : {v : Gram α (L-1) // v ∈ incidentVertices F}) (g : Gram α L)
    (hg : g ∈ supportUnion F) (hv : v.val=gramPrefix g) (hw : w.val=gramSuffix g) :
    (supportGraph F).Reachable v w := by
  classical
  by_cases he : v=w
  · subst w
    exact SimpleGraph.Reachable.refl _
  · apply SimpleGraph.Adj.reachable
    exact ⟨he,g,hg,Or.inl ⟨hv,hw⟩⟩

def gramAt (P : List α) (i k : ℕ) (hi : i+k ≤ P.length) : Gram α k :=
  fun j => P[i+j.val]'(by omega)

theorem ofFn_gramAt (P : List α) (i k : ℕ) (hi : i+k ≤ P.length) :
    List.ofFn (gramAt P i k hi)=window k P i := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,window,List.length_take,List.length_drop]
    omega
  · intro j hj hk
    simp only [List.getElem_ofFn,gramAt,window,List.getElem_take,List.getElem_drop]


theorem path_connected {L : ℕ} (F : Finset (Spectrum α L)) (P : List α)
    (hP : SpellsSimplePath L P) (hL : 1 ≤ L) (hlen : L ≤ P.length)
    (hedges : ∀ g, List.ofFn g ∈ windows L P → g ∈ supportUnion F)
    (v w : {v : Gram α (L-1) // v ∈ incidentVertices F})
    (hv : v.val ∈ PathVertices L P) (hw : w.val ∈ PathVertices L P) :
    (supportGraph F).Reachable v w := by
  let m := L-1
  let N := P.length-m+1
  have hN : 1 ≤ N := by dsimp [N]; omega
  let V : Fin N → {v : Gram α (L-1) // v ∈ incidentVertices F} := fun q =>
    ⟨gramAt P q.val m (by have h := q.isLt; dsimp [N] at h; omega),
      vertices_incident F P hP hL hlen hedges _ (by
        change List.ofFn (gramAt P q.val m (by have h := q.isLt; dsimp [N] at h; omega)) ∈ windows m P
        rw [ofFn_gramAt]
        exact mem_windows P m q.val (by have h := q.isLt; dsimp [N] at h; omega))⟩
  have hstep : ∀ q (hq : q+1<N),
      (supportGraph F).Reachable (V ⟨q,by omega⟩) (V ⟨q+1,hq⟩) := by
    intro q hq
    have hqL : q+L ≤ P.length := by dsimp [N,m] at hq; omega
    obtain ⟨g,hg,hpre,hsuf⟩ := hP.2.1 q (mem_starts P L q hqL)
    apply edge_reachable F _ _ g (hedges g (by rw [hg]; exact mem_windows P L q hqL))
    · apply List.ofFn_inj.mp
      change List.ofFn (gramAt P q m (by dsimp [m]; omega)) = List.ofFn (gramPrefix g)
      rw [ofFn_gramAt]
      exact hpre.symm
    · apply List.ofFn_inj.mp
      change List.ofFn (gramAt P (q+1) m (by dsimp [m]; omega)) = List.ofFn (gramSuffix g)
      rw [ofFn_gramAt]
      exact hsuf.symm
  have hreach : ∀ q (hq : q<N),
      (supportGraph F).Reachable (V ⟨0,by omega⟩) (V ⟨q,hq⟩) := by
    intro q
    induction q with
    | zero =>
      intro hq
      exact SimpleGraph.Reachable.refl _
    | succ q ih =>
      intro hq
      exact (ih (by omega)).trans (hstep q hq)
  have hcover : ∀ z : {v : Gram α (L-1) // v ∈ incidentVertices F},
      z.val ∈ PathVertices L P → ∃ q, V q=z := by
    intro z hz
    obtain ⟨i,hi,he⟩ := List.mem_map.mp hz
    have hib : i+m ≤ P.length := by
      simp only [starts,List.mem_range,if_pos (show L-1 ≤ P.length by omega)] at hi
      dsimp [m]
      omega
    refine ⟨⟨i,by dsimp [N]; omega⟩,Subtype.ext ?_⟩
    apply List.ofFn_inj.mp
    change List.ofFn (gramAt P i m hib)=List.ofFn z.val
    rw [ofFn_gramAt]
    exact he
  obtain ⟨i,hi⟩ := hcover v hv
  obtain ⟨j,hj⟩ := hcover w hw
  rw [← hi,← hj]
  exact (hreach i.val i.isLt).symm.trans (hreach j.val j.isLt)


end DeletionGeneralization.SupportPaths

-- Source module: BubbleConnectivity
namespace DeletionGeneralization.BubbleConnectivity
open DeletionHash.MixedEdit BubbleSupport SupportPaths
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem bubble_connected {k L b : ℕ} (F : Finset (Spectrum α L)) (P Q : List α)
    (hB : Bubble k L b P Q) (hL : 1 ≤ L)
    (hsupport : ∀ g, (spectrum L Q-spectrum L P) g ≠ 0 → g ∈ supportUnion F) :
    ∃ r : {v : Gram α (L-1) // v ∈ incidentVertices F},
      r.val ∈ bubbleVertices L P Q ∧
      ∀ v : {v : Gram α (L-1) // v ∈ incidentVertices F},
        v.val ∈ bubbleVertices L P Q → (supportGraph F).Reachable r v := by
  have hcopy := hB
  obtain ⟨_,hPl,_,hQl,_,hfirst,_,hpathP,hpathQ,_⟩ := hcopy
  have hedgesP : ∀ g, List.ofFn g ∈ windows L P → g ∈ supportUnion F := by
    intro g hg
    exact hsupport g ((difference_support hB hL g).mpr (Or.inl hg))
  have hedgesQ : ∀ g, List.ofFn g ∈ windows L Q → g ∈ supportUnion F := by
    intro g hg
    exact hsupport g ((difference_support hB hL g).mpr (Or.inr hg))
  let v0 := gramAt P 0 (L-1) (by omega)
  have hvP : v0 ∈ PathVertices L P := by
    change List.ofFn v0 ∈ windows (L-1) P
    rw [ofFn_gramAt]
    exact mem_windows P (L-1) 0 (by omega)
  have hvQ : v0 ∈ PathVertices L Q := by
    change List.ofFn v0 ∈ windows (L-1) Q
    have h : List.ofFn v0=Q.take (L-1) := by
      rw [ofFn_gramAt]
      simpa only [window,List.drop_zero] using hfirst
    rw [h]
    simpa only [window,List.drop_zero] using mem_windows Q (L-1) 0 (by omega)
  let r : {v : Gram α (L-1) // v ∈ incidentVertices F} :=
    ⟨v0,vertices_incident F P hpathP hL hPl hedgesP v0 hvP⟩
  refine ⟨r,Or.inl hvP,?_⟩
  intro v hv
  rcases hv with hv | hv
  · exact path_connected F P hpathP hL hPl hedgesP r v hvP hv
  · exact path_connected F Q hpathQ hL hQl hedgesQ r v hvQ hv

theorem bubble_nonzero {k L b : ℕ} (P Q : List α)
    (hB : Bubble k L b P Q) (hL : 1 ≤ L) :
    ∃ g, (spectrum L Q-spectrum L P) g ≠ 0 := by
  have hPl : L ≤ P.length := hB.2.1
  let g := gramAt P 0 L (by omega)
  refine ⟨g,(difference_support hB hL g).mpr (Or.inl ?_)⟩
  rw [ofFn_gramAt]
  exact mem_windows P L 0 (by omega)

theorem bubble_vertices_eq {k L b : ℕ} (P Q : List α)
    (hB : Bubble k L b P Q) (hL : 1 ≤ L) :
    bubbleVertices L P Q=incidentVertices {spectrum L Q-spectrum L P} := by
  ext v
  constructor
  · intro hv
    have hcopy := hB
    obtain ⟨_,hPl,_,hQl,_,_,_,hP,hQ,_⟩ := hcopy
    rcases hv with hv | hv
    · apply vertices_incident _ P hP hL hPl _ v hv
      intro g hg
      exact ⟨_,Finset.mem_singleton_self _,(difference_support hB hL g).mpr (Or.inl hg)⟩
    · apply vertices_incident _ Q hQ hL hQl _ v hv
      intro g hg
      exact ⟨_,Finset.mem_singleton_self _,(difference_support hB hL g).mpr (Or.inr hg)⟩
  · rintro ⟨g,⟨z,hz,hg⟩,hv⟩
    have he : z=spectrum L Q-spectrum L P := Finset.mem_singleton.mp hz
    subst z
    have hends := difference_endpoint hB hL g hg
    rcases hv with rfl | rfl
    · exact hends.1
    · exact hends.2

end DeletionGeneralization.BubbleConnectivity

-- Source module: ComponentCover
namespace DeletionGeneralization.ComponentCover
open DeletionHash.MixedEdit BubbleSupport BubbleConnectivity CatalogueSupport
universe u v
variable {α : Type u} [Fintype α] [DecidableEq α]
variable {ι : Type v} [Fintype ι]

theorem cover_by_bubbles {k L b : ℕ} (F : Finset (Spectrum α L))
    (B : ι → List α × List α) (hB : ∀ i, Bubble k L b (B i).1 (B i).2)
    (hL : 1 ≤ L)
    (hsupport : ∀ i g, (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0 → g ∈ supportUnion F)
    (hcover : ∀ g ∈ supportUnion F, ∃ i, (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0) :
    ∃ r : ι → {v : Gram α (L-1) // v ∈ incidentVertices F},
      (∀ i, (r i).val ∈ bubbleVertices L (B i).1 (B i).2) ∧
      (∀ i (v : {v : Gram α (L-1) // v ∈ incidentVertices F}),
        v.val ∈ bubbleVertices L (B i).1 (B i).2 → (supportGraph F).Reachable (r i) v) ∧
      Function.Surjective (fun i => (supportGraph F).connectedComponentMk (r i)) := by
  classical
  choose r hr hreach using fun i => bubble_connected F (B i).1 (B i).2 (hB i) hL (hsupport i)
  refine ⟨r,hr,hreach,?_⟩
  intro C
  refine SimpleGraph.ConnectedComponent.ind ?_ C
  intro v
  obtain ⟨g,hg,hv⟩ := v.property
  obtain ⟨i,hi⟩ := hcover g hg
  have he := difference_endpoint (hB i) hL g hi
  have hvmem : v.val ∈ bubbleVertices L (B i).1 (B i).2 := by
    rcases hv with hv | hv
    · rw [hv]
      exact he.1
    · rw [hv]
      exact he.2
  exact ⟨i,SimpleGraph.ConnectedComponent.sound (hreach i v hvmem)⟩

theorem count_le_bubbles {k L b : ℕ} (F : Finset (Spectrum α L))
    (B : ι → List α × List α) (hB : ∀ i, Bubble k L b (B i).1 (B i).2)
    (hL : 1 ≤ L)
    (hsupport : ∀ i g, (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0 → g ∈ supportUnion F)
    (hcover : ∀ g ∈ supportUnion F, ∃ i, (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0) :
    componentCount F ≤ Fintype.card ι := by
  classical
  obtain ⟨r,hr,hreach,hsurj⟩ := cover_by_bubbles F B hB hL hsupport hcover
  have h := Nat.card_le_card_of_surjective _ hsurj
  simpa only [componentCount,Nat.card_eq_fintype_card] using h

theorem catalogue_count_le {k L t b : ℕ} (w : Spectrum α L)
    (hw : w ∈ Catalogue k L t b) (hL : 1 ≤ L) :
    componentCount {w} ≤ 2*t := by
  classical
  obtain ⟨B,hB,hdis,heq⟩ := hw
  have hsupport : ∀ i g, (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0 →
      g ∈ supportUnion {w} := by
    intro i g hg
    refine ⟨w,Finset.mem_singleton_self _,?_⟩
    rw [heq]
    exact (sum_support B hB hdis hL g).mpr ⟨i,hg⟩
  have hcover : ∀ g ∈ supportUnion {w},
      ∃ i, (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0 := by
    rintro g ⟨z,hz,hg⟩
    have hz : z=w := Finset.mem_singleton.mp hz
    subst z
    rw [heq] at hg
    exact (sum_support B hB hdis hL g).mp hg
  simpa only [Fintype.card_fin] using count_le_bubbles {w} B hB hL hsupport hcover

end DeletionGeneralization.ComponentCover

-- Source module: RecoveryOccurrences
namespace DeletionGeneralization.RecoveryOccurrences
open DeletionHash.MixedEdit RecoveryList RecoveryWords WindowTools BubbleSupport SupportPaths
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Inhabited α]

theorem window_total (P : List α) (a len : ℕ) (ha : a+len ≤ P.length) :
    window len P a=List.ofFn (fun i : Fin len => total P (a+i.val)) := by
  apply List.ext_getElem
  · simp only [window,List.length_take,List.length_drop,List.length_ofFn]
    omega
  · intro j hj hj'
    have hlen : j < len := by simpa only [List.length_ofFn] using hj'
    have hp : a+j < P.length := by omega
    simp [window,List.getElem_ofFn,total,List.getElem?_eq_getElem,hp]

theorem agree_iff (P Q : List α) (a c len : ℕ)
    (ha : a+len ≤ P.length) (hc : c+len ≤ Q.length) :
    Agree (total P) a (total Q) c len ↔ window len P a=window len Q c := by
  rw [window_total P a len ha,window_total Q c len hc,List.ofFn_inj]
  constructor
  · intro h
    funext i
    exact h i.val i.isLt
  · intro h i hi
    exact congrFun h ⟨i,hi⟩

theorem total_unique {k : ℕ} (P : List α) (hp : IsUnique k P) :
    KUnique (total P) P.length k := by
  intro a c ha hc hagree
  exact unique_positions.mp hp a c ha hc ((agree_iff P P a c k ha hc).mp hagree)

theorem occurrence_of_mem {L : ℕ} (P : List α) (g : Gram α L)
    (hg : List.ofFn g ∈ windows L P) :
    ∃ a, a+L ≤ P.length ∧ List.ofFn g=window L P a := by
  obtain ⟨a,ha,hg⟩ := List.mem_map.mp hg
  refine ⟨a,?_,hg.symm⟩
  simp only [starts,List.mem_range] at ha
  split_ifs at ha <;> omega

theorem agree_of_gram {L : ℕ} (P Q : List α) (a c : ℕ)
    (ha : a+L ≤ P.length) (hc : c+L ≤ Q.length) (g : Gram α L)
    (hp : List.ofFn g=window L P a) (hq : List.ofFn g=window L Q c) :
    Agree (total P) a (total Q) c L :=
  (agree_iff P Q a c L ha hc).mpr (hp.symm.trans hq)

theorem negative_value {k L b : ℕ} {P Q : List α} (hB : Bubble k L b P Q)
    (hL : 1 ≤ L) (g : Gram α L) (hg : List.ofFn g ∈ windows L P) :
    (spectrum L Q-spectrum L P) g= -1 := by
  have hp : spectrum L P g≠0 := (nonzero_iff_mem L P g).mpr hg
  have hq : spectrum L Q g=0 := by
    by_contra hn
    exact bubble_grams_disjoint hB hL g ⟨hg,(nonzero_iff_mem L Q g).mp hn⟩
  have hs := BubbleSupport.spectrum_boolean P hB.2.2.2.2.2.2.2.1 g
  change spectrum L Q g-spectrum L P g= -1
  omega

end DeletionGeneralization.RecoveryOccurrences

-- Source module: CatalogueRecovery
namespace DeletionGeneralization.CatalogueRecovery
open DeletionHash.MixedEdit RecoveryHeader RecoveryFamily RecoveryList RecoveryOccurrences
open BubbleSupport CatalogueSupport SupportPaths
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Inhabited α]
variable {n k L t b R : ℕ}

structure Pieces (G : Fin R → Spectrum α L) where
  words : Fin R → Fin (2*t) → List α × List α
  bubble : ∀ j i, Bubble k L b (words j i).1 (words j i).2
  disjoint : ∀ j i i', i≠i' → Disjoint (bubbleVertices L (words j i).1 (words j i).2)
    (bubbleVertices L (words j i').1 (words j i').2)
  sum_eq : ∀ j, G j=∑ i, (spectrum L (words j i).2-spectrum L (words j i).1)

theorem pieces_exist (G : Fin R → Spectrum α L) (hg : ∀ j, G j ∈ Catalogue k L t b) :
    Nonempty (Pieces (k:=k) (t:=t) (b:=b) G) := by
  classical
  choose B hB hdis heq using hg
  exact ⟨⟨B,hB,hdis,heq⟩⟩

def pairWord {G : Fin R → Spectrum α L} (C : Pieces (k:=k) (t:=t) (b:=b) G)
    (a : Fin R × Fin (2*t)) (side : Bool) : List α :=
  if side then (C.words a.1 a.2).2 else (C.words a.1 a.2).1

structure Representation {G : Fin R → Spectrum α L}
    (C : Pieces (k:=k) (t:=t) (b:=b) G) where
  family : EditedFamily (Fin R × Fin (2*t)) α k L b
  path_eq : ∀ a side, family.family.path a side=total (pairWord C a side)
  length_eq : ∀ a side, pathLength (family.header a) side=(pairWord C a side).length
  rank_eq : ∀ a, family.rank a=a.1.val

theorem representation {G : Fin R → Spectrum α L}
    (C : Pieces (k:=k) (t:=t) (b:=b) G)
    (hL : L=3*(k+b+1)) (hb : b < k) :
    Nonempty (Representation C) := by
  classical
  have hex (a : Fin R × Fin (2*t)) := bubble_header hL hb (C.bubble a.1 a.2)
  choose H hn hp hv hc hpos using hex
  let E : EditedFamily (Fin R × Fin (2*t)) α k L b :=
    { header := H
      negative := fun a => total (C.words a.1 a.2).1
      rank := fun a => a.1.val
      bk := by omega
      k_lt := by omega
      valid := hv
      correct := hc
      positive_lower := fun a => by rw [hp a];exact (C.bubble a.1 a.2).2.2.2.1 }
  refine ⟨⟨E,?_,?_,fun _ => rfl⟩⟩
  · intro a side
    cases side
    · rfl
    · exact hpos a
  · intro a side
    cases side
    · exact hn a
    · exact hp a

theorem generates {G : Fin R → Spectrum α L}
    (C : Pieces (k:=k) (t:=t) (b:=b) G) (E : Representation C)
    (x : Word α n) (hg : GeneratingSequence k t b (spectrum L (letters x)) G)
    (hL : 1 ≤ L) :
    E.family.family.Generating (total (letters x)) n L := by
  intro a pos hpos
  have hlen : pathLength (E.family.header a) false=L+E.family.family.extra a false :=
    E.family.path_length_eq a false
  have hbound : pos+L ≤ (C.words a.1 a.2).1.length := by
    have hh := E.length_eq a false
    change pathLength (E.family.header a) false=(C.words a.1 a.2).1.length at hh
    omega
  let g := gramAt (C.words a.1 a.2).1 pos L hbound
  have hgram : List.ofFn g=window L (C.words a.1 a.2).1 pos := ofFn_gramAt _ _ _ _
  have hmem : List.ofFn g ∈ windows L (C.words a.1 a.2).1 := by
    rw [hgram]
    exact mem_windows _ L pos hbound
  have hneg := negative_value (C.bubble a.1 a.2) hL g hmem
  have hG : G a.1 g= -1 := by
    rw [C.sum_eq a.1,sum_piece_eq (C.words a.1) (C.bubble a.1) (C.disjoint a.1) hL a.2 g
      (by rw [hneg];decide)]
    exact hneg
  rcases hg.2.2 a.1 g hG with hbase | ⟨j,hj,hjg⟩
  · left
    obtain ⟨z,hz,hzg⟩ := occurrence_of_mem (letters x) g ((nonzero_iff_mem _ _ _).mp hbase)
    refine ⟨z,?_,?_⟩
    · simpa [letters] using hz
    · rw [E.path_eq a false]
      exact agree_of_gram (letters x) (C.words a.1 a.2).1 z pos hz hbound g hzg hgram
  · right
    rw [C.sum_eq j] at hjg
    obtain ⟨i,hi⟩ := (sum_support (C.words j) (C.bubble j) (C.disjoint j) hL g).mp hjg
    rcases (difference_support (C.bubble j i) hL g).mp hi with hp | hq
    · obtain ⟨z,hz,hzg⟩ := occurrence_of_mem (C.words j i).1 g hp
      refine ⟨(j,i),false,z,?_,?_,?_⟩
      · change E.family.rank (j,i) < E.family.rank a
        rw [E.rank_eq,E.rank_eq]
        exact hj
      · have hh := E.length_eq (j,i) false
        have hl := E.family.path_length_eq (j,i) false
        change pathLength (E.family.header (j,i)) false=(C.words j i).1.length at hh
        omega
      · rw [E.path_eq a false,E.path_eq (j,i) false]
        exact agree_of_gram _ _ pos z hbound hz g hgram hzg
    · obtain ⟨z,hz,hzg⟩ := occurrence_of_mem (C.words j i).2 g hq
      refine ⟨(j,i),true,z,?_,?_,?_⟩
      · change E.family.rank (j,i) < E.family.rank a
        rw [E.rank_eq,E.rank_eq]
        exact hj
      · have hh := E.length_eq (j,i) true
        have hl := E.family.path_length_eq (j,i) true
        change pathLength (E.family.header (j,i)) true=(C.words j i).2.length at hh
        omega
      · rw [E.path_eq a false,E.path_eq (j,i) true]
        exact agree_of_gram _ _ pos z hbound hz g hgram hzg

end DeletionGeneralization.CatalogueRecovery

-- Source module: ComponentInsert
namespace DeletionGeneralization.ComponentInsert
open DeletionHash.MixedEdit BubbleSupport BubbleConnectivity CatalogueSupport
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem support_mono {L : ℕ} {F H : Finset (Spectrum α L)} (h : F ⊆ H) :
    supportUnion F ⊆ supportUnion H := by
  rintro g ⟨w,hw,hg⟩
  exact ⟨w,h hw,hg⟩

theorem incident_mono {L : ℕ} {F H : Finset (Spectrum α L)} (h : F ⊆ H) :
    incidentVertices F ⊆ incidentVertices H := by
  rintro v ⟨g,hg,hv⟩
  exact ⟨g,support_mono h hg,hv⟩

def inclusion {L : ℕ} {F H : Finset (Spectrum α L)} (h : F ⊆ H) :
    supportGraph F →g supportGraph H where
  toFun v := ⟨v.val,incident_mono h v.property⟩
  map_rel' := by
    rintro v z ⟨hne,g,hg,he⟩
    refine ⟨?_,g,support_mono h hg,he⟩
    intro hvz
    exact hne (Subtype.ext (congrArg (fun x : {v : Gram α (L-1) // v ∈ incidentVertices H} => x.val) hvz))

theorem insert_bound {k L t b : ℕ} (hL : 1 ≤ L) (ht : 1 ≤ t)
    (F : Finset (Spectrum α L)) (w : Spectrum α L) (hw : w ∈ Catalogue k L t b)
    (hadj : ∃ z ∈ F, RuleAdjacent w z) :
    componentCount (insert w F) ≤ componentCount F+(2*t-1) := by
  classical
  let H := insert w F
  have hsub : F ⊆ H := Finset.subset_insert _ _
  let φ := inclusion hsub
  obtain ⟨B,hB,hdis,heq⟩ := hw
  have hs : ∀ i g, (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0 → g ∈ supportUnion H := by
    intro i g hg
    refine ⟨w,Finset.mem_insert_self _ _,?_⟩
    rw [heq]
    exact (sum_support B hB hdis hL g).mpr ⟨i,hg⟩
  choose r hr hreach using fun i => bubble_connected H (B i).1 (B i).2 (hB i) hL (hs i)
  let f : (supportGraph F).ConnectedComponent ⊕ Fin (2*t) → (supportGraph H).ConnectedComponent :=
    Sum.elim (fun C => C.map φ) (fun i => (supportGraph H).connectedComponentMk (r i))
  have hsurj : Function.Surjective f := by
    intro C
    refine SimpleGraph.ConnectedComponent.ind ?_ C
    intro v
    obtain ⟨g,⟨z,hz,hg⟩,hv⟩ := v.property
    rcases Finset.mem_insert.mp hz with hzw | hz
    · subst z
      rw [heq] at hg
      obtain ⟨i,hi⟩ := (sum_support B hB hdis hL g).mp hg
      have he := difference_endpoint (hB i) hL g hi
      have hvmem : v.val ∈ bubbleVertices L (B i).1 (B i).2 := by
        rcases hv with hv | hv
        · rw [hv]; exact he.1
        · rw [hv]; exact he.2
      exact ⟨Sum.inr i,SimpleGraph.ConnectedComponent.sound (hreach i v hvmem)⟩
    · let vF : {v : Gram α (L-1) // v ∈ incidentVertices F} := ⟨v.val,⟨g,⟨z,hz,hg⟩,hv⟩⟩
      refine ⟨Sum.inl ((supportGraph F).connectedComponentMk vF),?_⟩
      rfl
  have hnot : ¬Function.Injective f := by
    obtain ⟨z,hz,v,hvw,hvz⟩ := hadj
    have hvF : v ∈ incidentVertices F :=
      incident_mono (Finset.singleton_subset_iff.mpr hz) hvz
    let vF : {v : Gram α (L-1) // v ∈ incidentVertices F} := ⟨v,hvF⟩
    obtain ⟨g,⟨z',hz',hg⟩,hv⟩ := hvw
    have hz' : z'=w := Finset.mem_singleton.mp hz'
    subst z'
    rw [heq] at hg
    obtain ⟨i,hi⟩ := (sum_support B hB hdis hL g).mp hg
    have he := difference_endpoint (hB i) hL g hi
    have hvmem : (φ vF).val ∈ bubbleVertices L (B i).1 (B i).2 := by
      change v ∈ bubbleVertices L (B i).1 (B i).2
      rcases hv with hv | hv
      · rw [hv]; exact he.1
      · rw [hv]; exact he.2
    have heqC : f (Sum.inr i)=f (Sum.inl ((supportGraph F).connectedComponentMk vF)) :=
      SimpleGraph.ConnectedComponent.sound (hreach i (φ vF) hvmem)
    intro hinj
    have h := hinj heqC
    cases h
  letI : Fintype (supportGraph F).ConnectedComponent := Fintype.ofFinite _
  letI : Fintype (supportGraph H).ConnectedComponent := Fintype.ofFinite _
  have hc := Fintype.card_lt_of_surjective_not_injective f hsurj hnot
  simp only [Fintype.card_sum,Fintype.card_fin] at hc
  have heF : Fintype.card (supportGraph F).ConnectedComponent=componentCount F := by
    simp [componentCount,Nat.card_eq_fintype_card]
  have heH : Fintype.card (supportGraph H).ConnectedComponent=componentCount (insert w F) := by
    simp [H,componentCount,Nat.card_eq_fintype_card]
  rw [heF,heH] at hc
  omega

end DeletionGeneralization.ComponentInsert

-- Source module: ConnectedBlocks
namespace DeletionGeneralization.ConnectedBlocks
open DeletionHash.MixedEdit ComponentInsert ComponentCover
universe u v
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem reachable_mem {V : Type v} (G : SimpleGraph V) (S : Set V)
    (hclosed : ∀ v ∈ S, ∀ w, G.Adj v w → w ∈ S)
    {v w : V} (hv : v ∈ S) (h : G.Reachable v w) : w ∈ S := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hv
  | cons he p ih => exact ih (hclosed _ hv _ he)

theorem connected_bound {k L t b : ℕ} (hL : 1 ≤ L) (ht : 1 ≤ t)
    (B : Finset (Spectrum α L)) (hB : ∀ z ∈ B, z ∈ Catalogue k L t b)
    (hconn : ConnectedRules B) :
    componentCount B ≤ (2*t-1)*B.card+1 := by
  classical
  let S := B.powerset.filter (fun F => F.Nonempty ∧ componentCount F ≤ (2*t-1)*F.card+1)
  obtain ⟨z,hz⟩ := hconn.1
  have hseed : {z} ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hz),Finset.singleton_nonempty z,?_⟩
    have hc := catalogue_count_le z (hB z hz) hL
    simp only [Finset.card_singleton,mul_one]
    omega
  obtain ⟨F,hF,hmax⟩ := Finset.exists_max_image S Finset.card ⟨{z},hseed⟩
  have hfdata := Finset.mem_filter.mp hF
  have hsub : F ⊆ B := Finset.mem_powerset.mp hfdata.1
  have hne := hfdata.2.1
  have hbound := hfdata.2.2
  have hclosed : ∀ v : {w : Spectrum α L // w ∈ B}, v.val ∈ F →
      ∀ w : {w : Spectrum α L // w ∈ B}, (ruleGraph B).Adj v w → w.val ∈ F := by
    intro v hv w hadj
    by_contra hw
    have hnewbound : componentCount (insert w.val F) ≤ (2*t-1)*(insert w.val F).card+1 := by
      have ha : ∃ z ∈ F, RuleAdjacent w.val z := by
        refine ⟨v.val,hv,?_⟩
        obtain ⟨p,hp,hq⟩ := hadj.2
        exact ⟨p,hq,hp⟩
      have hc := insert_bound hL ht F w.val (hB w.val w.property) ha
      rw [Finset.card_insert_of_notMem hw,Nat.mul_add,Nat.mul_one]
      omega
    have hnew : insert w.val F ∈ S := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr ?_,Finset.insert_nonempty _ _,hnewbound⟩
      exact Finset.insert_subset w.property hsub
    have hm := hmax _ hnew
    rw [Finset.card_insert_of_notMem hw] at hm
    omega
  obtain ⟨v,hv⟩ := hne
  have hBF : B ⊆ F := by
    intro w hw
    exact reachable_mem (ruleGraph B) {z | z.val ∈ F} hclosed hv
      (hconn.2 ⟨v,hsub hv⟩ ⟨w,hw⟩)
  have heq : F=B := Finset.Subset.antisymm hsub hBF
  rwa [heq] at hbound

theorem blocks (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L) :
    (∀ F : Finset (Spectrum α L), (∀ z ∈ F, z ∈ Catalogue k L t b) →
      ∀ w : Spectrum α L, w ∈ Catalogue k L t b → w ∉ F →
        (∃ z ∈ F, RuleAdjacent w z) →
        componentCount (insert w F) ≤ componentCount F+(2*t-1)) ∧
    (∀ B : Finset (Spectrum α L), (∀ z ∈ B, z ∈ Catalogue k L t b) →
      ConnectedRules B → componentCount B ≤ (2*t-1)*B.card+1) := by
  have ht : 1 ≤ t := by have h := hreg.2.1; omega
  have hL : 1 ≤ L := by have h := hreg.2.2.2.2.1; omega
  exact ⟨fun F _ w hw _ ha => insert_bound hL ht F w hw ha,
    fun B hB hconn => connected_bound hL ht B hB hconn⟩

end DeletionGeneralization.ConnectedBlocks

-- Source module: RecoveryComponents
namespace DeletionGeneralization.RecoveryComponents
open DeletionHash.MixedEdit CatalogueRecovery RecoveryOccurrences RecoveryFamily RecoveryList
open BubbleSupport CatalogueSupport BubbleConnectivity ComponentCover
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Inhabited α]
variable {k L t b R : ℕ} {G : Fin R → Spectrum α L}

theorem support_iff (C : Pieces (k:=k) (t:=t) (b:=b) G) (hL : 1 ≤ L) (g : Gram α L) :
    g ∈ supportUnion (ruleSet G) ↔
      ∃ a : Fin R × Fin (2*t), (spectrum L (C.words a.1 a.2).2-spectrum L (C.words a.1 a.2).1) g≠0 := by
  classical
  letI : DecidableEq (Spectrum α L) := fun a b => Classical.propDecidable (a=b)
  constructor
  · rintro ⟨w,hw,hwg⟩
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
    rw [C.sum_eq j] at hwg
    obtain ⟨i,hi⟩ := (sum_support (C.words j) (C.bubble j) (C.disjoint j) hL g).mp hwg
    exact ⟨(j,i),hi⟩
  · rintro ⟨⟨j,i⟩,hi⟩
    refine ⟨G j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,?_⟩
    rw [C.sum_eq j]
    exact (sum_support (C.words j) (C.bubble j) (C.disjoint j) hL g).mpr ⟨i,hi⟩

theorem overlap_adjacent (C : Pieces (k:=k) (t:=t) (b:=b) G)
    (E : Representation C) (hL : 1 ≤ L)
    (a c : Fin R × Fin (2*t)) (v : Gram α (L-1))
    (ha : v ∈ bubbleVertices L (C.words a.1 a.2).1 (C.words a.1 a.2).2)
    (hc : v ∈ bubbleVertices L (C.words c.1 c.2).1 (C.words c.1 c.2).2) :
    E.family.family.Adjacent L a c := by
  have occurs (d : Fin R × Fin (2*t))
      (hd : v ∈ bubbleVertices L (C.words d.1 d.2).1 (C.words d.1 d.2).2) :
      ∃ side i, i+(L-1) ≤ (pairWord C d side).length ∧
        List.ofFn v=window (L-1) (pairWord C d side) i := by
    rcases hd with hd | hd
    · obtain ⟨i,hi,he⟩ := occurrence_of_mem (C.words d.1 d.2).1 v hd
      exact ⟨false,i,hi,he⟩
    · obtain ⟨i,hi,he⟩ := occurrence_of_mem (C.words d.1 d.2).2 v hd
      exact ⟨true,i,hi,he⟩
  obtain ⟨sa,i,hi,hei⟩ := occurs a ha
  obtain ⟨sc,j,hj,hej⟩ := occurs c hc
  have hal := E.length_eq a sa
  have hcl := E.length_eq c sc
  have hea := E.family.path_length_eq a sa
  have hec := E.family.path_length_eq c sc
  refine ⟨sa,sc,i,j,by omega,by omega,by omega,by omega,?_⟩
  rw [E.path_eq a sa,E.path_eq c sc]
  exact agree_of_gram _ _ i j hi hj v hei hej

theorem components_le (C : Pieces (k:=k) (t:=t) (b:=b) G)
    (E : Representation C) (hL : 1 ≤ L) :
    Fintype.card (Components E.family) ≤ componentCount (ruleSet G) := by
  classical
  let F := ruleSet G
  let B : (Fin R × Fin (2*t)) → List α × List α := fun a => C.words a.1 a.2
  have hb : ∀ a, Bubble k L b (B a).1 (B a).2 := fun a => C.bubble a.1 a.2
  have hsupp : ∀ a g, (spectrum L (B a).2-spectrum L (B a).1) g≠0 → g ∈ supportUnion F :=
    fun a g h => (support_iff C hL g).mpr ⟨a,h⟩
  have hcover : ∀ g ∈ supportUnion F, ∃ a, (spectrum L (B a).2-spectrum L (B a).1) g≠0 :=
    fun g h => (support_iff C hL g).mp h
  obtain ⟨r,hr,_,_⟩ := cover_by_bubbles F B hb hL hsupp hcover
  have connected_of_reachable (a c : Fin R × Fin (2*t))
      (h : (supportGraph F).Reachable (r a) (r c)) :
      E.family.family.Connected L a c := by
    let S : Set {v : Gram α (L-1) // v ∈ incidentVertices F} :=
      {v | ∃ d, E.family.family.Connected L a d ∧ v.val ∈ bubbleVertices L (B d).1 (B d).2}
    have hclosed : ∀ v ∈ S, ∀ w, (supportGraph F).Adj v w → w ∈ S := by
      rintro v ⟨d,had,hvd⟩ w ⟨hne,g,hg,hends⟩
      obtain ⟨e,he⟩ := hcover g hg
      have heps := difference_endpoint (hb e) hL g he
      have hve : v.val ∈ bubbleVertices L (B e).1 (B e).2 := by
        rcases hends with hends | hends
        · rw [hends.1];exact heps.1
        · rw [hends.2];exact heps.2
      have hwe : w.val ∈ bubbleVertices L (B e).1 (B e).2 := by
        rcases hends with hends | hends
        · rw [hends.2];exact heps.2
        · rw [hends.1];exact heps.1
      have hde := overlap_adjacent C E hL d e v.val hvd hve
      exact ⟨e,Relation.EqvGen.trans a d e had (Relation.EqvGen.rel d e hde),hwe⟩
    have haS : r a ∈ S := ⟨a,Relation.EqvGen.refl a,hr a⟩
    obtain ⟨d,had,hdc⟩ := ConnectedBlocks.reachable_mem (supportGraph F) S hclosed haS h
    have hdc' := overlap_adjacent C E hL d c (r c).val hdc (hr c)
    exact Relation.EqvGen.trans a d c had (Relation.EqvGen.rel d c hdc')
  let f : Components E.family → (supportGraph F).ConnectedComponent :=
    fun c => (supportGraph F).connectedComponentMk (r c.out)
  have hf : Function.Injective f := by
    intro c d heq
    have hh : (supportGraph F).Reachable (r c.out) (r d.out) :=
      SimpleGraph.ConnectedComponent.exact heq
    have hcd := connected_of_reachable c.out d.out hh
    have hq : Quotient.mk (componentSetoid E.family.family L) c.out=
        Quotient.mk (componentSetoid E.family.family L) d.out := Quotient.sound hcd
    simpa only [Quotient.out_eq] using hq
  rw [←Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_injective f hf

end DeletionGeneralization.RecoveryComponents

-- Source module: RecoveryCodec
namespace DeletionGeneralization.RecoveryCodec
open RecoveryDecoder
universe u
variable {B : Type*} {α : Type u} {b L : ℕ}

def strip : Instruction B α b → Instruction B Unit b
  | .start a sa i c sc j _ => .start a sa i c sc j (fun _ => ())
  | .fillBase a w r => .fillBase a w r
  | .fillSupplier a s i c w => .fillSupplier a s i c w

def extension : Instruction B α b → Option (Fin b → α)
  | .start _ _ _ _ _ _ extra => some extra
  | _ => none

def restore : List (Instruction B Unit b) → List (Fin b → α) → Option (List (Instruction B α b))
  | [], [] => some []
  | [], _::_ => none
  | .start a sa i c sc j _::rest, extra::extras =>
      (restore rest extras).map (Instruction.start a sa i c sc j extra :: ·)
  | .start ..::_, [] => none
  | .fillBase a w r::rest, extras =>
      (restore rest extras).map (Instruction.fillBase a w r :: ·)
  | .fillSupplier a s i c w::rest, extras =>
      (restore rest extras).map (Instruction.fillSupplier a s i c w :: ·)

theorem restore_strip (ins : List (Instruction B α b)) :
    restore (ins.map strip) (ins.filterMap extension)=some ins := by
  induction ins with
  | nil => rfl
  | cons i rest ih => cases i <;> simp [List.filterMap_cons,strip,extension,restore,ih]

theorem extension_count (ins : List (Instruction B α b)) :
    (ins.filterMap extension).length=starts ins := by
  induction ins with
  | nil => rfl
  | cons i rest ih => cases i <;> simp [List.filterMap_cons,extension,starts,isStart,Nat.add_comm] <;> exact ih

abbrev Shape (B : Type*) (L : ℕ) :=
  Fin 3 × Option B × Option B × Bool × Bool × Fin (3*L+1) × Fin (3*L+1) × Fin 3

def encode (i : Instruction B Unit b) (hi : Bounded L i) : Shape B L :=
  match i with
  | .start a sa o c sc d _ =>
      (0,some a,some c,sa,sc,⟨o,by exact Nat.lt_succ_of_lt hi.1⟩,
        ⟨d,by exact Nat.lt_succ_of_lt hi.2⟩,0)
  | .fillBase a w r =>
      (1,none,some a,false,false,⟨r,by exact Nat.lt_succ_of_lt hi⟩,0,w)
  | .fillSupplier a s o c w =>
      (2,some a,some c,s,false,⟨o,by exact Nat.lt_succ_of_lt hi⟩,0,w)

def decode (s : Shape B L) : Option (Instruction B Unit b) :=
  let (tag,a,c,sa,sc,o,d,w) := s
  if tag.val=0 then a.bind fun a => c.map fun c => .start a sa o.val c sc d.val (fun _ => ())
  else if tag.val=1 then c.map fun c => .fillBase c w o.val
  else a.bind fun a => c.map fun c => .fillSupplier a sa o.val c w

theorem decode_encode (i : Instruction B Unit b) (hi : Bounded L i) :
    decode (encode i hi)=some i := by
  cases i with
  | start a sa o c sc d extra =>
    have he : extra=(fun _ => ()) := Subsingleton.elim _ _
    subst extra
    rfl
  | fillBase a w r => rfl
  | fillSupplier a s o c w => rfl

instance (i : Instruction B α b) : Decidable (Bounded L i) := by
  cases i <;> unfold Bounded <;> infer_instance

def encodeTotal (i : Instruction B Unit b) : Option (Shape B L) :=
  if hi : Bounded L i then some (encode i hi) else none

def decodeRow (row : Option (Shape B L)) : Option (Option (Instruction B Unit b)) :=
  match row with
  | none => some none
  | some s => (decode s).map some

theorem decode_total (i : Instruction B Unit b) (hi : Bounded L i) :
    decodeRow (encodeTotal (L:=L) i)=some (some i) := by
  simp [encodeTotal,hi,decodeRow,decode_encode]

theorem strip_bounded (i : Instruction B α b) (hi : Bounded L i) :
    Bounded L (strip i) := by
  cases i <;> exact hi

end DeletionGeneralization.RecoveryCodec

-- Source module: RecordPacking

/-! Fixed-width padding of instruction lists, with a proved decoding round trip. -/
namespace DeletionGeneralization.RecordPacking

variable {α β : Type*}

def pack (padding : β) (xs : List β) (size : ℕ) : Fin size → β :=
  fun i => xs[i.val]?.getD padding

def unpack (decode : β → Option (Option α)) :
    (size : ℕ) → (Fin size → β) → Option (List α)
  | 0, _ => some []
  | size + 1, rows =>
    (decode (rows ⟨0, by omega⟩)).bind fun entry =>
      (unpack decode size (fun i => rows i.succ)).map fun rest => entry.toList ++ rest

theorem unpack_of_positions (decode : β → Option (Option α)) (size : ℕ)
    (rows : Fin size → β) (xs : List α) (hsize : xs.length ≤ size)
    (hrows : ∀ i, decode (rows i) = some xs[i.val]?) :
    unpack decode size rows = some xs := by
  induction size generalizing xs with
  | zero =>
    have hx : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs
    rfl
  | succ size ih =>
    cases xs with
    | nil =>
      have hfirst := hrows ⟨0, by omega⟩
      change decode (rows 0) = some none at hfirst
      have hrest : ∀ i : Fin size, decode (rows i.succ) = some ([] : List α)[i.val]? := by
        intro i
        simpa using hrows i.succ
      have hr := ih (fun i => rows i.succ) [] (by simp) hrest
      simp [unpack, hfirst, hr]
    | cons a xs =>
      have hfirst := hrows ⟨0, by omega⟩
      change decode (rows 0) = some (some a) at hfirst
      have hrest : ∀ i : Fin size, decode (rows i.succ) = some xs[i.val]? := by
        intro i
        simpa using hrows i.succ
      have hr := ih (fun i => rows i.succ) xs (by simp at hsize; omega) hrest
      simp [unpack, hfirst, hr]

theorem unpack_pack (decode : β → Option (Option α)) (encode : α → β)
    (padding : β) (hpadding : decode padding = some none)
    (xs : List α) (hencode : ∀ a ∈ xs, decode (encode a) = some (some a))
    (size : ℕ) (hsize : xs.length ≤ size) :
    unpack decode size (pack padding (xs.map encode) size) = some xs := by
  apply unpack_of_positions decode size _ xs hsize
  intro i
  unfold pack
  cases hget : xs[i.val]? with
  | none => simpa [List.getElem?_map, hget] using hpadding
  | some a =>
    have ha : a ∈ xs := List.mem_of_getElem? hget
    simpa [List.getElem?_map, hget] using hencode a ha


end DeletionGeneralization.RecordPacking

-- Source module: RecoveryDescription
namespace DeletionGeneralization.RecoveryDescription
open RecoveryMemory RecoveryHeader RecoveryDecoder RecordPacking
universe u
variable {α : Type u} [DecidableEq α] [Inhabited α]
variable {B : Type*} [Fintype B] [DecidableEq B] {n k L b c : ℕ}

abbrev Code (B : Type*) [Fintype B] (α : Type u) (n L b c : ℕ) :=
  (Fin c → Option (B × Fin n)) ×
  (Fin (4*Fintype.card B) → Option (RecoveryCodec.Shape B L)) ×
  (Fin (Fintype.card B) → Option (Fin b → α))

def encodeRoot (r : B × ℕ) : Option (B × Fin n) :=
  if h : r.2 < n then some (r.1,⟨r.2,h⟩) else none

def decodeRoot (row : Option (B × Fin n)) : Option (Option (B × ℕ)) :=
  some (row.map (fun r => (r.1,r.2.val)))

theorem root_roundtrip (r : B × ℕ) (hr : r.2 < n) :
    decodeRoot (encodeRoot (n:=n) r)=some (some r) := by
  simp [encodeRoot,decodeRoot,hr]

def decode (x : ℕ → α) (n k : ℕ) (hbk : b ≤ k) (header : B → Header α L b)
    (code : Code B α n L b c) : Option ((a : B) → Fin (negativeLength (header a)) → α) :=
  (unpack decodeRoot c code.1).bind fun roots =>
    (unpack RecoveryCodec.decodeRow (4*Fintype.card B) code.2.1).bind fun shapes =>
      (unpack some (Fintype.card B) code.2.2).bind fun extras =>
        (RecoveryCodec.restore shapes extras).bind fun ins =>
          RecoveryRun.decode x n k hbk header roots ins

theorem pack_record (x : ℕ → α) (n k : ℕ) (hbk : b ≤ k) (header : B → Header α L b)
    (roots : List (B × ℕ)) (ins : List (Instruction B α b))
    (hc : roots.length ≤ c) (hr : ∀ r ∈ roots, r.2 < n)
    (hlen : ins.length ≤ 4*Fintype.card B) (hext : starts ins ≤ Fintype.card B)
    (hbounds : ∀ i ∈ ins, Bounded L i) :
    ∃ code : Code B α n L b c,
      decode x n k hbk header code=RecoveryRun.decode x n k hbk header roots ins := by
  let rootRows := pack none (roots.map (encodeRoot (n:=n))) c
  let shapes := ins.map RecoveryCodec.strip
  let shapeRows := pack none (shapes.map (RecoveryCodec.encodeTotal (L:=L))) (4*Fintype.card B)
  let extras := ins.filterMap RecoveryCodec.extension
  let extraRows := pack none (extras.map some) (Fintype.card B)
  have hroot : unpack decodeRoot c rootRows=some roots :=
    unpack_pack decodeRoot (encodeRoot (n:=n)) none rfl roots
      (fun r hm => root_roundtrip r (hr r hm)) c hc
  have hshape : unpack RecoveryCodec.decodeRow (4*Fintype.card B) shapeRows=some shapes := by
    apply unpack_pack RecoveryCodec.decodeRow (RecoveryCodec.encodeTotal (L:=L)) none rfl shapes
    · intro s hs
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hs
      exact RecoveryCodec.decode_total _ (RecoveryCodec.strip_bounded i (hbounds i hi))
    · simpa [shapes] using hlen
  have hextras : unpack some (Fintype.card B) extraRows=some extras := by
    apply unpack_pack some some none rfl extras (fun _ _ => rfl) (Fintype.card B)
    simpa [extras,RecoveryCodec.extension_count] using hext
  refine ⟨(rootRows,shapeRows,extraRows),?_⟩
  simp only [decode,hroot,hshape,hextras,Option.bind_some]
  rw [RecoveryCodec.restore_strip]
  rfl

end DeletionGeneralization.RecoveryDescription

-- Source module: GeneratingEncoding
namespace DeletionGeneralization.GeneratingEncoding
open DeletionHash.MixedEdit RecoveryHeader RecoveryList RecoveryOccurrences RecoveryFamily CatalogueRecovery
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Inhabited α]
variable {n k L t b R c : ℕ}

abbrev Index (t R : ℕ) := Fin R × Fin (2*t)
abbrev Description (α : Type u) (n L t b R c : ℕ) :=
  (Index t R → Header α L b) × RecoveryDescription.Code (Index t R) α n L b c

noncomputable def rules (header : Index t R → Header α L b)
    (negative : (a : Index t R) → Fin (negativeLength (header a)) → α) :
    Finset (Spectrum α L) :=
  ruleSet (fun j => ∑ i : Fin (2*t),
    (spectrum L (List.ofFn (fun z : Fin (positiveLength (header (j,i))) =>
      positive (header (j,i)) (pad (negative (j,i))) z.val)) -
     spectrum L (List.ofFn (negative (j,i)))))

noncomputable def decode (x : Word α n) (k : ℕ) (hbk : b ≤ k)
    (desc : Description α n L t b R c) : Option (Finset (Spectrum α L)) :=
  (RecoveryDescription.decode (total (letters x)) n k hbk desc.1 desc.2).map (rules desc.1)

theorem ofFn_total (P : List α) (len : ℕ) (hlen : len=P.length) :
    List.ofFn (fun i : Fin len => total P i.val)=P := by
  subst len
  have h := window_total P 0 P.length (by omega)
  simpa only [window,List.drop_zero,List.take_length,Nat.zero_add] using h.symm

theorem reconstruct {G : Fin R → Spectrum α L}
    (C : Pieces (k:=k) (t:=t) (b:=b) G) (E : Representation C) :
    rules E.family.header (fun a i => E.family.negative a i.val)=ruleSet G := by
  have hn (a : Index t R) :
      List.ofFn (fun i : Fin (negativeLength (E.family.header a)) => E.family.negative a i.val)=
        (C.words a.1 a.2).1 := by
    have he := E.path_eq a false
    change E.family.negative a=total (C.words a.1 a.2).1 at he
    rw [he]
    exact ofFn_total _ _ (E.length_eq a false)
  have hp (a : Index t R) :
      List.ofFn (fun i : Fin (positiveLength (E.family.header a)) =>
        positive (E.family.header a) (pad (fun j : Fin (negativeLength (E.family.header a)) => E.family.negative a j.val)) i.val)=
      (C.words a.1 a.2).2 := by
    have he := E.path_eq a true
    change positive (E.family.header a) (E.family.negative a)=total (C.words a.1 a.2).2 at he
    have hf : (fun i : Fin (positiveLength (E.family.header a)) =>
        positive (E.family.header a) (pad (fun j : Fin (negativeLength (E.family.header a)) =>
          E.family.negative a j.val)) i.val)=
        (fun i : Fin (positiveLength (E.family.header a)) => total (C.words a.1 a.2).2 i.val) := by
      funext i
      rw [←he]
      apply positive_congr (E.family.header a) _ _ _ i.val i.isLt
      intro z hz
      simp [pad,hz]
    rw [hf]
    exact ofFn_total _ _ (E.length_eq a true)
  unfold rules
  congr 1
  funext j
  rw [C.sum_eq j]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hp (j,i),hn (j,i)]

theorem exists_description (x : Word α n) (hx : IsUnique k (letters x))
    (hL : L=3*(k+b+1)) (hb : b < k) (G : Fin R → Spectrum α L)
    (hg : GeneratingSequence k t b (spectrum L (letters x)) G)
    (hc : componentCount (ruleSet G) ≤ c) :
    ∃ desc : Description α n L t b R c, decode x k (by omega) desc=some (ruleSet G) := by
  classical
  obtain ⟨C⟩ := pieces_exist G hg.1
  obtain ⟨E⟩ := representation C hL hb
  have hgen := generates C E x hg (by omega)
  have hunique : RecoveryWords.KUnique (total (letters x)) n k := by
    simpa only [letters,List.length_ofFn] using total_unique (letters x) hx
  obtain ⟨roots,ins,hroots,hpositions,hlen,hstarts,hbounds,hrun⟩ :=
    RecoveryFamily.exists_record E.family (total (letters x)) n hunique hgen
  have hrootle : roots.length ≤ c := by
    rw [hroots]
    exact (RecoveryComponents.components_le C E (by omega)).trans hc
  obtain ⟨code,hcode⟩ := RecoveryDescription.pack_record (total (letters x)) n k E.family.bk
    E.family.header roots ins hrootle hpositions hlen hstarts hbounds
  refine ⟨(E.family.header,code),?_⟩
  unfold decode
  dsimp only
  rw [hcode,hrun]
  simp only [Option.map_some]
  congr 1
  exact reconstruct C E

end DeletionGeneralization.GeneratingEncoding

-- Source module: DescriptionCount
namespace DeletionGeneralization.DescriptionCount
open DeletionHash.MixedEdit GeneratingEncoding RecoveryHeader RecoveryDescription RecoveryCodec
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Inhabited α]

theorem header_card (L b : ℕ) :
    Fintype.card (Header α L b)=L^2*(b+1)^2*(Fintype.card α)^(2*b) := by
  let e : Header α L b ≃
      (Fin L × Fin L × Fin (b+1) × Fin (b+1) × (Fin b → α) × (Fin b → α)) :=
    { toFun := fun h => (h.left,h.right,h.removed,h.inserted,h.old,h.new)
      invFun := fun x => ⟨x.1,x.2.1,x.2.2.1,x.2.2.2.1,x.2.2.2.2.1,x.2.2.2.2.2⟩
      left_inv := by intro h;cases h;rfl
      right_inv := by rintro ⟨a,c,d,e,f,g⟩;rfl }
  rw [Fintype.card_congr e]
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_fun]
  rw [show 2*b=b+b by omega,pow_add]
  ring

theorem shape_card (B : Type*) [Fintype B] (L : ℕ) :
    Fintype.card (Shape B L)=36*(Fintype.card B+1)^2*(3*L+1)^2 := by
  simp only [Shape,Fintype.card_prod,Fintype.card_fin,Fintype.card_option,Fintype.card_bool]
  ring

theorem description_card (n L t b R c : ℕ) :
    Fintype.card (Description α n L t b R c)=
      (L^2*(b+1)^2*(Fintype.card α)^(2*b))^(2*t*R) *
      (((2*t*R)*n+1)^c *
        ((36*(2*t*R+1)^2*(3*L+1)^2+1)^(4*(2*t*R)) *
          ((Fintype.card α)^b+1)^(2*t*R))) := by
  simp only [Description,Code,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,
    Fintype.card_option,Fintype.card_bool,header_card,shape_card,Index]
  congr 1 <;> congr 1 <;> ring

theorem count_le_description {n k L t b R c : ℕ}
    (x : Word α n) (hx : IsUnique k (letters x)) (hL : L=3*(k+b+1)) (hb : b < k) :
    generatingCount k t b (spectrum L (letters x)) R c ≤
      (Fintype.card (Description α n L t b R c) : ℕ∞) := by
  classical
  let S : Set (Finset (Spectrum α L)) :=
    {F | GeneratingSet k t b (spectrum L (letters x)) F ∧ F.card=R ∧ componentCount F=c}
  have hex' (F : Finset (Spectrum α L))
      (hf : GeneratingSet k t b (spectrum L (letters x)) F ∧ F.card=R ∧ componentCount F=c) :
      ∃ d : Description α n L t b R c, GeneratingEncoding.decode x k (by omega) d=some F := by
    obtain ⟨⟨G,hG,hset⟩,hcard,hcomp⟩ := hf
    subst R
    have hc : componentCount (ruleSet G) ≤ c := by rw [hset];exact hcomp.le
    obtain ⟨d,hd⟩ := GeneratingEncoding.exists_description x hx hL hb G hG hc
    exact ⟨d,by simpa only [hset] using hd⟩
  have hex (F : S) := hex' F.val F.property
  let enc : S → Description α n L t b R c := fun F => Classical.choose (hex F)
  have henc (F : S) : GeneratingEncoding.decode x k (by omega) (enc F)=some F.val :=
    Classical.choose_spec (hex F)
  have hinj : Function.Injective enc := by
    intro F H heq
    apply Subtype.ext
    apply Option.some.inj
    rw [←henc F,←henc H,heq]
  letI : Finite S := Finite.of_injective enc hinj
  letI : Fintype S := Fintype.ofFinite S
  have hc := Fintype.card_le_of_injective enc hinj
  change S.encard ≤ _
  rw [←Set.coe_fintypeCard S]
  exact_mod_cast hc

end DeletionGeneralization.DescriptionCount

-- Source module: CountArithmetic
namespace DeletionGeneralization.CountArithmetic
open DeletionHash.MixedEdit GeneratingEncoding DescriptionCount
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Inhabited α]

def field (L ν : ℕ) : ℕ := 100*L*(ν+1)
def exponent (t : ℕ) : ℕ := 60*t*(100*(2*t+1)+1)

theorem exponent_pos (t : ℕ) (ht : 1 ≤ t) : 1 ≤ exponent t := by
  unfold exponent
  nlinarith

theorem raw_bound (n L b q ν c : ℕ)
    (hn : 1 ≤ n) (hL : 1 ≤ L) (hb : b+1 ≤ L) (hq : 1 ≤ q)
    (hν : 1 ≤ ν) (hc : c ≤ ν) :
    (L^2*(b+1)^2*q^(2*b))^ν *
      ((ν*n+1)^c*((36*(ν+1)^2*(3*L+1)^2+1)^(4*ν)*(q^b+1)^ν)) ≤
      n^c*q^(3*b*ν)*(field L ν)^(30*ν) := by
  let D := field L ν
  have hd100 : 100*L ≤ D := by
    dsimp [D,field]
    nlinarith [Nat.mul_le_mul_left (100*L) (show 1 ≤ ν+1 by omega)]
  have hdn : ν+1 ≤ D := by
    dsimp [D,field]
    nlinarith [Nat.mul_le_mul_right (ν+1) (show 1 ≤ 100*L by omega)]
  have hdL : L ≤ D := by omega
  have hd3 : 3*L+1 ≤ D := by omega
  have hd36 : 36 ≤ D := by omega
  have hd2 : 2 ≤ D := by omega
  have hhead : L^2*(b+1)^2 ≤ D^4 := by
    calc
      _ ≤ D^2*D^2 := by gcongr <;> omega
      _ = D^4 := by ring
  have hroot : ν*n+1 ≤ n*D := by nlinarith
  have hsh : 36*(ν+1)^2*(3*L+1)^2 ≤ D^5 := by
    calc
      _ ≤ D*D^2*D^2 := by gcongr
      _ = D^5 := by ring
  have hshape : 36*(ν+1)^2*(3*L+1)^2+1 ≤ D^6 := by
    have hp : 1 ≤ D^5 := one_le_pow₀ (by omega)
    calc
      _ ≤ D^5+1 := by omega
      _ ≤ D^5*D := by nlinarith
      _ = D^6 := by ring
  have hqp : 1 ≤ q^b := one_le_pow₀ hq
  have hextra : q^b+1 ≤ D*q^b := by nlinarith
  calc
    _ ≤ (D^4*q^(2*b))^ν * ((n*D)^c*((D^6)^(4*ν)*(D*q^b)^ν)) := by
      gcongr
    _ = n^c*q^(3*b*ν)*D^(29*ν+c) := by
      simp only [mul_pow,←pow_mul]
      rw [show 3*b*ν=2*b*ν+b*ν by ring,
        show 29*ν+c=4*ν+c+6*(4*ν)+ν by ring]
      simp only [pow_add]
      ring
    _ ≤ n^c*q^(3*b*ν)*D^(30*ν) := by
      gcongr <;> omega

theorem self_le_power (base : ℕ) (hbase : 2 ≤ base) : ∀ q, q ≤ base^q := by
  intro q
  induction q with
  | zero => simp
  | succ q ih =>
    have hp : 1 ≤ base^q := one_le_pow₀ (by omega)
    calc
      q+1 ≤ base^q+base^q := by omega
      _ = 2*base^q := by omega
      _ ≤ base*base^q := Nat.mul_le_mul_right _ hbase
      _ = base^(q+1) := by rw [pow_succ,Nat.mul_comm]

theorem field_bound (L t R : ℕ) (hL : 2 ≤ L) (hR : 1 ≤ R) :
    (field L (2*t*R))^(30*(2*t*R)) ≤ (L*R)^(exponent t*R) := by
  let C := 100*(2*t+1)
  have hbase : 2 ≤ L*R := by nlinarith
  have hC : C ≤ (L*R)^C := self_le_power (L*R) hbase C
  have hfield : field L (2*t*R) ≤ C*(L*R) := by
    have hi : 2*t*R+1 ≤ (2*t+1)*R := by nlinarith
    calc
      _ ≤ 100*L*((2*t+1)*R) := Nat.mul_le_mul_left _ hi
      _ = C*(L*R) := by dsimp [C];ring
  have hb : field L (2*t*R) ≤ (L*R)^(C+1) := by
    calc
      _ ≤ C*(L*R) := hfield
      _ ≤ (L*R)^C*(L*R) := Nat.mul_le_mul_right _ hC
      _ = (L*R)^(C+1) := (pow_succ _ _).symm
  calc
    _ ≤ ((L*R)^(C+1))^(30*(2*t*R)) := by gcongr
    _ = (L*R)^(exponent t*R) := by
      rw [←pow_mul]
      congr 1
      dsimp [C,exponent]
      ring

theorem cardinal_bound (q n k L t b R c : ℕ) (hqa : Fintype.card α=q)
    (hreg : Regime q n t b k L) (hR : 1 ≤ R) (hc : c ≤ 2*t*R) :
    Fintype.card (Description α n L t b R c) ≤
      n^c*q^(6*b*t*R)*(L*R)^(exponent t*R) := by
  obtain ⟨hq,ht,hb,hk,hL,hbk,hLn⟩ := hreg
  rw [description_card,hqa]
  have hν : 1 ≤ 2*t*R := by nlinarith
  have hh := raw_bound n L b q (2*t*R) c (by omega) (by omega) (by omega)
    (by omega) hν hc
  have he : 3*b*(2*t*R)=6*b*t*R := by ring
  rw [he] at hh
  exact hh.trans (Nat.mul_le_mul_left _ (field_bound L t R (by omega) hR))

end DeletionGeneralization.CountArithmetic

-- Source module: Counting
namespace DeletionGeneralization.Counting
open DeletionHash.MixedEdit

universe u

/-- Lemma 5.1: counts underlying sets admitting an order, without an R! factor. -/
theorem count (t b : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ b) :
    ∃ a : ℕ, 1 ≤ a ∧ ∀ (q : ℕ) (α : Type u) [Fintype α] [DecidableEq α],
      Fintype.card α = q → ∀ n k L : ℕ, Regime q n t b k L →
      ∀ x : Word α n, IsUnique k (letters x) → ∀ R c : ℕ, 1 ≤ R → c ≤ 2*t*R →
      generatingCount k t b (spectrum L (letters x)) R c ≤
        ((n^c * q^(6*b*t*R) * (L*R)^(a*R) : ℕ) : ℕ∞) := by
  refine ⟨DeletionGeneralization.CountArithmetic.exponent t,
    DeletionGeneralization.CountArithmetic.exponent_pos t (by omega),?_⟩
  intro q α instF instD hqa n k L hreg x hx R c hR hc
  have hpos : 0 < Fintype.card α := by have hq := hreg.1;omega
  letI : Inhabited α := ⟨Classical.choice (Fintype.card_pos_iff.mp hpos)⟩
  have hle := DeletionGeneralization.DescriptionCount.count_le_description (t:=t) (R:=R) (c:=c) x hx hreg.2.2.2.2.1 hreg.2.2.2.2.2.1
  have hcard := DeletionGeneralization.CountArithmetic.cardinal_bound q n k L t b R c hqa hreg hR hc
  exact hle.trans (by exact_mod_cast hcard)



end DeletionGeneralization.Counting

-- Source module: CountingSolution
open DeletionHash.MixedEdit

universe u

/-- Lemma 5.1: counts underlying sets admitting an order, without an R! factor. -/
theorem solution (t b : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ b) :
    ∃ a : ℕ, 1 ≤ a ∧ ∀ (q : ℕ) (α : Type u) [Fintype α] [DecidableEq α],
      Fintype.card α = q → ∀ n k L : ℕ, Regime q n t b k L →
      ∀ x : Word α n, IsUnique k (letters x) → ∀ R c : ℕ, 1 ≤ R → c ≤ 2*t*R →
      generatingCount k t b (spectrum L (letters x)) R c ≤
        ((n^c * q^(6*b*t*R) * (L*R)^(a*R) : ℕ) : ℕ∞) := by exact DeletionGeneralization.Counting.count t b ht hb




#print axioms solution
