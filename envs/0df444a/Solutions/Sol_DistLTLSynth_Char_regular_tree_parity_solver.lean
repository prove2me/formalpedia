-- Prove2me | solution 1 for DistLTLSynth.Char.regular_tree_parity_solver
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T09:15:37.66314+00:00
-- url     : https://prove2.me/submissions/bc289c56-eab7-4c64-9376-325d33821b31

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_Automata
import Definitions.Def_DistLTLSynth_Char_ComponentTree
import Definitions.Def_DistLTLSynth_Char_SynthesisEngine

set_option autoImplicit false

namespace DistLTLSynth.Char.Thm34ParityGameAux
open DistLTLSynth.Char

/-! ### Section 1: Bounded-Range Min-Parity Dichotomy & Shift Lemmas -/

/-- Dual of `ParityCond`: the least priority occurring infinitely often exists and is odd. -/
def OddParityCond (c : ℕ → ℕ) : Prop :=
  ∃ p : ℕ, Odd p ∧ (∃ᶠ n in Filter.atTop, c n = p) ∧ ∀ᶠ n in Filter.atTop, p ≤ c n

lemma not_parityCond_and_oddParityCond (c : ℕ → ℕ) :
    ¬ (ParityCond c ∧ OddParityCond c) := by
  rintro ⟨⟨p, hp_even, hp_freq, hp_ev⟩, ⟨q, hq_odd, hq_freq, hq_ev⟩⟩
  obtain ⟨n1, hn1_eq, hn1_le⟩ := (hq_freq.and_eventually hp_ev).exists
  obtain ⟨n2, hn2_eq, hn2_le⟩ := (hp_freq.and_eventually hq_ev).exists
  have hpq : p = q := by omega
  subst hpq
  rcases hp_even with ⟨k, rfl⟩
  rcases hq_odd with ⟨l, hl⟩
  omega

lemma parityCond_or_oddParityCond_of_bdd (c : ℕ → ℕ) (B : ℕ)
    (hbdd : ∀ n : ℕ, c n ≤ B) :
    ParityCond c ∨ OddParityCond c := by
  classical
  have hex : ∃ p : ℕ, p ≤ B ∧ ∃ᶠ n in Filter.atTop, c n = p := by
    by_contra hall
    have hnone : ∀ p ≤ B, ∃ N : ℕ, ∀ n ≥ N, c n ≠ p := by
      intro p hp
      have hnf : ¬ ∃ᶠ n in Filter.atTop, c n = p := fun hf => hall ⟨p, hp, hf⟩
      rw [Filter.frequently_atTop] at hnf
      by_contra hnoN
      apply hnf
      intro N
      by_contra hno_n
      exact hnoN ⟨N, fun n hn hc => hno_n ⟨n, hn, hc⟩⟩
    let boundOf : ℕ → ℕ := fun p => if hp : p ≤ B then (hnone p hp).choose else 0
    let M := (Finset.range (B + 1)).sup boundOf
    have hcM : c M ≤ B := hbdd M
    have hleM : boundOf (c M) ≤ M :=
      Finset.le_sup (f := boundOf) (Finset.mem_range.mpr (by omega))
    have hspec : ∀ n ≥ boundOf (c M), c n ≠ c M := by
      dsimp only [boundOf]
      rw [dif_pos hcM]
      exact (hnone (c M) hcM).choose_spec
    exact hspec M hleM rfl
  let p := Nat.find hex
  have hp_spec : p ≤ B ∧ ∃ᶠ n in Filter.atTop, c n = p := Nat.find_spec hex
  have hp_min : ∀ q < p, ¬ (q ≤ B ∧ ∃ᶠ n in Filter.atTop, c n = q) :=
    fun q hq => Nat.find_min hex hq
  have hno_lt : ∀ q < p, ∃ N : ℕ, ∀ n ≥ N, c n ≠ q := by
    intro q hq
    have hqB : q ≤ B := le_trans (le_of_lt hq) hp_spec.1
    have hnf : ¬ ∃ᶠ n in Filter.atTop, c n = q := fun hf => hp_min q hq ⟨hqB, hf⟩
    rw [Filter.frequently_atTop] at hnf
    by_contra hnoN
    apply hnf
    intro N
    by_contra hno_n
    exact hnoN ⟨N, fun n hn hc => hno_n ⟨n, hn, hc⟩⟩
  let boundLt : ℕ → ℕ := fun q => if hq : q < p then (hno_lt q hq).choose else 0
  let N0 := (Finset.range p).sup boundLt
  have hev : ∀ᶠ n in Filter.atTop, p ≤ c n := by
    rw [Filter.eventually_atTop]
    refine ⟨N0, fun n hn => ?_⟩
    by_contra hlt
    have hcp : c n < p := by omega
    have hleN : boundLt (c n) ≤ N0 :=
      Finset.le_sup (f := boundLt) (Finset.mem_range.mpr hcp)
    have hspec : ∀ m ≥ boundLt (c n), c m ≠ c n := by
      dsimp only [boundLt]
      rw [dif_pos hcp]
      exact (hno_lt (c n) hcp).choose_spec
    exact hspec n (le_trans hleN hn) rfl
  rcases Nat.even_or_odd p with heven | hodd
  · exact Or.inl ⟨p, heven, hp_spec.2, hev⟩
  · exact Or.inr ⟨p, hodd, hp_spec.2, hev⟩

lemma oddParityCond_iff_not_parityCond_of_bdd (c : ℕ → ℕ) (B : ℕ)
    (hbdd : ∀ n : ℕ, c n ≤ B) :
    OddParityCond c ↔ ¬ ParityCond c := by
  constructor
  · intro ho hp
    exact not_parityCond_and_oddParityCond c ⟨hp, ho⟩
  · intro hnp
    rcases parityCond_or_oddParityCond_of_bdd c B hbdd with hp | ho
    · exact False.elim (hnp hp)
    · exact ho

lemma parityCond_shift (c : ℕ → ℕ) (d : ℕ) :
    ParityCond c ↔ ParityCond (fun n => c (d + n)) := by
  unfold ParityCond
  constructor
  · rintro ⟨p, heven, hfreq, hev⟩
    refine ⟨p, heven, ?_, ?_⟩
    · rw [Filter.frequently_atTop] at hfreq ⊢
      intro N
      obtain ⟨n, hn, hp⟩ := hfreq (d + N)
      refine ⟨n - d, by omega, ?_⟩
      dsimp only
      rwa [show d + (n - d) = n by omega]
    · rw [Filter.eventually_atTop] at hev ⊢
      obtain ⟨N, hN⟩ := hev
      exact ⟨N, fun n hn => hN (d + n) (by omega)⟩
  · rintro ⟨p, heven, hfreq, hev⟩
    refine ⟨p, heven, ?_, ?_⟩
    · rw [Filter.frequently_atTop] at hfreq ⊢
      intro N
      obtain ⟨n, hn, hp⟩ := hfreq N
      exact ⟨d + n, by omega, hp⟩
    · rw [Filter.eventually_atTop] at hev ⊢
      obtain ⟨N, hN⟩ := hev
      refine ⟨d + N, fun n hn => ?_⟩
      have hle := hN (n - d) (by omega)
      dsimp only at hle
      rwa [show d + (n - d) = n by omega] at hle

lemma oddParityCond_shift (c : ℕ → ℕ) (d : ℕ) :
    OddParityCond c ↔ OddParityCond (fun n => c (d + n)) := by
  unfold OddParityCond
  constructor
  · rintro ⟨p, hodd, hfreq, hev⟩
    refine ⟨p, hodd, ?_, ?_⟩
    · rw [Filter.frequently_atTop] at hfreq ⊢
      intro N
      obtain ⟨n, hn, hp⟩ := hfreq (d + N)
      refine ⟨n - d, by omega, ?_⟩
      dsimp only
      rwa [show d + (n - d) = n by omega]
    · rw [Filter.eventually_atTop] at hev ⊢
      obtain ⟨N, hN⟩ := hev
      exact ⟨N, fun n hn => hN (d + n) (by omega)⟩
  · rintro ⟨p, hodd, hfreq, hev⟩
    refine ⟨p, hodd, ?_, ?_⟩
    · rw [Filter.frequently_atTop] at hfreq ⊢
      intro N
      obtain ⟨n, hn, hp⟩ := hfreq N
      exact ⟨d + n, by omega, hp⟩
    · rw [Filter.eventually_atTop] at hev ⊢
      obtain ⟨N, hN⟩ := hev
      refine ⟨d + N, fun n hn => ?_⟩
      have hle := hN (n - d) (by omega)
      dsimp only at hle
      rwa [show d + (n - d) = n by omega] at hle

lemma parityCond_double_step (c f : ℕ → ℕ)
    (hstep : ∀ k : ℕ, c (2 * k + 1) = f k ∧ c (2 * k + 2) = f k) :
    ParityCond c ↔ ParityCond f := by
  have hc_at : ∀ n : ℕ, 1 ≤ n → c n = f ((n - 1) / 2) := by
    intro n hn
    let k := (n - 1) / 2
    have hcases : n = 2 * k + 1 ∨ n = 2 * k + 2 := by omega
    rcases hcases with h1 | h2
    · rw [h1, show (2 * k + 1 - 1) / 2 = k by omega]
      exact (hstep k).1
    · rw [h2, show (2 * k + 2 - 1) / 2 = k by omega]
      exact (hstep k).2
  unfold ParityCond
  constructor
  · rintro ⟨p, heven, hfreq, hev⟩
    refine ⟨p, heven, ?_, ?_⟩
    · rw [Filter.frequently_atTop] at hfreq ⊢
      intro K
      obtain ⟨n, hn, hp⟩ := hfreq (2 * K + 1)
      refine ⟨(n - 1) / 2, by omega, ?_⟩
      rw [← hc_at n (by omega)]
      exact hp
    · rw [Filter.eventually_atTop] at hev ⊢
      obtain ⟨N, hN⟩ := hev
      refine ⟨N, fun k hk => ?_⟩
      rw [← (hstep k).1]
      exact hN (2 * k + 1) (by omega)
  · rintro ⟨p, heven, hfreq, hev⟩
    refine ⟨p, heven, ?_, ?_⟩
    · rw [Filter.frequently_atTop] at hfreq ⊢
      intro N
      obtain ⟨k, hk, hp⟩ := hfreq N
      refine ⟨2 * k + 1, by omega, ?_⟩
      rw [(hstep k).1]
      exact hp
    · rw [Filter.eventually_atTop] at hev ⊢
      obtain ⟨K, hK⟩ := hev
      refine ⟨2 * K + 1, fun n hn => ?_⟩
      rw [hc_at n (by omega)]
      exact hK ((n - 1) / 2) (by omega)

/-! ### Section 2: Encoded Finite Parity Games (`PGCode`) & `Primrec` Solver (`solvePG`) -/

/-- Encoded finite 2-player parity game `(N, owners, succs, prios)` on `Fin (N + 1)`:
`owner = true` is Eve (Player 0), `owner = false` is Adam (Player 1). -/
abbrev PGCode : Type := ℕ × List Bool × List (List ℕ) × List ℕ

def owner (g : PGCode) (v : Fin (g.1 + 1)) : Bool :=
  g.2.1.getD v.val false

def prio (g : PGCode) (v : Fin (g.1 + 1)) : ℕ :=
  g.2.2.2.getD v.val 0

def filterFinAux (N : ℕ) : List ℕ → List (Fin (N + 1))
  | [] => []
  | u :: us =>
      if h : u < N + 1 then ⟨u, h⟩ :: filterFinAux N us
      else filterFinAux N us

def succList (g : PGCode) (v : Fin (g.1 + 1)) : List (Fin (g.1 + 1)) :=
  let l := filterFinAux g.1 (g.2.2.1.getD v.val [])
  if l.isEmpty then [v] else l

lemma succList_ne_nil (g : PGCode) (v : Fin (g.1 + 1)) : succList g v ≠ [] := by
  unfold succList
  dsimp only
  cases filterFinAux g.1 (g.2.2.1.getD v.val []) <;> simp

lemma succList_nonempty (g : PGCode) (v : Fin (g.1 + 1)) :
    ∃ u : Fin (g.1 + 1), u ∈ succList g v :=
  ⟨(succList g v).head (succList_ne_nil g v), List.head_mem (succList_ne_nil g v)⟩

/-- Nat-level mirrors of `owner`, `prio`, `succList`. -/
def ownerNat (g : PGCode) (v : ℕ) : Bool :=
  g.2.1.getD v false

def prioNat (g : PGCode) (v : ℕ) : ℕ :=
  g.2.2.2.getD v 0

def filterLtNat (M : ℕ) (l : List ℕ) : List ℕ :=
  l.flatMap fun u => if u < M then [u] else []

def succNat (g : PGCode) (v : ℕ) : List ℕ :=
  let l := filterLtNat (g.1 + 1) (g.2.2.1.getD v [])
  if l.length = 0 then [v] else l

lemma map_val_filterFinAux (N : ℕ) (raw : List ℕ) :
    (filterFinAux N raw).map Fin.val = filterLtNat (N + 1) raw := by
  induction raw with
  | nil => rfl
  | cons u us ih =>
    unfold filterFinAux filterLtNat
    by_cases h : u < N + 1
    · rw [dif_pos h, List.map_cons, List.flatMap_cons, if_pos h, List.singleton_append]
      exact congrArg (u :: ·) ih
    · rw [dif_neg h, List.flatMap_cons, if_neg h, List.nil_append]
      exact ih

lemma map_val_succList (g : PGCode) (v : Fin (g.1 + 1)) :
    (succList g v).map Fin.val = succNat g v.val := by
  unfold succList succNat
  have hmap := map_val_filterFinAux g.1 (g.2.2.1.getD v.val [])
  set lf := filterFinAux g.1 (g.2.2.1.getD v.val [])
  rw [← hmap]
  cases lf <;> simp

lemma mem_succList_iff_mem_succNat (g : PGCode) (v u : Fin (g.1 + 1)) :
    u ∈ succList g v ↔ u.val ∈ succNat g v.val := by
  rw [← map_val_succList, List.mem_map]
  constructor
  · intro hu
    exact ⟨u, hu, rfl⟩
  · rintro ⟨w, hw, hw_eq⟩
    exact Fin.ext hw_eq ▸ hw

def andBool (a b : Bool) : Bool := if a = true then b else false
def orBool (a b : Bool) : Bool := if a = true then true else b
def notBool (a : Bool) : Bool := if a = true then false else true
def eqBool (a b : ℕ) : Bool := if a = b then true else false
def ltBool (a b : ℕ) : Bool := if a < b then true else false

@[simp] lemma andBool_eq (a b : Bool) : andBool a b = (a && b) := by cases a <;> cases b <;> rfl
@[simp] lemma orBool_eq (a b : Bool) : orBool a b = (a || b) := by cases a <;> cases b <;> rfl
@[simp] lemma notBool_eq (a : Bool) : notBool a = !a := by cases a <;> rfl
@[simp] lemma eqBool_eq (a b : ℕ) : eqBool a b = decide (a = b) := by
  unfold eqBool; split_ifs with h <;> simp [h]
@[simp] lemma ltBool_eq (a b : ℕ) : ltBool a b = decide (a < b) := by
  unfold ltBool; split_ifs with h <;> simp [h]

def memNat (x : ℕ) (l : List ℕ) : Bool :=
  l.foldl (fun acc y => orBool acc (decide (y = x))) false

lemma memNat_iff (x : ℕ) (l : List ℕ) : memNat x l = true ↔ x ∈ l := by
  suffices ∀ (b : Bool),
      l.foldl (fun acc y => orBool acc (decide (y = x))) b = true ↔ b = true ∨ x ∈ l by
    simpa [memNat] using this false
  induction l with
  | nil => intro b; simp
  | cons y ys ih =>
    intro b
    rw [List.foldl_cons, ih (orBool b (decide (y = x)))]
    simp only [orBool_eq, Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
    tauto

def myPow (b e : ℕ) : ℕ :=
  (List.range e).foldl (fun acc _ => acc * b) 1

lemma myPow_eq (b e : ℕ) : myPow b e = b ^ e := by
  unfold myPow
  induction e with
  | zero => simp
  | succ e ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih, pow_succ]

def stratOfCode (M c : ℕ) : List ℕ :=
  (List.range M).map fun i => (c / myPow M i) % M

lemma stratOfCode_length (M c : ℕ) : (stratOfCode M c).length = M := by
  simp [stratOfCode]

lemma stratOfCode_getD (M c v : ℕ) (hv : v < M) :
    (stratOfCode M c).getD v 0 = (c / M ^ v) % M := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [stratOfCode, hv]),
    Option.getD_some]
  simp [stratOfCode, myPow_eq]

lemma exists_code_of_finFun {B : ℕ} (hB : 0 < B) :
    ∀ (M : ℕ) (f : Fin M → Fin B),
      ∃ c < B ^ M, ∀ i : Fin M, (c / B ^ i.val) % B = (f i).val
  | 0, _ => ⟨0, by simp, fun i => Fin.elim0 i⟩
  | M + 1, f => by
      obtain ⟨c', hc'_lt, hc'_eq⟩ := exists_code_of_finFun hB M (fun j => f j.succ)
      refine ⟨(f 0).val + B * c', ?_, ?_⟩
      · have hf0 : (f 0).val < B := (f 0).isLt
        calc
          (f 0).val + B * c' < B + B * c' := by omega
          _ = B * (c' + 1) := by ring
          _ ≤ B * B ^ M := Nat.mul_le_mul_left B (by omega)
          _ = B ^ (M + 1) := by rw [pow_succ']
      · intro i
        refine Fin.cases ?_ ?_ i
        · simp only [Fin.val_zero, pow_zero, Nat.div_one]
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (f 0).isLt]
        · intro j
          simp only [Fin.val_succ, pow_succ', ← Nat.div_div_eq_div_mul]
          have hdiv : ((f 0).val + B * c') / B = c' := by
            rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt (f 0).isLt, zero_add]
          rw [hdiv]
          exact hc'_eq j

def outStratNat (g : PGCode) (σ : List ℕ) (v : ℕ) : List ℕ :=
  if ownerNat g v = true then [σ.getD v 0] else succNat g v

def validStratNat (g : PGCode) (σ : List ℕ) : Bool :=
  andBool (decide (σ.length = g.1 + 1))
    ((List.range (g.1 + 1)).foldl
      (fun ok v =>
        andBool ok
          (andBool (decide (σ.getD v 0 < g.1 + 1))
            (if ownerNat g v = true then memNat (σ.getD v 0) (succNat g v) else true)))
      true)

def stratToFin (g : PGCode) (σ : List ℕ) (v : Fin (g.1 + 1)) : Fin (g.1 + 1) :=
  ⟨(σ.getD v.val 0) % (g.1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

/-! #### Shallow `ℕ`-Packed Reachability Engine (avoids deep tuple `Primcodable` blowup) -/

/-- Pack `(M, minP, start, adj, prios, outStart)` into a single `ℕ` for fast `Primrec` checking.
Specifically `cfg` packs `Nat.pair (Nat.pair M minP) (Nat.pair (Encodable.encode adj) (Nat.pair (Encodable.encode prios) (Encodable.encode outStart)))`. -/
def packReachCfg (g : PGCode) (σ : List ℕ) (minP start : ℕ) : ℕ :=
  let M := g.1 + 1
  let adj : List (List ℕ) := (List.range M).map (outStratNat g σ)
  let prios : List ℕ := g.2.2.2
  let outStart : List ℕ := outStratNat g σ start
  Nat.pair (Nat.pair M minP)
    (Nat.pair (Encodable.encode adj)
      (Nat.pair (Encodable.encode prios) (Encodable.encode outStart)))

def unionStepPacked (cfg : ℕ) (S : List ℕ) : List ℕ :=
  let M := cfg.unpair.1.unpair.1
  let minP := cfg.unpair.1.unpair.2
  let adj := (Encodable.decode (α := List (List ℕ)) cfg.unpair.2.unpair.1).getD []
  let prios := (Encodable.decode (α := List ℕ) cfg.unpair.2.unpair.2.unpair.1).getD []
  let outStart := (Encodable.decode (α := List ℕ) cfg.unpair.2.unpair.2.unpair.2).getD []
  (List.range M).flatMap fun u =>
    if minP ≤ prios.getD u 0 then
      let fromStart := memNat u outStart
      let fromS := S.foldl (fun acc v => orBool acc (memNat u (adj.getD v []))) false
      if orBool (memNat u S) (orBool fromStart fromS) = true then [u] else []
    else []

def reachPlusPacked (cfg : ℕ) : List ℕ :=
  let M := cfg.unpair.1.unpair.1
  (List.range M).foldl (fun S _ => unionStepPacked cfg S) []

def reachPlusNat (g : PGCode) (σ : List ℕ) (minP start : ℕ) : List ℕ :=
  reachPlusPacked (packReachCfg g σ minP start)

def isReachableNat (g : PGCode) (σ : List ℕ) (v0 w : ℕ) : Bool :=
  orBool (decide (w = v0)) (memNat w (reachPlusNat g σ 0 v0))

def badVertexNat (g : PGCode) (v0 : ℕ) (σ : List ℕ) (w : ℕ) : Bool :=
  andBool (isReachableNat g σ v0 w)
    (andBool (decide (prioNat g w % 2 = 1))
      (memNat w (reachPlusNat g σ (prioNat g w) w)))

def winsStratNat (g : PGCode) (v0 : ℕ) (σ : List ℕ) : Bool :=
  andBool (validStratNat g σ)
    ((List.range (g.1 + 1)).foldl
      (fun ok w => andBool ok (notBool (badVertexNat g v0 σ w)))
      true)

/-- Executable primitive-recursive parity game solver: searches all `(N+1)^(N+1)` memoryless
Eve strategies and returns `some σ` for the first cycle-winning strategy from `v0`, or `none`. -/
def solvePG (g : PGCode) (v0 : ℕ) : Option (List ℕ) :=
  let M := g.1 + 1
  (List.range (myPow M M)).foldl
    (fun acc c =>
      match acc with
      | some s => some s
      | none =>
          let σ := stratOfCode M c
          if winsStratNat g v0 σ = true then some σ else none)
    none

/-! #### Fast `Primrec` Proofs for `solvePG` (all domains have tuple depth ≤ 2) -/

lemma primrec₂_natPair : Primrec₂ Nat.pair :=
  Primrec.encode

lemma primrec₂_andBool : Primrec₂ andBool :=
  Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const true)) Primrec.snd (Primrec.const false)

lemma primrec₂_orBool : Primrec₂ orBool :=
  Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const true)) (Primrec.const true) Primrec.snd

lemma primrec_notBool : Primrec notBool :=
  Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const true))
    (Primrec.const false) (Primrec.const true)

lemma primrec₂_eqBool : Primrec₂ eqBool :=
  Primrec.ite Primrec.eq (Primrec.const true) (Primrec.const false)

lemma primrec₂_ltBool : Primrec₂ ltBool :=
  Primrec.ite Primrec.nat_lt (Primrec.const true) (Primrec.const false)

lemma primrec_foldl_clean {α σ β : Type*} [Primcodable α] [Primcodable σ] [Primcodable β]
    {fl : α → List β} {fi : α → σ} {fs : α → σ → β → σ}
    (hl : Primrec fl) (hi : Primrec fi)
    (hs : Primrec fun q : α × (σ × β) => fs q.1 q.2.1 q.2.2) :
    Primrec fun x => (fl x).foldl (fun s b => fs x s b) (fi x) :=
  (Primrec.list_foldl hl hi hs.to₂).of_eq fun _ => by
    congr 1

lemma primrec₂_memNat : Primrec₂ memNat :=
  Primrec.list_foldl Primrec.snd (Primrec.const false)
    (primrec₂_orBool.comp
      (Primrec.fst.comp Primrec.snd)
      (Primrec.ite
        (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
        (Primrec.const true) (Primrec.const false))).to₂

lemma primrec₂_myPow : Primrec₂ myPow :=
  Primrec.list_foldl (Primrec.list_range.comp Primrec.snd) (Primrec.const 1)
    (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst)).to₂

lemma primrec₂_stratOfCode : Primrec₂ stratOfCode :=
  Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    (Primrec.nat_mod.comp
      (Primrec.nat_div.comp
        (Primrec.snd.comp Primrec.fst)
        (primrec₂_myPow.comp (Primrec.fst.comp Primrec.fst) Primrec.snd))
      (Primrec.fst.comp Primrec.fst)).to₂

lemma primrec₂_filterLtNat : Primrec₂ filterLtNat :=
  Primrec.list_flatMap Primrec.snd
    (Primrec.ite (Primrec.nat_lt.comp Primrec.snd (Primrec.fst.comp Primrec.fst))
      (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
      (Primrec.const [])).to₂

/-- Pack `PGCode` into a single `ℕ` so every inner combinator has shallow `ℕ` types. -/
def packPG (g : PGCode) : ℕ :=
  Nat.pair (Nat.pair g.1 (Encodable.encode g.2.1))
    (Nat.pair (Encodable.encode g.2.2.1) (Encodable.encode g.2.2.2))

lemma primrec_packPG : Primrec packPG := by
  have h1 : Primrec fun g : PGCode => g.1 := Primrec.fst
  have h21 : Primrec fun g : PGCode => Encodable.encode g.2.1 :=
    Primrec.encode.comp (Primrec.fst.comp Primrec.snd)
  have h221 : Primrec fun g : PGCode => Encodable.encode g.2.2.1 :=
    Primrec.encode.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have h222 : Primrec fun g : PGCode => Encodable.encode g.2.2.2 :=
    Primrec.encode.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact primrec₂_natPair.comp (primrec₂_natPair.comp h1 h21) (primrec₂_natPair.comp h221 h222)

def ownerPacked (gp v : ℕ) : Bool :=
  ((Encodable.decode (α := List Bool) gp.unpair.1.unpair.2).getD []).getD v false

def prioPacked (gp v : ℕ) : ℕ :=
  ((Encodable.decode (α := List ℕ) gp.unpair.2.unpair.2).getD []).getD v 0

def succPacked (gp v : ℕ) : List ℕ :=
  let M := gp.unpair.1.unpair.1 + 1
  let succs := (Encodable.decode (α := List (List ℕ)) gp.unpair.2.unpair.1).getD []
  let l := filterLtNat M (succs.getD v [])
  if l.length = 0 then [v] else l

lemma ownerPacked_eq (g : PGCode) (v : ℕ) : ownerPacked (packPG g) v = ownerNat g v := by
  simp [ownerPacked, packPG, ownerNat, Nat.unpair_pair, Encodable.encodek]

lemma prioPacked_eq (g : PGCode) (v : ℕ) : prioPacked (packPG g) v = prioNat g v := by
  simp [prioPacked, packPG, prioNat, Nat.unpair_pair]

lemma succPacked_eq (g : PGCode) (v : ℕ) : succPacked (packPG g) v = succNat g v := by
  simp [succPacked, packPG, succNat, Nat.unpair_pair]

lemma primrec₂_ownerPacked : Primrec₂ ownerPacked := by
  have hl : Primrec fun p : ℕ × ℕ => (Encodable.decode (α := List Bool) p.1.unpair.1.unpair.2).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)))))
      (Primrec.const [])
  exact (Primrec.list_getD false).comp hl Primrec.snd

lemma primrec₂_prioPacked : Primrec₂ prioPacked := by
  have hl : Primrec fun p : ℕ × ℕ => (Encodable.decode (α := List ℕ) p.1.unpair.2.unpair.2).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))))
      (Primrec.const [])
  exact (Primrec.list_getD 0).comp hl Primrec.snd

lemma primrec₂_succPacked : Primrec₂ succPacked := by
  have hM : Primrec fun p : ℕ × ℕ => p.1.unpair.1.unpair.1 + 1 :=
    Primrec.succ.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))))
  have hsuccs : Primrec fun p : ℕ × ℕ => (Encodable.decode (α := List (List ℕ)) p.1.unpair.2.unpair.1).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))))
      (Primrec.const [])
  have hl : Primrec fun p : ℕ × ℕ =>
      filterLtNat (p.1.unpair.1.unpair.1 + 1)
        (((Encodable.decode (α := List (List ℕ)) p.1.unpair.2.unpair.1).getD []).getD p.2 []) :=
    primrec₂_filterLtNat.comp hM ((Primrec.list_getD []).comp hsuccs Primrec.snd)
  exact Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp hl) (Primrec.const 0))
    (Primrec.list_cons.comp Primrec.snd (Primrec.const [])) hl

def outStratPacked (gpσ : ℕ) (v : ℕ) : List ℕ :=
  let gp := gpσ.unpair.1
  let σ := (Encodable.decode (α := List ℕ) gpσ.unpair.2).getD []
  if ownerPacked gp v = true then [σ.getD v 0] else succPacked gp v

lemma primrec₂_outStratPacked : Primrec₂ outStratPacked := by
  have hgp : Primrec fun p : ℕ × ℕ => p.1.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  have hσ : Primrec fun p : ℕ × ℕ => (Encodable.decode (α := List ℕ) p.1.unpair.2).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))) (Primrec.const [])
  exact Primrec.ite (Primrec.eq.comp (primrec₂_ownerPacked.comp hgp Primrec.snd) (Primrec.const true))
    (Primrec.list_cons.comp ((Primrec.list_getD 0).comp hσ Primrec.snd) (Primrec.const []))
    (primrec₂_succPacked.comp hgp Primrec.snd)

lemma primrec₂_unionStepPacked : Primrec₂ unionStepPacked := by
  have hM : Primrec fun p : ℕ × List ℕ => p.1.unpair.1.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)))
  have hminP : Primrec fun p : ℕ × List ℕ => p.1.unpair.1.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)))
  have hadj : Primrec fun p : ℕ × List ℕ => (Encodable.decode (α := List (List ℕ)) p.1.unpair.2.unpair.1).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))))
      (Primrec.const [])
  have hprios : Primrec fun p : ℕ × List ℕ => (Encodable.decode (α := List ℕ) p.1.unpair.2.unpair.2.unpair.1).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))))))
      (Primrec.const [])
  have houtS : Primrec fun p : ℕ × List ℕ => (Encodable.decode (α := List ℕ) p.1.unpair.2.unpair.2.unpair.2).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))))))
      (Primrec.const [])
  -- Encode `(adj, u)` as `ℕ` inside `fromS` fold to keep depth = 2!
  have hfromS_aux : Primrec₂ fun (au : ℕ) (S : List ℕ) =>
      let adj := (Encodable.decode (α := List (List ℕ)) au.unpair.1).getD []
      let u := au.unpair.2
      S.foldl (fun acc v => orBool acc (memNat u (adj.getD v []))) false := by
    have r_adj : Primrec fun q : (ℕ × List ℕ) × (Bool × ℕ) =>
        (Encodable.decode (α := List (List ℕ)) q.1.1.unpair.1).getD [] :=
      Primrec.option_getD.comp
        (Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst))))
        (Primrec.const [])
    have r_u : Primrec fun q : (ℕ × List ℕ) × (Bool × ℕ) => q.1.1.unpair.2 :=
      Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst))
    have r_step : Primrec fun q : (ℕ × List ℕ) × (Bool × ℕ) =>
        orBool q.2.1
          (memNat q.1.1.unpair.2
            (((Encodable.decode (α := List (List ℕ)) q.1.1.unpair.1).getD []).getD q.2.2 [])) :=
      primrec₂_orBool.comp (Primrec.fst.comp Primrec.snd)
        (primrec₂_memNat.comp r_u ((Primrec.list_getD []).comp r_adj (Primrec.snd.comp Primrec.snd)))
    exact Primrec.list_foldl Primrec.snd (Primrec.const false) r_step.to₂
  have hbody : Primrec fun q : (ℕ × List ℕ) × ℕ =>
      let cfg := q.1.1
      let S := q.1.2
      let u := q.2
      let minP := cfg.unpair.1.unpair.2
      let adj := (Encodable.decode (α := List (List ℕ)) cfg.unpair.2.unpair.1).getD []
      let prios := (Encodable.decode (α := List ℕ) cfg.unpair.2.unpair.2.unpair.1).getD []
      let outStart := (Encodable.decode (α := List ℕ) cfg.unpair.2.unpair.2.unpair.2).getD []
      if minP ≤ prios.getD u 0 then
        let fromStart := memNat u outStart
        let fromS := S.foldl (fun acc v => orBool acc (memNat u (adj.getD v []))) false
        if orBool (memNat u S) (orBool fromStart fromS) = true then [u] else []
      else [] := by
    have fstQ : Primrec fun q : (ℕ × List ℕ) × ℕ => q.1 := Primrec.fst
    have q_minP := hminP.comp fstQ
    have q_prios := hprios.comp fstQ
    have q_outS := houtS.comp fstQ
    have q_S : Primrec fun q : (ℕ × List ℕ) × ℕ => q.1.2 := Primrec.snd.comp fstQ
    have q_u : Primrec fun q : (ℕ × List ℕ) × ℕ => q.2 := Primrec.snd
    have q_adjEnc : Primrec fun q : (ℕ × List ℕ) × ℕ => Encodable.encode ((Encodable.decode (α := List (List ℕ)) q.1.1.unpair.2.unpair.1).getD []) :=
      Primrec.encode.comp (hadj.comp fstQ)
    have q_fromS : Primrec fun q : (ℕ × List ℕ) × ℕ =>
        let adj := (Encodable.decode (α := List (List ℕ)) q.1.1.unpair.2.unpair.1).getD []
        q.1.2.foldl (fun acc v => orBool acc (memNat q.2 (adj.getD v []))) false := by
      have hcomp := hfromS_aux.comp (primrec₂_natPair.comp q_adjEnc q_u) q_S
      exact hcomp.of_eq fun q => by simp [Nat.unpair_pair]
    have q_cond : Primrec fun q : (ℕ × List ℕ) × ℕ =>
        orBool (memNat q.2 q.1.2)
          (orBool (memNat q.2 ((Encodable.decode (α := List ℕ) q.1.1.unpair.2.unpair.2.unpair.2).getD []))
            (let adj := (Encodable.decode (α := List (List ℕ)) q.1.1.unpair.2.unpair.1).getD []
             q.1.2.foldl (fun acc v => orBool acc (memNat q.2 (adj.getD v []))) false)) :=
      primrec₂_orBool.comp (primrec₂_memNat.comp q_u q_S)
        (primrec₂_orBool.comp (primrec₂_memNat.comp q_u q_outS) q_fromS)
    exact Primrec.ite (Primrec.nat_le.comp q_minP ((Primrec.list_getD 0).comp q_prios q_u))
      (Primrec.ite (Primrec.eq.comp q_cond (Primrec.const true))
        (Primrec.list_cons.comp q_u (Primrec.const [])) (Primrec.const []))
      (Primrec.const [])
  exact Primrec.list_flatMap (Primrec.list_range.comp hM) hbody.to₂

lemma primrec_reachPlusPacked : Primrec reachPlusPacked := by
  have hM : Primrec fun cfg : ℕ => cfg.unpair.1.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
  have hstep : Primrec fun q : ℕ × (List ℕ × ℕ) => unionStepPacked q.1 q.2.1 :=
    primrec₂_unionStepPacked.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  exact Primrec.list_foldl (Primrec.list_range.comp hM) (Primrec.const []) hstep.to₂

def packReachCfgPacked (gpσ : ℕ) (ms : ℕ) : ℕ :=
  let gp := gpσ.unpair.1
  let M := gp.unpair.1.unpair.1 + 1
  let minP := ms.unpair.1
  let start := ms.unpair.2
  let adj : List (List ℕ) := (List.range M).map (outStratPacked gpσ)
  let priosEnc := gp.unpair.2.unpair.2
  let prios := (Encodable.decode (α := List ℕ) priosEnc).getD []
  let outStart := outStratPacked gpσ start
  Nat.pair (Nat.pair M minP)
    (Nat.pair (Encodable.encode adj)
      (Nat.pair (Encodable.encode prios) (Encodable.encode outStart)))

lemma packReachCfgPacked_eq (g : PGCode) (σ : List ℕ) (minP start : ℕ) :
    packReachCfgPacked (Nat.pair (packPG g) (Encodable.encode σ)) (Nat.pair minP start) =
      packReachCfg g σ minP start := by
  have hout : outStratPacked (Nat.pair (packPG g) (Encodable.encode σ)) = outStratNat g σ := by
    funext v
    simp [outStratPacked, Nat.unpair_pair, ownerPacked_eq, succPacked_eq, outStratNat]
  unfold packReachCfgPacked packReachCfg
  simp only [Nat.unpair_pair, hout]
  have hgp1 : (packPG g).unpair.1.unpair.1 = g.1 := by simp [packPG, Nat.unpair_pair]
  have hgp2 : (Encodable.decode (α := List ℕ) (packPG g).unpair.2.unpair.2).getD [] = g.2.2.2 := by
    simp [packPG, Nat.unpair_pair]
  rw [hgp1, hgp2]

lemma primrec₂_packReachCfgPacked : Primrec₂ packReachCfgPacked := by
  have hgp : Primrec fun p : ℕ × ℕ => p.1.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  have hM : Primrec fun p : ℕ × ℕ => p.1.unpair.1.unpair.1.unpair.1 + 1 :=
    Primrec.succ.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp (Primrec.unpair.comp hgp))))
  have hminP : Primrec fun p : ℕ × ℕ => p.2.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hstart : Primrec fun p : ℕ × ℕ => p.2.unpair.2 := Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hadj : Primrec fun p : ℕ × ℕ => Encodable.encode ((List.range (p.1.unpair.1.unpair.1.unpair.1 + 1)).map (outStratPacked p.1)) :=
    Primrec.encode.comp
      (Primrec.list_map (Primrec.list_range.comp hM)
        (primrec₂_outStratPacked.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂)
  have hprios : Primrec fun p : ℕ × ℕ =>
      Encodable.encode ((Encodable.decode (α := List ℕ) p.1.unpair.1.unpair.2.unpair.2).getD []) :=
    Primrec.encode.comp
      (Primrec.option_getD.comp
        (Primrec.decode.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hgp)))))
        (Primrec.const []))
  have houtS : Primrec fun p : ℕ × ℕ => Encodable.encode (outStratPacked p.1 p.2.unpair.2) :=
    Primrec.encode.comp (primrec₂_outStratPacked.comp Primrec.fst hstart)
  exact primrec₂_natPair.comp (primrec₂_natPair.comp hM hminP)
    (primrec₂_natPair.comp hadj (primrec₂_natPair.comp hprios houtS))

def validStratStep (gpσ : ℕ) (ok : Bool) (v : ℕ) : Bool :=
  let gp := gpσ.unpair.1
  let M := gp.unpair.1.unpair.1 + 1
  let σ := (Encodable.decode (α := List ℕ) gpσ.unpair.2).getD []
  andBool ok
    (andBool (ltBool (σ.getD v 0) M)
      (if ownerPacked gp v = true then memNat (σ.getD v 0) (succPacked gp v) else true))

lemma primrec_validStratStep :
    Primrec fun q : ℕ × (Bool × ℕ) => validStratStep q.1 q.2.1 q.2.2 := by
  have q_gp : Primrec fun q : ℕ × (Bool × ℕ) => q.1.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  have q_M : Primrec fun q : ℕ × (Bool × ℕ) => q.1.unpair.1.unpair.1.unpair.1 + 1 :=
    Primrec.succ.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp (Primrec.unpair.comp q_gp))))
  have q_σ : Primrec fun q : ℕ × (Bool × ℕ) => (Encodable.decode (α := List ℕ) q.1.unpair.2).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))) (Primrec.const [])
  have q_ok : Primrec fun q : ℕ × (Bool × ℕ) => q.2.1 := Primrec.fst.comp Primrec.snd
  have q_v : Primrec fun q : ℕ × (Bool × ℕ) => q.2.2 := Primrec.snd.comp Primrec.snd
  have q_get := (Primrec.list_getD 0).comp q_σ q_v
  have q_lt := primrec₂_ltBool.comp q_get q_M
  have q_mem := Primrec.ite (Primrec.eq.comp (primrec₂_ownerPacked.comp q_gp q_v) (Primrec.const true))
    (primrec₂_memNat.comp q_get (primrec₂_succPacked.comp q_gp q_v))
    (Primrec.const true)
  exact primrec₂_andBool.comp q_ok (primrec₂_andBool.comp q_lt q_mem)

def validStratPacked (gpσ : ℕ) : Bool :=
  let gp := gpσ.unpair.1
  let M := gp.unpair.1.unpair.1 + 1
  let σ := (Encodable.decode (α := List ℕ) gpσ.unpair.2).getD []
  andBool (eqBool σ.length M)
    ((List.range M).foldl (fun ok v => validStratStep gpσ ok v) true)

lemma validStratPacked_eq (g : PGCode) (σ : List ℕ) :
    validStratPacked (Nat.pair (packPG g) (Encodable.encode σ)) = validStratNat g σ := by
  have hgp1 : (packPG g).unpair.1.unpair.1 = g.1 := by simp [packPG, Nat.unpair_pair]
  unfold validStratPacked validStratNat
  simp only [Nat.unpair_pair, Encodable.encodek, Option.getD_some, hgp1, eqBool_eq]
  congr 2
  funext ok v
  unfold validStratStep
  simp only [Nat.unpair_pair, Encodable.encodek, Option.getD_some, hgp1,
    ltBool_eq, ownerPacked_eq, succPacked_eq]

lemma primrec_validStratPacked : Primrec validStratPacked := by
  have hgp : Primrec fun x : ℕ => x.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hM : Primrec fun x : ℕ => x.unpair.1.unpair.1.unpair.1 + 1 :=
    Primrec.succ.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp (Primrec.unpair.comp hgp))))
  have hσ : Primrec fun x : ℕ => (Encodable.decode (α := List ℕ) x.unpair.2).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.snd.comp Primrec.unpair)) (Primrec.const [])
  have hlenOk := primrec₂_eqBool.comp (Primrec.list_length.comp hσ) hM
  exact primrec₂_andBool.comp hlenOk
    (primrec_foldl_clean (Primrec.list_range.comp hM) (Primrec.const true) primrec_validStratStep)

def badVertexPacked (gpv0σ : ℕ) (w : ℕ) : Bool :=
  let gpσ := gpv0σ.unpair.1
  let v0 := gpv0σ.unpair.2
  let gp := gpσ.unpair.1
  let reach0 := reachPlusPacked (packReachCfgPacked gpσ (Nat.pair 0 v0))
  let isReach := orBool (eqBool w v0) (memNat w reach0)
  let pw := prioPacked gp w
  let cyc := reachPlusPacked (packReachCfgPacked gpσ (Nat.pair pw w))
  andBool isReach (andBool (eqBool (pw % 2) 1) (memNat w cyc))

lemma primrec₂_badVertexPacked : Primrec₂ badVertexPacked := by
  have hgpσ : Primrec fun p : ℕ × ℕ => p.1.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  have hv0 : Primrec fun p : ℕ × ℕ => p.1.unpair.2 := Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)
  have hgp : Primrec fun p : ℕ × ℕ => p.1.unpair.1.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp hgpσ)
  have hw : Primrec fun p : ℕ × ℕ => p.2 := Primrec.snd
  have hreach0 : Primrec fun p : ℕ × ℕ =>
      reachPlusPacked (packReachCfgPacked p.1.unpair.1 (Nat.pair 0 p.1.unpair.2)) :=
    primrec_reachPlusPacked.comp (primrec₂_packReachCfgPacked.comp hgpσ (primrec₂_natPair.comp (Primrec.const 0) hv0))
  have hisReach := primrec₂_orBool.comp (primrec₂_eqBool.comp hw hv0) (primrec₂_memNat.comp hw hreach0)
  have hpw := primrec₂_prioPacked.comp hgp hw
  have hodd := primrec₂_eqBool.comp (Primrec.nat_mod.comp hpw (Primrec.const 2)) (Primrec.const 1)
  have hcyc : Primrec fun p : ℕ × ℕ =>
      reachPlusPacked (packReachCfgPacked p.1.unpair.1 (Nat.pair (prioPacked p.1.unpair.1.unpair.1 p.2) p.2)) :=
    primrec_reachPlusPacked.comp (primrec₂_packReachCfgPacked.comp hgpσ (primrec₂_natPair.comp hpw hw))
  exact primrec₂_andBool.comp hisReach (primrec₂_andBool.comp hodd (primrec₂_memNat.comp hw hcyc))

def winsStratStep (gpv0σ : ℕ) (ok : Bool) (w : ℕ) : Bool :=
  andBool ok (notBool (badVertexPacked gpv0σ w))

lemma primrec_winsStratStep :
    Primrec fun q : ℕ × (Bool × ℕ) => winsStratStep q.1 q.2.1 q.2.2 :=
  primrec₂_andBool.comp (Primrec.fst.comp Primrec.snd)
    (primrec_notBool.comp (primrec₂_badVertexPacked.comp Primrec.fst (Primrec.snd.comp Primrec.snd)))

def winsStratPacked (gpv0σ : ℕ) : Bool :=
  let gpσ := gpv0σ.unpair.1
  let gp := gpσ.unpair.1
  let M := gp.unpair.1.unpair.1 + 1
  andBool (validStratPacked gpσ)
    ((List.range M).foldl (fun ok w => winsStratStep gpv0σ ok w) true)

lemma winsStratPacked_eq (g : PGCode) (v0 : ℕ) (σ : List ℕ) :
    winsStratPacked (Nat.pair (Nat.pair (packPG g) (Encodable.encode σ)) v0) = winsStratNat g v0 σ := by
  have hgp1 : (packPG g).unpair.1.unpair.1 = g.1 := by simp [packPG, Nat.unpair_pair]
  have hbad : ∀ w, badVertexPacked (Nat.pair (Nat.pair (packPG g) (Encodable.encode σ)) v0) w =
      badVertexNat g v0 σ w := by
    intro w
    unfold badVertexPacked badVertexNat isReachableNat reachPlusNat
    simp only [Nat.unpair_pair, packReachCfgPacked_eq, prioPacked_eq, eqBool_eq]
  unfold winsStratPacked winsStratNat
  simp only [Nat.unpair_pair, validStratPacked_eq, hgp1]
  congr 2
  funext ok w
  simp [winsStratStep, hbad]

lemma primrec_winsStratPacked : Primrec winsStratPacked := by
  have hgpσ : Primrec fun x : ℕ => x.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hgp : Primrec fun x : ℕ => x.unpair.1.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp hgpσ)
  have hM : Primrec fun x : ℕ => x.unpair.1.unpair.1.unpair.1.unpair.1 + 1 :=
    Primrec.succ.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp (Primrec.unpair.comp hgp))))
  exact primrec₂_andBool.comp (primrec_validStratPacked.comp hgpσ)
    (primrec_foldl_clean (Primrec.list_range.comp hM) (Primrec.const true) primrec_winsStratStep)

def solvePGStep (gpv0 : ℕ) (acc : Option (List ℕ)) (c : ℕ) : Option (List ℕ) :=
  match acc with
  | some s => some s
  | none =>
      let gp := gpv0.unpair.1
      let v0 := gpv0.unpair.2
      let M := gp.unpair.1.unpair.1 + 1
      let σ := stratOfCode M c
      let gpv0σ := Nat.pair (Nat.pair gp (Encodable.encode σ)) v0
      if winsStratPacked gpv0σ = true then some σ else none

lemma primrec_solvePGStep :
    Primrec fun q : ℕ × (Option (List ℕ) × ℕ) => solvePGStep q.1 q.2.1 q.2.2 := by
  have q_gp : Primrec fun q : ℕ × (Option (List ℕ) × ℕ) => q.1.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  have q_v0 : Primrec fun q : ℕ × (Option (List ℕ) × ℕ) => q.1.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)
  have q_M : Primrec fun q : ℕ × (Option (List ℕ) × ℕ) => q.1.unpair.1.unpair.1.unpair.1 + 1 :=
    Primrec.succ.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp (Primrec.unpair.comp q_gp))))
  have q_σ : Primrec fun q : ℕ × (Option (List ℕ) × ℕ) =>
      stratOfCode (q.1.unpair.1.unpair.1.unpair.1 + 1) q.2.2 :=
    primrec₂_stratOfCode.comp q_M (Primrec.snd.comp Primrec.snd)
  have q_gpv0σ := primrec₂_natPair.comp
    (primrec₂_natPair.comp q_gp (Primrec.encode.comp q_σ)) q_v0
  have hnoneB := Primrec.ite
    (Primrec.eq.comp (primrec_winsStratPacked.comp q_gpv0σ) (Primrec.const true))
    (Primrec.option_some.comp q_σ)
    (Primrec.const none)
  have hsomeB : Primrec fun r : (ℕ × (Option (List ℕ) × ℕ)) × List ℕ =>
      (some r.2 : Option (List ℕ)) :=
    Primrec.option_some.comp Primrec.snd
  exact (Primrec.option_casesOn (Primrec.fst.comp Primrec.snd) hnoneB hsomeB.to₂).of_eq
    fun q => by cases q.2.1 <;> rfl

def solvePGPacked (gpv0 : ℕ) : Option (List ℕ) :=
  let M := gpv0.unpair.1.unpair.1.unpair.1 + 1
  (List.range (myPow M M)).foldl (fun acc c => solvePGStep gpv0 acc c) none

lemma solvePGPacked_eq (g : PGCode) (v0 : ℕ) :
    solvePGPacked (Nat.pair (packPG g) v0) = solvePG g v0 := by
  have hgp1 : (packPG g).unpair.1.unpair.1 = g.1 := by simp [packPG, Nat.unpair_pair]
  unfold solvePGPacked solvePG
  simp only [Nat.unpair_pair, hgp1]
  congr 1
  funext acc c
  cases acc with
  | some s => rfl
  | none =>
    unfold solvePGStep
    simp only [Nat.unpair_pair, hgp1, winsStratPacked_eq]

lemma primrec_solvePGPacked : Primrec solvePGPacked := by
  have hM : Primrec fun x : ℕ => x.unpair.1.unpair.1.unpair.1 + 1 :=
    Primrec.succ.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))))
  have hrange : Primrec fun x : ℕ => List.range (myPow (x.unpair.1.unpair.1.unpair.1 + 1) (x.unpair.1.unpair.1.unpair.1 + 1)) :=
    Primrec.list_range.comp (primrec₂_myPow.comp hM hM)
  exact primrec_foldl_clean hrange (Primrec.const none) primrec_solvePGStep

theorem primrec_solvePG : Primrec fun p : PGCode × ℕ => solvePG p.1 p.2 := by
  have h := primrec_solvePGPacked.comp
    (primrec₂_natPair.comp (primrec_packPG.comp Primrec.fst) Primrec.snd)
  exact h.of_eq fun p => solvePGPacked_eq p.1 p.2

theorem computable_solvePG : Computable₂ solvePG :=
  primrec_solvePG.to_comp

/-! ### Section 3: Walk Characterization, Soundness, and Memoryless Completeness of `solvePG` -/

lemma validStratNat_spec (g : PGCode) (σ : List ℕ) (hval : validStratNat g σ = true) :
    σ.length = g.1 + 1 ∧
      (∀ v : Fin (g.1 + 1), σ.getD v.val 0 < g.1 + 1) ∧
      (∀ v : Fin (g.1 + 1), owner g v = true → stratToFin g σ v ∈ succList g v) := by
  unfold validStratNat at hval
  rw [andBool_eq, Bool.and_eq_true, decide_eq_true_eq] at hval
  rcases hval with ⟨hlen, hfold⟩
  have hfold_iff : ∀ (l : List ℕ) (init : Bool),
      l.foldl
        (fun ok v =>
          andBool ok
            (andBool (decide (σ.getD v 0 < g.1 + 1))
              (if ownerNat g v = true then memNat (σ.getD v 0) (succNat g v) else true)))
        init = true ↔
      init = true ∧ ∀ v ∈ l,
        σ.getD v 0 < g.1 + 1 ∧
          (ownerNat g v = true → memNat (σ.getD v 0) (succNat g v) = true) := by
    intro l
    induction l with
    | nil => intro init; simp
    | cons x xs ih =>
      intro init
      rw [List.foldl_cons, ih]
      simp only [andBool_eq, Bool.and_eq_true, decide_eq_true_eq, List.mem_cons]
      constructor
      · rintro ⟨⟨hinit, hx_lt, hx_mem⟩, hxs⟩
        refine ⟨hinit, fun v hv => ?_⟩
        rcases hv with rfl | hv
        · refine ⟨hx_lt, fun hown => ?_⟩
          rw [if_pos hown] at hx_mem
          exact hx_mem
        · exact hxs v hv
      · rintro ⟨hinit, hall⟩
        have hx := hall x (Or.inl rfl)
        refine ⟨⟨hinit, hx.1, ?_⟩, fun v hv => hall v (Or.inr hv)⟩
        by_cases hown : ownerNat g x = true
        · rw [if_pos hown]; exact hx.2 hown
        · rw [if_neg hown]
  obtain ⟨-, hall⟩ := (hfold_iff (List.range (g.1 + 1)) true).mp hfold
  refine ⟨hlen, ?_, ?_⟩
  · intro v
    exact (hall v.val (List.mem_range.mpr v.isLt)).1
  · intro v hown
    have hv := hall v.val (List.mem_range.mpr v.isLt)
    have hmem_nat : σ.getD v.val 0 ∈ succNat g v.val :=
      (memNat_iff _ _).mp (hv.2 hown)
    rw [mem_succList_iff_mem_succNat]
    unfold stratToFin
    dsimp only
    rwa [Nat.mod_eq_of_lt hv.1]

/-- Nonempty walk in `G_σ` staying inside `{u < g.1 + 1 | minP ≤ prioNat g u}` after step 0. -/
def HasPosWalk (g : PGCode) (σ : List ℕ) (minP start u : ℕ) : Prop :=
  ∃ (m : ℕ) (walk : ℕ → ℕ), 1 ≤ m ∧ walk 0 = start ∧ walk m = u ∧
    ∀ i < m, walk (i + 1) < g.1 + 1 ∧ minP ≤ prioNat g (walk (i + 1)) ∧
      walk (i + 1) ∈ outStratNat g σ (walk i)

lemma unionStepPacked_pack_eq (g : PGCode) (σ : List ℕ) (minP start : ℕ)
    (S : List ℕ) (hS : ∀ v ∈ S, v < g.1 + 1) :
    unionStepPacked (packReachCfg g σ minP start) S =
      (List.range (g.1 + 1)).flatMap fun u =>
        if minP ≤ prioNat g u then
          let fromStart := memNat u (outStratNat g σ start)
          let fromS := S.foldl (fun acc v => orBool acc (memNat u (outStratNat g σ v))) false
          if orBool (memNat u S) (orBool fromStart fromS) = true then [u] else []
        else [] := by
  unfold unionStepPacked packReachCfg
  simp only [Nat.unpair_pair, Encodable.encodek, Option.getD_some]
  congr 1
  funext u
  have hp : g.2.2.2.getD u 0 = prioNat g u := rfl
  rw [hp]
  by_cases hle : minP ≤ prioNat g u
  · rw [if_pos hle, if_pos hle]
    have hfold_eq : ∀ (l : List ℕ) (b : Bool), (∀ v ∈ l, v < g.1 + 1) →
        l.foldl (fun acc v => orBool acc (memNat u (((List.range (g.1 + 1)).map (outStratNat g σ)).getD v []))) b =
        l.foldl (fun acc v => orBool acc (memNat u (outStratNat g σ v))) b := by
      intro l
      induction l with
      | nil => intros; rfl
      | cons v vs ih =>
        intro b hl
        have hv : v < g.1 + 1 := hl v (List.mem_cons.mpr (Or.inl rfl))
        have hgd : ((List.range (g.1 + 1)).map (outStratNat g σ)).getD v [] = outStratNat g σ v := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hv]), Option.getD_some]
          simp
        simp only [List.foldl_cons, hgd]
        exact ih _ (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    rw [hfold_eq S false hS]
  · rw [if_neg hle, if_neg hle]

lemma mem_reachPlusNat_bdd_iff (g : PGCode) (σ : List ℕ) (minP start : ℕ) :
    ∀ (k : ℕ),
      let Sk := (List.range k).foldl (fun S _ => unionStepPacked (packReachCfg g σ minP start) S) []
      (∀ u ∈ Sk, u < g.1 + 1) ∧
      ∀ u : ℕ, u ∈ Sk ↔
        ∃ (m : ℕ) (walk : ℕ → ℕ), 1 ≤ m ∧ m ≤ k ∧ walk 0 = start ∧ walk m = u ∧
          ∀ i < m, walk (i + 1) < g.1 + 1 ∧ minP ≤ prioNat g (walk (i + 1)) ∧
            walk (i + 1) ∈ outStratNat g σ (walk i)
  | 0 => by
      dsimp only [List.range_zero, List.foldl_nil]
      refine ⟨by simp, fun u => ⟨by simp, ?_⟩⟩
      rintro ⟨m, _, hm1, hm0, _⟩
      omega
  | k + 1 => by
      obtain ⟨hSk_lt, ih⟩ := mem_reachPlusNat_bdd_iff g σ minP start k
      set Sk := (List.range k).foldl (fun S _ => unionStepPacked (packReachCfg g σ minP start) S) []
      dsimp only
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (∀ u ∈ unionStepPacked (packReachCfg g σ minP start) Sk, u < g.1 + 1) ∧ _
      rw [unionStepPacked_pack_eq g σ minP start Sk hSk_lt]
      have hfromS : ∀ (u : ℕ) (l : List ℕ) (b : Bool),
          l.foldl (fun acc v => orBool acc (memNat u (outStratNat g σ v))) b = true ↔
            b = true ∨ ∃ v ∈ l, u ∈ outStratNat g σ v := by
        intro u l
        induction l with
        | nil => intro b; simp
        | cons v vs ih_l =>
          intro b
          rw [List.foldl_cons, ih_l]
          simp only [orBool_eq, Bool.or_eq_true, memNat_iff, List.mem_cons]
          constructor
          · rintro ((hb | hmem) | ⟨w, hw, hwm⟩)
            · exact Or.inl hb
            · exact Or.inr ⟨v, Or.inl rfl, hmem⟩
            · exact Or.inr ⟨w, Or.inr hw, hwm⟩
          · rintro (hb | ⟨w, rfl | hw, hwm⟩)
            · exact Or.inl (Or.inl hb)
            · exact Or.inl (Or.inr hwm)
            · exact Or.inr ⟨w, hw, hwm⟩
      have hmem_flat : ∀ u : ℕ,
          u ∈ ((List.range (g.1 + 1)).flatMap fun x =>
            if minP ≤ prioNat g x then
              let fromStart := memNat x (outStratNat g σ start)
              let fromS := Sk.foldl (fun acc v => orBool acc (memNat x (outStratNat g σ v))) false
              if orBool (memNat x Sk) (orBool fromStart fromS) = true then [x] else []
            else []) ↔
          u < g.1 + 1 ∧ minP ≤ prioNat g u ∧
            (u ∈ Sk ∨ u ∈ outStratNat g σ start ∨ ∃ v ∈ Sk, u ∈ outStratNat g σ v) := by
        intro u
        simp only [List.mem_flatMap, List.mem_range]
        constructor
        · rintro ⟨x, hx_lt, hx_mem⟩
          split_ifs at hx_mem with hp hcond
          · simp only [List.mem_singleton] at hx_mem
            subst hx_mem
            rw [orBool_eq, orBool_eq, Bool.or_eq_true, Bool.or_eq_true,
              memNat_iff, memNat_iff, hfromS] at hcond
            rcases hcond with h1 | h2 | (hfalse | h3)
            · exact ⟨hx_lt, hp, Or.inl h1⟩
            · exact ⟨hx_lt, hp, Or.inr (Or.inl h2)⟩
            · cases hfalse
            · exact ⟨hx_lt, hp, Or.inr (Or.inr h3)⟩
          · simp at hx_mem
          · simp at hx_mem
        · rintro ⟨hu_lt, hp, hcond⟩
          refine ⟨u, hu_lt, ?_⟩
          rw [if_pos hp, if_pos]
          · simp
          · rw [orBool_eq, orBool_eq, Bool.or_eq_true, Bool.or_eq_true,
              memNat_iff, memNat_iff, hfromS]
            rcases hcond with h1 | h2 | h3
            · exact Or.inl h1
            · exact Or.inr (Or.inl h2)
            · exact Or.inr (Or.inr (Or.inr h3))
      refine ⟨fun u hu => ((hmem_flat u).mp hu).1, fun u => ?_⟩
      rw [hmem_flat]
      constructor
      · rintro ⟨hu_lt, hp, hmem | hstart | ⟨v, hv_mem, huv⟩⟩
        · obtain ⟨m, walk, hm1, hmk, hw0, hwm, hstep⟩ := (ih u).mp hmem
          exact ⟨m, walk, hm1, by omega, hw0, hwm, hstep⟩
        · refine ⟨1, fun i => if i = 0 then start else u, le_rfl, by omega, by simp, by simp, ?_⟩
          intro i hi
          have hi0 : i = 0 := by omega
          subst hi0
          simp [hu_lt, hp, hstart]
        · obtain ⟨m, walk, hm1, hmk, hw0, hwm, hstep⟩ := (ih v).mp hv_mem
          let walk' : ℕ → ℕ := fun i => if i ≤ m then walk i else u
          refine ⟨m + 1, walk', by omega, by omega, ?_, ?_, ?_⟩
          · simp [walk', hw0]
          · simp [walk']
          · intro i hi
            by_cases him : i < m
            · have h1 : i ≤ m := by omega
              have h2 : i + 1 ≤ m := by omega
              simp only [walk', h1, h2, ↓reduceIte]
              exact hstep i him
            · have hieq : i = m := by omega
              rw [hieq]
              have hnot : ¬ (m + 1 ≤ m) := by omega
              simp only [walk', le_rfl, hnot, ↓reduceIte, hwm]
              exact ⟨hu_lt, hp, huv⟩
      · rintro ⟨m, walk, hm1, hmk1, hw0, hwm, hstep⟩
        have hlast := hstep (m - 1) (by omega)
        have hm_sub : m - 1 + 1 = m := by omega
        rw [hm_sub, hwm] at hlast
        refine ⟨hlast.1, hlast.2.1, ?_⟩
        by_cases hm_eq1 : m = 1
        · subst hm_eq1
          right; left
          simpa [hw0] using hlast.2.2
        · right; right
          refine ⟨walk (m - 1), ?_, hlast.2.2⟩
          apply (ih (walk (m - 1))).mpr
          exact ⟨m - 1, walk, by omega, by omega, hw0, rfl, fun i hi => hstep i (by omega)⟩

lemma shorten_pos_walk (g : PGCode) (σ : List ℕ) (minP start u : ℕ)
    (hwalk : HasPosWalk g σ minP start u) :
    u ∈ reachPlusNat g σ minP start := by
  unfold reachPlusNat reachPlusPacked
  have hM_cfg : (packReachCfg g σ minP start).unpair.1.unpair.1 = g.1 + 1 := by
    simp [packReachCfg, Nat.unpair_pair]
  dsimp only
  rw [hM_cfg, (mem_reachPlusNat_bdd_iff g σ minP start (g.1 + 1)).2 u]
  rcases hwalk with ⟨m0, walk0, hm0, hw0, hwm0, hstep0⟩
  suffices ∀ (m : ℕ) (walk : ℕ → ℕ),
      1 ≤ m → walk 0 = start → walk m = u →
      (∀ i < m, walk (i + 1) < g.1 + 1 ∧ minP ≤ prioNat g (walk (i + 1)) ∧
        walk (i + 1) ∈ outStratNat g σ (walk i)) →
      ∃ (m' : ℕ) (walk' : ℕ → ℕ), 1 ≤ m' ∧ m' ≤ g.1 + 1 ∧ walk' 0 = start ∧ walk' m' = u ∧
        ∀ i < m', walk' (i + 1) < g.1 + 1 ∧ minP ≤ prioNat g (walk' (i + 1)) ∧
          walk' (i + 1) ∈ outStratNat g σ (walk' i) from
    this m0 walk0 hm0 hw0 hwm0 hstep0
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro walk hm1 hw_start hw_end hstep
    by_cases hle : m ≤ g.1 + 1
    · exact ⟨m, walk, hm1, hle, hw_start, hw_end, hstep⟩
    · let M := g.1 + 1
      let f : Fin (M + 1) → Fin M := fun k =>
        ⟨walk (k.val + 1), (hstep k.val (by omega)).1⟩
      obtain ⟨ka, kb, hkab, hfeq⟩ :=
        Fintype.exists_ne_map_eq_of_card_lt f (by simp)
      have hval_ne : ka.val ≠ kb.val := fun hv => hkab (Fin.ext hv)
      obtain ⟨a, b, hab, hbM, heq_ab⟩ :
          ∃ a b : ℕ, a < b ∧ b ≤ M ∧ walk (a + 1) = walk (b + 1) := by
        rcases lt_or_gt_of_ne hval_ne with hlt | hgt
        · exact ⟨ka.val, kb.val, hlt, by omega, congrArg Fin.val hfeq⟩
        · exact ⟨kb.val, ka.val, hgt, by omega, (congrArg Fin.val hfeq).symm⟩
      let d := b - a
      let m' := m - d
      let walk' : ℕ → ℕ := fun i => if i ≤ a + 1 then walk i else walk (i + d)
      have hm'_lt : m' < m := by omega
      have hm'_pos : 1 ≤ m' := by omega
      apply ih m' hm'_lt walk' hm'_pos
      · simp [walk', hw_start]
      · dsimp only [walk']
        split_ifs with hcond
        · have heq1 : m' = a + 1 := by omega
          have heq2 : m = b + 1 := by omega
          rw [heq1, heq_ab, ← heq2, hw_end]
        · have heq_add : m' + d = m := by omega
          rw [heq_add, hw_end]
      · intro i hi
        by_cases hi1 : i + 1 ≤ a + 1
        · have hi0 : i ≤ a + 1 := by omega
          simp only [walk', hi0, hi1, ↓reduceIte]
          exact hstep i (by omega)
        · by_cases hi0 : i ≤ a + 1
          · have hieq : i = a + 1 := by omega
            rw [hieq]
            have hnle : ¬ (a + 1 + 1 ≤ a + 1) := by omega
            simp only [walk', le_rfl, hnle, ↓reduceIte]
            have hidx : a + 1 + 1 + d = b + 1 + 1 := by omega
            rw [heq_ab, hidx]
            exact hstep (b + 1) (by omega)
          · simp only [walk', hi0, hi1, ↓reduceIte]
            have hidx : i + 1 + d = (i + d) + 1 := by omega
            rw [hidx]
            exact hstep (i + d) (by omega)

lemma mem_reachPlusNat_iff (g : PGCode) (σ : List ℕ) (minP start u : ℕ) :
    u ∈ reachPlusNat g σ minP start ↔ HasPosWalk g σ minP start u := by
  constructor
  · intro hmem
    unfold reachPlusNat reachPlusPacked at hmem
    have hM_cfg : (packReachCfg g σ minP start).unpair.1.unpair.1 = g.1 + 1 := by
      simp [packReachCfg, Nat.unpair_pair]
    dsimp only at hmem
    rw [hM_cfg] at hmem
    obtain ⟨m, walk, hm1, _, hw0, hwm, hstep⟩ :=
      ((mem_reachPlusNat_bdd_iff g σ minP start (g.1 + 1)).2 u).mp hmem
    exact ⟨m, walk, hm1, hw0, hwm, hstep⟩
  · exact shorten_pos_walk g σ minP start u

lemma winsStratNat_sound (g : PGCode) (v0 : Fin (g.1 + 1)) (σ : List ℕ)
    (hwins : winsStratNat g v0.val σ = true) :
    σ.length = g.1 + 1 ∧
      (∀ v : Fin (g.1 + 1), σ.getD v.val 0 < g.1 + 1) ∧
      (∀ v : Fin (g.1 + 1), owner g v = true → stratToFin g σ v ∈ succList g v) ∧
      (∀ π : ℕ → Fin (g.1 + 1), π 0 = v0 →
        (∀ n : ℕ, π (n + 1) ∈ succList g (π n)) →
        (∀ n : ℕ, owner g (π n) = true → π (n + 1) = stratToFin g σ (π n)) →
        ParityCond (fun n => prio g (π n))) := by
  unfold winsStratNat at hwins
  rw [andBool_eq, Bool.and_eq_true] at hwins
  rcases hwins with ⟨hval, hnobad⟩
  obtain ⟨hlen, hlt, hleg⟩ := validStratNat_spec g σ hval
  have hno_bad : ∀ w < g.1 + 1, badVertexNat g v0.val σ w = false := by
    have hfold_iff : ∀ (l : List ℕ) (init : Bool),
        l.foldl (fun ok w => andBool ok (notBool (badVertexNat g v0.val σ w))) init = true ↔
          init = true ∧ ∀ w ∈ l, badVertexNat g v0.val σ w = false := by
      intro l
      induction l with
      | nil => intro init; simp
      | cons x xs ih =>
        intro init
        rw [List.foldl_cons, ih]
        simp only [andBool_eq, notBool_eq, Bool.and_eq_true, Bool.not_eq_true', List.mem_cons]
        constructor
        · rintro ⟨⟨h1, hx⟩, hxs⟩
          refine ⟨h1, fun w hw => ?_⟩
          rcases hw with rfl | hw
          · exact hx
          · exact hxs w hw
        · rintro ⟨h1, hall⟩
          exact ⟨⟨h1, hall x (Or.inl rfl)⟩, fun w hw => hall w (Or.inr hw)⟩
    exact fun w hw => ((hfold_iff (List.range (g.1 + 1)) true).mp hnobad).2 w (List.mem_range.mpr hw)
  refine ⟨hlen, hlt, hleg, ?_⟩
  intro π hπ0 hπ_succ hπ_eve
  have hstep_out : ∀ n : ℕ, (π (n + 1)).val ∈ outStratNat g σ (π n).val := by
    intro n
    unfold outStratNat
    by_cases hown : ownerNat g (π n).val = true
    · rw [if_pos hown, List.mem_singleton, hπ_eve n hown]
      unfold stratToFin
      dsimp only
      exact Nat.mod_eq_of_lt (hlt (π n))
    · rw [if_neg hown, ← mem_succList_iff_mem_succNat]
      exact hπ_succ n
  by_contra hnot_even
  let B := (Finset.univ : Finset (Fin (g.1 + 1))).sup (prio g)
  have hbdd : ∀ n : ℕ, prio g (π n) ≤ B :=
    fun n => Finset.le_sup (f := prio g) (Finset.mem_univ (π n))
  obtain ⟨p, hp_odd, hp_freq, hp_ev⟩ :=
    (oddParityCond_iff_not_parityCond_of_bdd _ B hbdd).mpr hnot_even
  rw [Filter.eventually_atTop] at hp_ev
  obtain ⟨N0, hN0⟩ := hp_ev
  rw [Filter.frequently_atTop] at hp_freq
  let nextIdx : ℕ → ℕ := fun m => (hp_freq m).choose
  have hnextIdx : ∀ m : ℕ, m ≤ nextIdx m ∧ prio g (π (nextIdx m)) = p :=
    fun m => (hp_freq m).choose_spec
  let idx : ℕ → ℕ := fun k => Nat.rec (nextIdx N0) (fun _ prev => nextIdx (prev + 1)) k
  have hidx_ge : ∀ k : ℕ, N0 ≤ idx k ∧ prio g (π (idx k)) = p := by
    intro k
    induction k with
    | zero => exact hnextIdx N0
    | succ k ih =>
      change N0 ≤ nextIdx (idx k + 1) ∧ prio g (π (nextIdx (idx k + 1))) = p
      have hs := hnextIdx (idx k + 1)
      exact ⟨by omega, hs.2⟩
  have hidx_mono : StrictMono idx := by
    apply strictMono_nat_of_lt_succ
    intro k
    have hs := (hnextIdx (idx k + 1)).1
    change idx k < nextIdx (idx k + 1)
    omega
  obtain ⟨ia, ib, hiab, hπ_eq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (g.1 + 2) => π (idx i.val)) (by simp)
  have hval_ne : ia.val ≠ ib.val := fun hv => hiab (Fin.ext hv)
  obtain ⟨n1, n2, hn_N0, hn12, hπ12, hp1⟩ :
      ∃ n1 n2 : ℕ, N0 ≤ n1 ∧ n1 < n2 ∧ π n1 = π n2 ∧ prio g (π n1) = p := by
    rcases lt_or_gt_of_ne hval_ne with hlt_i | hgt_i
    · exact ⟨idx ia.val, idx ib.val, (hidx_ge ia.val).1, hidx_mono hlt_i, hπ_eq, (hidx_ge ia.val).2⟩
    · exact ⟨idx ib.val, idx ia.val, (hidx_ge ib.val).1, hidx_mono hgt_i, hπ_eq.symm, (hidx_ge ib.val).2⟩
  let w := π n1
  have hreach_w : isReachableNat g σ v0.val w.val = true := by
    unfold isReachableNat
    simp only [orBool_eq, Bool.or_eq_true, decide_eq_true_eq, memNat_iff]
    by_cases hn1_zero : n1 = 0
    · left
      subst hn1_zero
      simp [w, hπ0]
    · right
      rw [mem_reachPlusNat_iff]
      refine ⟨n1, fun i => (π i).val, by omega, by simp [hπ0], rfl, ?_⟩
      intro i _
      exact ⟨(π (i + 1)).isLt, Nat.zero_le _, hstep_out i⟩
  have hodd_w : prioNat g w.val % 2 = 1 := by
    have hpw : prioNat g w.val = p := hp1
    rw [hpw]
    rcases hp_odd with ⟨k, rfl⟩
    omega
  have hcyc_w : memNat w.val (reachPlusNat g σ (prioNat g w.val) w.val) = true := by
    rw [memNat_iff, mem_reachPlusNat_iff]
    refine ⟨n2 - n1, fun i => (π (n1 + i)).val, by omega, by simp [w], ?_, ?_⟩
    · dsimp only
      have hadd : n1 + (n2 - n1) = n2 := by omega
      rw [hadd, ← hπ12]
    · intro i _
      dsimp only
      refine ⟨(π (n1 + (i + 1))).isLt, ?_, ?_⟩
      · have hp_eq : prioNat g w.val = p := hp1
        rw [hp_eq]
        exact hN0 (n1 + (i + 1)) (by omega)
      · have hadd : n1 + (i + 1) = (n1 + i) + 1 := by omega
        rw [hadd]
        exact hstep_out (n1 + i)
  have hbad : badVertexNat g v0.val σ w.val = true := by
    unfold badVertexNat
    simp [hreach_w, hodd_w, hcyc_w]
  have hfalse := hno_bad w.val w.isLt
  rw [hbad] at hfalse
  cases hfalse

theorem solvePG_some_sound (g : PGCode) (v0 : Fin (g.1 + 1)) (σ : List ℕ)
    (hsol : solvePG g v0.val = some σ) :
    σ.length = g.1 + 1 ∧
      (∀ v : Fin (g.1 + 1), σ.getD v.val 0 < g.1 + 1) ∧
      (∀ v : Fin (g.1 + 1), owner g v = true → stratToFin g σ v ∈ succList g v) ∧
      (∀ π : ℕ → Fin (g.1 + 1), π 0 = v0 →
        (∀ n : ℕ, π (n + 1) ∈ succList g (π n)) →
        (∀ n : ℕ, owner g (π n) = true → π (n + 1) = stratToFin g σ (π n)) →
        ParityCond (fun n => prio g (π n))) := by
  unfold solvePG at hsol
  dsimp only at hsol
  let M := g.1 + 1
  have hfold_some : ∀ (l : List ℕ) (init : Option (List ℕ)),
      l.foldl
        (fun acc c =>
          match acc with
          | some s => some s
          | none =>
              let σ' := stratOfCode M c
              if winsStratNat g v0.val σ' = true then some σ' else none)
        init = some σ →
      init = some σ ∨ winsStratNat g v0.val σ = true := by
    intro l
    induction l with
    | nil => intro init h; exact Or.inl h
    | cons c cs ih =>
      intro init h
      simp only [List.foldl_cons] at h
      rcases ih _ h with hinit | hwin
      · cases init with
        | some s => exact Or.inl hinit
        | none =>
          dsimp only at hinit
          split_ifs at hinit with hw
          injection hinit with heq
          exact Or.inr (heq ▸ hw)
      · exact Or.inr hwin
  rcases hfold_some (List.range (myPow M M)) none hsol with hnone | hwin
  · cases hnone
  · exact winsStratNat_sound g v0 σ hwin

lemma solvePG_ne_none_of_memless_eve (g : PGCode) (v0 : Fin (g.1 + 1))
    (σFin : Fin (g.1 + 1) → Fin (g.1 + 1))
    (hleg : ∀ v : Fin (g.1 + 1), owner g v = true → σFin v ∈ succList g v)
    (hwin : ∀ π : ℕ → Fin (g.1 + 1), π 0 = v0 →
      (∀ n : ℕ, π (n + 1) ∈ succList g (π n)) →
      (∀ n : ℕ, owner g (π n) = true → π (n + 1) = σFin (π n)) →
      ParityCond (fun n => prio g (π n))) :
    solvePG g v0.val ≠ none := by
  let M := g.1 + 1
  obtain ⟨c, hc_lt, hc_eq⟩ := exists_code_of_finFun (Nat.succ_pos g.1) M σFin
  let σ := stratOfCode M c
  have hget : ∀ v : Fin (g.1 + 1), σ.getD v.val 0 = (σFin v).val := by
    intro v
    rw [stratOfCode_getD M c v.val v.isLt]
    exact hc_eq v
  have hval : validStratNat g σ = true := by
    unfold validStratNat
    rw [andBool_eq, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨stratOfCode_length M c, ?_⟩
    have hfold_true : ∀ (l : List ℕ),
        (∀ v ∈ l, v < M) →
        l.foldl
          (fun ok v =>
            andBool ok
              (andBool (decide (σ.getD v 0 < M))
                (if ownerNat g v = true then memNat (σ.getD v 0) (succNat g v) else true)))
          true = true := by
      intro l hl
      induction l with
      | nil => rfl
      | cons v vs ih =>
        have hv : v < g.1 + 1 := hl v (List.mem_cons.mpr (Or.inl rfl))
        let vf : Fin (g.1 + 1) := ⟨v, hv⟩
        have h1 : decide (σ.getD v 0 < M) = true :=
          decide_eq_true (by rw [hget vf]; exact (σFin vf).isLt)
        have h2 : (if ownerNat g v = true then memNat (σ.getD v 0) (succNat g v) else true) = true := by
          by_cases hown : ownerNat g v = true
          · rw [if_pos hown, memNat_iff, hget vf]
            exact (mem_succList_iff_mem_succNat g vf (σFin vf)).mp (hleg vf hown)
          · rw [if_neg hown]
        rw [List.foldl_cons, h1, h2]
        exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    exact hfold_true (List.range M) (fun _ hv => List.mem_range.mp hv)
  have hwins : winsStratNat g v0.val σ = true := by
    unfold winsStratNat
    rw [andBool_eq, Bool.and_eq_true]
    refine ⟨hval, ?_⟩
    by_contra hnot_all
    have hex_bad : ∃ w < M, badVertexNat g v0.val σ w = true := by
      by_contra hnone_bad
      apply hnot_all
      have hfold_ok : ∀ (l : List ℕ), (∀ w ∈ l, w < M) →
          l.foldl (fun ok w => andBool ok (notBool (badVertexNat g v0.val σ w))) true = true := by
        intro l hl
        induction l with
        | nil => rfl
        | cons w ws ih =>
          have hw : w < M := hl w (List.mem_cons.mpr (Or.inl rfl))
          have hnb : badVertexNat g v0.val σ w = false := by
            cases hb : badVertexNat g v0.val σ w
            · rfl
            · exact False.elim (hnone_bad ⟨w, hw, hb⟩)
          simp only [List.foldl_cons, hnb]
          exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      exact hfold_ok (List.range M) (fun _ hw => List.mem_range.mp hw)
    obtain ⟨w, hw_lt, hbad⟩ := hex_bad
    unfold badVertexNat at hbad
    simp only [andBool_eq, Bool.and_eq_true, decide_eq_true_eq, memNat_iff] at hbad
    rcases hbad with ⟨hreach, hodd_rem, hcyc⟩
    have hstem : ∃ (r : ℕ) (stem : ℕ → Fin (g.1 + 1)),
        stem 0 = v0 ∧ (stem r).val = w ∧
        ∀ i < r, stem (i + 1) ∈ succList g (stem i) ∧
          (owner g (stem i) = true → stem (i + 1) = σFin (stem i)) := by
      unfold isReachableNat at hreach
      simp only [orBool_eq, Bool.or_eq_true, decide_eq_true_eq, memNat_iff] at hreach
      rcases hreach with rfl | hpos
      · exact ⟨0, fun _ => v0, rfl, rfl, fun _ hi => by omega⟩
      · obtain ⟨r, walk, hr1, hw0, hwr, hstep⟩ := (mem_reachPlusNat_iff g σ 0 v0.val w).mp hpos
        let stem : ℕ → Fin (g.1 + 1) := fun i =>
          if hi0 : i = 0 then v0
          else if hi : i ≤ r then
            ⟨walk i, by
              have hlt_step := (hstep (i - 1) (by omega)).1
              rwa [show i - 1 + 1 = i by omega] at hlt_step⟩
          else ⟨w, hw_lt⟩
        have hstem_val : ∀ i ≤ r, (stem i).val = walk i := by
          intro i hi
          by_cases hi0 : i = 0
          · subst hi0; simp [stem, hw0]
          · simp [stem, hi0, hi]
        refine ⟨r, stem, by simp [stem], by rw [hstem_val r le_rfl, hwr], ?_⟩
        intro i hi
        have hout := (hstep i hi).2.2
        rw [← hstem_val i (by omega), ← hstem_val (i + 1) (by omega)] at hout
        unfold outStratNat at hout
        by_cases hown : owner g (stem i) = true
        · have hown_nat : ownerNat g (stem i).val = true := hown
          rw [if_pos hown_nat, List.mem_singleton, hget (stem i)] at hout
          have heq_fin : stem (i + 1) = σFin (stem i) := Fin.ext hout
          exact ⟨heq_fin ▸ hleg (stem i) hown, fun _ => heq_fin⟩
        · have hown_nat : ¬ (ownerNat g (stem i).val = true) := hown
          rw [if_neg hown_nat, ← mem_succList_iff_mem_succNat] at hout
          exact ⟨hout, fun h => False.elim (hown h)⟩
    obtain ⟨r, stem, hstem0, hstemr, hstem_step⟩ := hstem
    let wf : Fin (g.1 + 1) := ⟨w, hw_lt⟩
    obtain ⟨m, cwalk, hm1, hcw0, hcwm, hcw_step⟩ :=
      (mem_reachPlusNat_iff g σ (prioNat g w) w w).mp hcyc
    let cyc : ℕ → Fin (g.1 + 1) := fun j =>
      if hj0 : j = 0 then wf
      else if hj : j ≤ m then
        ⟨cwalk j, by
          have hlt_step := (hcw_step (j - 1) (by omega)).1
          rwa [show j - 1 + 1 = j by omega] at hlt_step⟩
      else wf
    have hcyc_val : ∀ j ≤ m, (cyc j).val = cwalk j := by
      intro j hj
      by_cases hj0 : j = 0
      · subst hj0; simp [cyc, wf, hcw0]
      · simp [cyc, hj0, hj]
    have hcyc0 : cyc 0 = wf := by simp [cyc]
    have hcycm : cyc m = wf := Fin.ext (by rw [hcyc_val m le_rfl, hcwm])
    have hcyc_step : ∀ j < m,
        cyc (j + 1) ∈ succList g (cyc j) ∧
        (owner g (cyc j) = true → cyc (j + 1) = σFin (cyc j)) ∧
        prio g wf ≤ prio g (cyc (j + 1)) := by
      intro j hj
      have hs := hcw_step j hj
      have hp_ge : prio g wf ≤ prio g (cyc (j + 1)) := by
        change prioNat g w ≤ prioNat g (cyc (j + 1)).val
        rw [hcyc_val (j + 1) (by omega)]
        exact hs.2.1
      have hout := hs.2.2
      rw [← hcyc_val j (by omega), ← hcyc_val (j + 1) (by omega)] at hout
      unfold outStratNat at hout
      by_cases hown : owner g (cyc j) = true
      · have hown_nat : ownerNat g (cyc j).val = true := hown
        rw [if_pos hown_nat, List.mem_singleton, hget (cyc j)] at hout
        have heq_fin : cyc (j + 1) = σFin (cyc j) := Fin.ext hout
        exact ⟨heq_fin ▸ hleg (cyc j) hown, fun _ => heq_fin, hp_ge⟩
      · have hown_nat : ¬ (ownerNat g (cyc j).val = true) := hown
        rw [if_neg hown_nat, ← mem_succList_iff_mem_succNat] at hout
        exact ⟨hout, fun h => False.elim (hown h), hp_ge⟩
    let π : ℕ → Fin (g.1 + 1) := fun n =>
      if n < r then stem n else cyc ((n - r) % m)
    have hπ0 : π 0 = v0 := by
      dsimp only [π]
      split_ifs with h0
      · exact hstem0
      · have hr0 : r = 0 := by omega
        subst hr0
        simp [hcyc0, wf, ← hstemr, hstem0]
    have hstemr_eq : stem r = wf := Fin.ext hstemr
    have hπ_step : ∀ n : ℕ, π (n + 1) ∈ succList g (π n) ∧
        (owner g (π n) = true → π (n + 1) = σFin (π n)) := by
      intro n
      by_cases hn1 : n + 1 < r
      · have hn : n < r := by omega
        simp only [π, hn, hn1, ↓reduceIte]
        exact hstem_step n hn
      · by_cases hn : n < r
        · have hnr : n + 1 = r := by omega
          have hπn : π n = stem n := if_pos hn
          have hπn1 : π (n + 1) = stem (n + 1) := by
            dsimp only [π]
            rw [if_neg hn1, hnr, Nat.sub_self, Nat.zero_mod, hcyc0, ← hstemr_eq]
          rw [hπn, hπn1]
          exact hstem_step n hn
        · simp only [π, hn, hn1, ↓reduceIte]
          have hsub : n + 1 - r = (n - r) + 1 := by omega
          rw [hsub]
          let q := (n - r) % m
          have hq_lt : q < m := Nat.mod_lt _ (by omega)
          have hmod_succ : ((n - r) + 1) % m = if q + 1 < m then q + 1 else 0 := by
            have hdiv := Nat.div_add_mod (n - r) m
            by_cases hqm : q + 1 < m
            · rw [if_pos hqm]
              have heq : (n - r) + 1 = (q + 1) + m * ((n - r) / m) := by omega
              rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hqm]
            · rw [if_neg hqm]
              have hqm_eq : q + 1 = m := by omega
              have heq : (n - r) + 1 = m * (((n - r) / m) + 1) := by
                rw [Nat.mul_succ]
                omega
              rw [heq, Nat.mul_mod_right]
          change cyc (((n - r) + 1) % m) ∈ succList g (cyc q) ∧
            (owner g (cyc q) = true → cyc (((n - r) + 1) % m) = σFin (cyc q))
          rw [hmod_succ]
          split_ifs with hqm
          · exact ⟨(hcyc_step q hq_lt).1, (hcyc_step q hq_lt).2.1⟩
          · have hqm_eq : q + 1 = m := by omega
            rw [hcyc0, ← hcycm, ← hqm_eq]
            exact ⟨(hcyc_step q hq_lt).1, (hcyc_step q hq_lt).2.1⟩
    have heven_π := hwin π hπ0 (fun n => (hπ_step n).1) (fun n => (hπ_step n).2)
    have hodd_π : OddParityCond (fun n => prio g (π n)) := by
      refine ⟨prio g wf, ?_, ?_, ?_⟩
      · change Odd (prioNat g w)
        exact Nat.odd_iff.mpr hodd_rem
      · rw [Filter.frequently_atTop]
        intro N
        have hNm : N ≤ N * m := by
          have := Nat.mul_le_mul_left N hm1
          omega
        refine ⟨r + N * m, by omega, ?_⟩
        have hnr : ¬ (r + N * m < r) := by omega
        dsimp only [π]
        rw [if_neg hnr, Nat.add_sub_cancel_left, Nat.mul_mod_left, hcyc0]
      · rw [Filter.eventually_atTop]
        refine ⟨r, fun n hn => ?_⟩
        have hnr : ¬ (n < r) := by omega
        simp only [π, hnr, ↓reduceIte]
        let q := (n - r) % m
        have hq_lt : q < m := Nat.mod_lt _ (by omega)
        by_cases hq0 : q = 0
        · change prio g wf ≤ prio g (cyc q)
          rw [hq0, hcyc0]
        · have hq_pred : (q - 1) + 1 = q := by omega
          change prio g wf ≤ prio g (cyc q)
          rw [← hq_pred]
          exact (hcyc_step (q - 1) (by omega)).2.2
    exact not_parityCond_and_oddParityCond _ ⟨heven_π, hodd_π⟩
  intro hsol_none
  have hc_mem : c ∈ List.range (myPow M M) := by
    rw [List.mem_range, myPow_eq]
    exact hc_lt
  have hfold_ne : ∀ (l : List ℕ) (init : Option (List ℕ)),
      (init.isSome = true ∨ c ∈ l) →
      (l.foldl
        (fun acc x =>
          match acc with
          | some s => some s
          | none =>
              let σ' := stratOfCode M x
              if winsStratNat g v0.val σ' = true then some σ' else none)
        init).isSome = true := by
    intro l
    induction l with
    | nil =>
      intro init h
      rcases h with hs | hm
      · exact hs
      · cases hm
    | cons x xs ih =>
      intro init h
      simp only [List.foldl_cons]
      apply ih
      cases init with
      | some s => exact Or.inl rfl
      | none =>
        rcases h with hs | hm
        · cases hs
        · rw [List.mem_cons] at hm
          rcases hm with rfl | hxs
          · left
            change (if winsStratNat g v0.val σ = true then some σ else none).isSome = true
            rw [if_pos hwins]
            rfl
          · exact Or.inr hxs
  have hisSome : (solvePG g v0.val).isSome = true :=
    hfold_ne (List.range (myPow M M)) none (Or.inr hc_mem)
  rw [hsol_none] at hisSome
  cases hisSome

/-! ### Section 4: McNaughton–Zielonka Memoryless Determinacy & Adam Counterstrategy -/

def PlayerWins (g : PGCode) (player : Bool) (π : ℕ → Fin (g.1 + 1)) : Prop :=
  if player = true then ParityCond (fun n => prio g (π n))
  else OddParityCond (fun n => prio g (π n))

def PrioFavors (player : Bool) (p : ℕ) : Prop :=
  if player = true then Even p else Odd p

lemma playerWins_shift (g : PGCode) (player : Bool) (π : ℕ → Fin (g.1 + 1)) (d : ℕ) :
    PlayerWins g player π ↔ PlayerWins g player (fun n => π (d + n)) := by
  unfold PlayerWins
  cases player <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact oddParityCond_shift _ d
  · exact parityCond_shift _ d

lemma playerWins_of_min_freq (g : PGCode) (player : Bool) (p : ℕ)
    (hfav : PrioFavors player p) (π : ℕ → Fin (g.1 + 1))
    (hfreq : ∃ᶠ n in Filter.atTop, prio g (π n) = p)
    (hev : ∀ᶠ n in Filter.atTop, p ≤ prio g (π n)) :
    PlayerWins g player π := by
  cases player
  · exact ⟨p, hfav, hfreq, hev⟩
  · exact ⟨p, hfav, hfreq, hev⟩

def IsSubgame (g : PGCode) (S : Finset (Fin (g.1 + 1))) : Prop :=
  ∀ v ∈ S, ∃ u ∈ S, u ∈ succList g v

lemma isSubgame_univ (g : PGCode) : IsSubgame g Finset.univ := by
  intro v _
  obtain ⟨u, hu⟩ := succList_nonempty g v
  exact ⟨u, Finset.mem_univ u, hu⟩

structure WinsIn (g : PGCode) (S : Finset (Fin (g.1 + 1))) (player : Bool)
    (W : Finset (Fin (g.1 + 1))) (σ : Fin (g.1 + 1) → Fin (g.1 + 1)) : Prop where
  sub : W ⊆ S
  own_step : ∀ v ∈ W, owner g v = player → σ v ∈ succList g v ∧ σ v ∈ W
  opp_step : ∀ v ∈ W, owner g v ≠ player → ∀ u ∈ succList g v, u ∈ S → u ∈ W
  wins : ∀ π : ℕ → Fin (g.1 + 1), π 0 ∈ W →
    (∀ n : ℕ, π (n + 1) ∈ succList g (π n) ∧ π (n + 1) ∈ S) →
    (∀ n : ℕ, owner g (π n) = player → π (n + 1) = σ (π n)) →
    PlayerWins g player π

def CanForce (g : PGCode) (S : Finset (Fin (g.1 + 1))) (player : Bool)
    (A : Finset (Fin (g.1 + 1))) (v : Fin (g.1 + 1)) : Prop :=
  if owner g v = player then ∃ u ∈ succList g v, u ∈ S ∧ u ∈ A
  else ∀ u ∈ succList g v, u ∈ S → u ∈ A

noncomputable def attrStep (g : PGCode) (S : Finset (Fin (g.1 + 1))) (player : Bool)
    (A : Finset (Fin (g.1 + 1))) : Finset (Fin (g.1 + 1)) := by
  classical
  exact A ∪ S.filter (CanForce g S player A)

noncomputable def attrIter (g : PGCode) (S : Finset (Fin (g.1 + 1))) (player : Bool)
    (U : Finset (Fin (g.1 + 1))) : ℕ → Finset (Fin (g.1 + 1))
  | 0 => U
  | k + 1 => attrStep g S player (attrIter g S player U k)

noncomputable def attr (g : PGCode) (S : Finset (Fin (g.1 + 1))) (player : Bool)
    (U : Finset (Fin (g.1 + 1))) : Finset (Fin (g.1 + 1)) :=
  attrIter g S player U (S.card + 1)

lemma attrIter_sub (g : PGCode) (S : Finset (Fin (g.1 + 1))) (player : Bool)
    (U : Finset (Fin (g.1 + 1))) (hU : U ⊆ S) :
    ∀ k : ℕ, U ⊆ attrIter g S player U k ∧ attrIter g S player U k ⊆ S
  | 0 => ⟨Finset.Subset.refl U, hU⟩
  | k + 1 => by
      classical
      obtain ⟨ih1, ih2⟩ := attrIter_sub g S player U hU k
      refine ⟨ih1.trans Finset.subset_union_left, ?_⟩
      unfold attrIter attrStep
      exact Finset.union_subset ih2 (Finset.filter_subset _ S)

lemma attrIter_mono_succ (g : PGCode) (S : Finset (Fin (g.1 + 1))) (player : Bool)
    (U : Finset (Fin (g.1 + 1))) (k : ℕ) :
    attrIter g S player U k ⊆ attrIter g S player U (k + 1) := by
  classical
  exact Finset.subset_union_left

lemma attrIter_mono (g : PGCode) (S : Finset (Fin (g.1 + 1))) (player : Bool)
    (U : Finset (Fin (g.1 + 1))) : Monotone (attrIter g S player U) :=
  monotone_nat_of_le_succ (attrIter_mono_succ g S player U)

lemma attr_sub (g : PGCode) (S : Finset (Fin (g.1 + 1))) (player : Bool)
    (U : Finset (Fin (g.1 + 1))) (hU : U ⊆ S) :
    U ⊆ attr g S player U ∧ attr g S player U ⊆ S :=
  attrIter_sub g S player U hU (S.card + 1)

lemma attr_fixed (g : PGCode) (S : Finset (Fin (g.1 + 1))) (player : Bool)
    (U : Finset (Fin (g.1 + 1))) (hU : U ⊆ S) :
    attrStep g S player (attr g S player U) = attr g S player U := by
  classical
  have hstay_of_eq : ∀ {j : ℕ}, attrIter g S player U j = attrIter g S player U (j + 1) →
      ∀ d : ℕ, attrIter g S player U (j + d) = attrIter g S player U j := by
    intro j hj d
    induction d with
    | zero => rfl
    | succ d ih =>
      have hsucc : j + (d + 1) = (j + d) + 1 := by omega
      rw [hsucc]
      change attrStep g S player (attrIter g S player U (j + d)) = attrIter g S player U j
      rw [ih]
      exact hj.symm
  have hex_eq : ∃ j ≤ S.card, attrIter g S player U j = attrIter g S player U (j + 1) := by
    by_contra hall_ne
    have hlt_step : ∀ j ≤ S.card,
        (attrIter g S player U j).card < (attrIter g S player U (j + 1)).card := by
      intro j hj
      have hsub := attrIter_mono_succ g S player U j
      have hne : attrIter g S player U j ≠ attrIter g S player U (j + 1) :=
        fun heq => hall_ne ⟨j, hj, heq⟩
      exact Finset.card_lt_card (lt_of_le_of_ne hsub hne)
    have hcard_ge : ∀ j ≤ S.card + 1, j ≤ (attrIter g S player U j).card := by
      intro j hj
      induction j with
      | zero => omega
      | succ j ih =>
        have hprev := ih (by omega)
        have hgrow := hlt_step j (by omega)
        omega
    have htop := hcard_ge (S.card + 1) le_rfl
    have hle_S := Finset.card_le_card (attrIter_sub g S player U hU (S.card + 1)).2
    omega
  obtain ⟨j, hj, heq⟩ := hex_eq
  have h1 := hstay_of_eq heq (S.card + 1 - j)
  have h2 := hstay_of_eq heq (S.card + 2 - j)
  have e1 : j + (S.card + 1 - j) = S.card + 1 := by omega
  have e2 : j + (S.card + 2 - j) = S.card + 2 := by omega
  rw [e1] at h1
  rw [e2] at h2
  change attrIter g S player U (S.card + 2) = attrIter g S player U (S.card + 1)
  exact h2.trans h1.symm

lemma not_canForce_of_sdiff_attr (g : PGCode) (S : Finset (Fin (g.1 + 1))) (player : Bool)
    (U : Finset (Fin (g.1 + 1))) (hU : U ⊆ S) {v : Fin (g.1 + 1)}
    (hv : v ∈ S \ attr g S player U) :
    ¬ CanForce g S player (attr g S player U) v := by
  classical
  rw [Finset.mem_sdiff] at hv
  intro hcf
  have hmem : v ∈ attrStep g S player (attr g S player U) := by
    unfold attrStep
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv.1, hcf⟩)
  rw [attr_fixed g S player U hU] at hmem
  exact hv.2 hmem

lemma isSubgame_sdiff_attr (g : PGCode) (S : Finset (Fin (g.1 + 1))) (player : Bool)
    (U : Finset (Fin (g.1 + 1))) (hSub : IsSubgame g S) (hU : U ⊆ S) :
    IsSubgame g (S \ attr g S player U) := by
  classical
  intro v hv
  have hncf := not_canForce_of_sdiff_attr g S player U hU hv
  rw [Finset.mem_sdiff] at hv
  unfold CanForce at hncf
  by_cases hown : owner g v = player
  · rw [if_pos hown] at hncf
    obtain ⟨u, huS, hu_succ⟩ := hSub v hv.1
    refine ⟨u, Finset.mem_sdiff.mpr ⟨huS, ?_⟩, hu_succ⟩
    intro huA
    exact hncf ⟨u, hu_succ, huS, huA⟩
  · rw [if_neg hown] at hncf
    by_contra hno
    apply hncf
    intro u hu_succ huS
    by_contra hu_notA
    exact hno ⟨u, Finset.mem_sdiff.mpr ⟨huS, hu_notA⟩, hu_succ⟩

noncomputable def attrStrat (g : PGCode) (S : Finset (Fin (g.1 + 1))) (player : Bool)
    (U : Finset (Fin (g.1 + 1))) (v : Fin (g.1 + 1)) : Fin (g.1 + 1) := by
  classical
  exact if hv : (∃ k : ℕ, v ∈ attrIter g S player U (k + 1)) ∧ v ∉ U ∧ owner g v = player then
    let k := Nat.find hv.1
    have hk_mem : v ∈ attrStep g S player (attrIter g S player U k) := Nat.find_spec hv.1
    have hnot_k : v ∉ attrIter g S player U k := by
      cases hk_eq : k with
      | zero => exact hv.2.1
      | succ k' =>
        have hk'_lt : k' < k := by omega
        exact Nat.find_min hv.1 hk'_lt
    have hcf : CanForce g S player (attrIter g S player U k) v := by
      unfold attrStep at hk_mem
      rcases Finset.mem_union.mp hk_mem with hk | hfilt
      · exact False.elim (hnot_k hk)
      · exact (Finset.mem_filter.mp hfilt).2
    have hex_u : ∃ u ∈ succList g v, u ∈ S ∧ u ∈ attrIter g S player U k := by
      unfold CanForce at hcf
      rwa [if_pos hv.2.2] at hcf
    hex_u.choose
  else (succList g v).head (succList_ne_nil g v)

lemma attrStrat_step_layer (g : PGCode) (S : Finset (Fin (g.1 + 1))) (player : Bool)
    (U : Finset (Fin (g.1 + 1))) {v : Fin (g.1 + 1)} {m : ℕ}
    (hvm : v ∈ attrIter g S player U (m + 1)) (hvU : v ∉ U) :
    ∃ k ≤ m,
      (owner g v = player →
        attrStrat g S player U v ∈ succList g v ∧
        attrStrat g S player U v ∈ S ∧
        attrStrat g S player U v ∈ attrIter g S player U k) ∧
      (owner g v ≠ player →
        ∀ u ∈ succList g v, u ∈ S → u ∈ attrIter g S player U k) := by
  classical
  have hex : ∃ k : ℕ, v ∈ attrIter g S player U (k + 1) := ⟨m, hvm⟩
  let k := Nat.find hex
  have hk_le : k ≤ m := Nat.find_min' hex hvm
  have hk_mem : v ∈ attrStep g S player (attrIter g S player U k) := Nat.find_spec hex
  have hnot_k : v ∉ attrIter g S player U k := by
    cases hk_eq : k with
    | zero => exact hvU
    | succ k' =>
      have hk'_lt : k' < k := by omega
      exact Nat.find_min hex hk'_lt
  have hcf : CanForce g S player (attrIter g S player U k) v := by
    unfold attrStep at hk_mem
    rcases Finset.mem_union.mp hk_mem with hk | hfilt
    · exact False.elim (hnot_k hk)
    · exact (Finset.mem_filter.mp hfilt).2
  refine ⟨k, hk_le, ?_, ?_⟩
  · intro hown
    have hcond : (∃ k : ℕ, v ∈ attrIter g S player U (k + 1)) ∧ v ∉ U ∧ owner g v = player :=
      ⟨hex, hvU, hown⟩
    unfold attrStrat
    rw [dif_pos hcond]
    unfold CanForce at hcf
    rw [if_pos hown] at hcf
    exact hcf.choose_spec
  · intro hown
    unfold CanForce at hcf
    rw [if_neg hown] at hcf
    exact hcf

lemma attrStrat_hits_aux (g : PGCode) (S : Finset (Fin (g.1 + 1))) (player : Bool)
    (U : Finset (Fin (g.1 + 1))) :
    ∀ (m : ℕ), m ≤ S.card + 1 →
      ∀ (π : ℕ → Fin (g.1 + 1)),
        π 0 ∈ attrIter g S player U m →
        (∀ n : ℕ, π (n + 1) ∈ succList g (π n) ∧ π (n + 1) ∈ S) →
        (∀ n : ℕ, π n ∈ attr g S player U → π n ∉ U →
          owner g (π n) = player → π (n + 1) = attrStrat g S player U (π n)) →
        ∃ t : ℕ, π t ∈ U := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm π h0 hsucc hcon
    by_cases h0U : π 0 ∈ U
    · exact ⟨0, h0U⟩
    · cases m with
      | zero => exact False.elim (h0U h0)
      | succ m' =>
        have h0A : π 0 ∈ attr g S player U := attrIter_mono g S player U hm h0
        obtain ⟨k, hk_le, hown_k, hopp_k⟩ := attrStrat_step_layer g S player U h0 h0U
        have h1_mem : π 1 ∈ attrIter g S player U k := by
          by_cases hown : owner g (π 0) = player
          · rw [hcon 0 h0A h0U hown]
            exact (hown_k hown).2.2
          · exact hopp_k hown (π 1) (hsucc 0).1 (hsucc 0).2
        obtain ⟨t, ht⟩ := ih k (Nat.lt_succ_of_le hk_le) (by omega) (fun n => π (1 + n)) h1_mem
          (fun n => by simpa [Nat.add_assoc] using hsucc (1 + n))
          (fun n hnA hnU hown => by simpa [Nat.add_assoc] using hcon (1 + n) hnA hnU hown)
        exact ⟨1 + t, ht⟩

lemma attrStrat_hits (g : PGCode) (S : Finset (Fin (g.1 + 1))) (player : Bool)
    (U : Finset (Fin (g.1 + 1))) (π : ℕ → Fin (g.1 + 1))
    (h0 : π 0 ∈ attr g S player U)
    (hsucc : ∀ n : ℕ, π (n + 1) ∈ succList g (π n) ∧ π (n + 1) ∈ S)
    (hcon : ∀ n : ℕ, π n ∈ attr g S player U → π n ∉ U →
      owner g (π n) = player → π (n + 1) = attrStrat g S player U (π n)) :
    ∃ t : ℕ, π t ∈ U :=
  attrStrat_hits_aux g S player U (S.card + 1) le_rfl π h0 hsucc hcon

lemma zielonka_step (g : PGCode) (S : Finset (Fin (g.1 + 1)))
    (hSub : IsSubgame g S) (hS : S.Nonempty) (player : Bool)
    (hfav : PrioFavors player (S.inf' hS (prio g)))
    (ih : ∀ T : Finset (Fin (g.1 + 1)), T.card < S.card → IsSubgame g T →
      ∃ (W_pl W_opp : Finset (Fin (g.1 + 1)))
        (σ_pl σ_opp : Fin (g.1 + 1) → Fin (g.1 + 1)),
        W_pl ∪ W_opp = T ∧ Disjoint W_pl W_opp ∧
        WinsIn g T player W_pl σ_pl ∧ WinsIn g T (!player) W_opp σ_opp) :
    ∃ (W_pl W_opp : Finset (Fin (g.1 + 1)))
      (σ_pl σ_opp : Fin (g.1 + 1) → Fin (g.1 + 1)),
      W_pl ∪ W_opp = S ∧ Disjoint W_pl W_opp ∧
      WinsIn g S player W_pl σ_pl ∧ WinsIn g S (!player) W_opp σ_opp := by
  classical
  let p := S.inf' hS (prio g)
  let opp := !player
  let U := S.filter fun v => prio g v = p
  have hU_sub : U ⊆ S := Finset.filter_subset _ S
  have hU_ne : U.Nonempty := by
    obtain ⟨v, hvS, hvp⟩ := Finset.exists_mem_eq_inf' hS (prio g)
    exact ⟨v, Finset.mem_filter.mpr ⟨hvS, hvp.symm⟩⟩
  let A := attr g S player U
  have hUA : U ⊆ A := (attr_sub g S player U hU_sub).1
  have hAS : A ⊆ S := (attr_sub g S player U hU_sub).2
  have hA_ne : A.Nonempty := hU_ne.mono hUA
  let S' := S \ A
  have hS'_lt : S'.card < S.card := by
    dsimp only [S']
    have hpos : 0 < A.card := Finset.card_pos.mpr hA_ne
    have hadd := Finset.card_sdiff_add_card_eq_card hAS
    omega
  have hS'_sub : IsSubgame g S' := isSubgame_sdiff_attr g S player U hSub hU_sub
  obtain ⟨W'_pl, W'_opp, σ'_pl, σ'_opp, hpart', hdisj', hW'_pl, hW'_opp⟩ :=
    ih S' hS'_lt hS'_sub
  by_cases hW'_empty : W'_opp = ∅
  · have hW'_eq : W'_pl = S' := by simpa [hW'_empty] using hpart'
    let σ_pl : Fin (g.1 + 1) → Fin (g.1 + 1) := fun v =>
      if v ∈ S' then σ'_pl v
      else if hvU : v ∈ U then (hSub v (hU_sub hvU)).choose
      else attrStrat g S player U v
    refine ⟨S, ∅, σ_pl, fun v => v, by simp, Finset.disjoint_empty_right S, ?_, ?_⟩
    · refine ⟨Finset.Subset.refl S, ?_, ?_, ?_⟩
      · intro v hvS hown
        dsimp only [σ_pl]
        by_cases hvS' : v ∈ S'
        · rw [if_pos hvS']
          have hvW : v ∈ W'_pl := hW'_eq.symm ▸ hvS'
          have hs := hW'_pl.own_step v hvW hown
          exact ⟨hs.1, Finset.sdiff_subset (hW'_pl.sub hs.2)⟩
        · rw [if_neg hvS']
          by_cases hvU : v ∈ U
          · rw [dif_pos hvU]
            have hch := (hSub v (hU_sub hvU)).choose_spec
            exact ⟨hch.2, hch.1⟩
          · rw [dif_neg hvU]
            have hvA : v ∈ A := by
              by_contra hnA
              exact hvS' (Finset.mem_sdiff.mpr ⟨hvS, hnA⟩)
            obtain ⟨k, _, hown_k, _⟩ := attrStrat_step_layer g S player U hvA hvU
            exact ⟨(hown_k hown).1, (hown_k hown).2.1⟩
      · intro _ _ _ _ _ huS
        exact huS
      · intro π hπ0 hπ_succ hπ_con
        have hπS : ∀ n : ℕ, π n ∈ S := by
          intro n
          induction n with
          | zero => exact hπ0
          | succ n _ => exact (hπ_succ n).2
        by_cases hfreqA : ∃ᶠ n in Filter.atTop, π n ∈ A
        · have hfreqU : ∃ᶠ n in Filter.atTop, π n ∈ U := by
            rw [Filter.frequently_atTop] at hfreqA ⊢
            intro N
            obtain ⟨n, hn, hπnA⟩ := hfreqA N
            obtain ⟨t, htU⟩ := attrStrat_hits g S player U (fun k => π (n + k))
              (by simpa using hπnA)
              (fun k => by simpa [Nat.add_assoc] using hπ_succ (n + k))
              (by
                intro k hkA hkU hown
                have hnotS' : π (n + k) ∉ S' := fun hs => (Finset.mem_sdiff.mp hs).2 hkA
                have hstep := hπ_con (n + k) hown
                dsimp only [σ_pl] at hstep
                rw [if_neg hnotS', dif_neg hkU] at hstep
                simpa [Nat.add_assoc] using hstep)
            exact ⟨n + t, by omega, htU⟩
          have hfreq_p : ∃ᶠ n in Filter.atTop, prio g (π n) = p :=
            hfreqU.mono fun n hnU => (Finset.mem_filter.mp hnU).2
          have hev_p : ∀ᶠ n in Filter.atTop, p ≤ prio g (π n) :=
            Filter.Eventually.of_forall fun n => Finset.inf'_le (prio g) (hπS n)
          exact playerWins_of_min_freq g player p hfav π hfreq_p hev_p
        · have hev_notA : ∃ N : ℕ, ∀ k : ℕ, π (N + k) ∉ A := by
            rw [Filter.frequently_atTop] at hfreqA
            by_contra hnoN
            apply hfreqA
            intro N
            by_contra hno_n
            exact hnoN ⟨N, fun k hkA => hno_n ⟨N + k, by omega, hkA⟩⟩
          obtain ⟨N, hN⟩ := hev_notA
          have hstay_S' : ∀ k : ℕ, π (N + k) ∈ S' :=
            fun k => Finset.mem_sdiff.mpr ⟨hπS (N + k), hN k⟩
          have hwin_suf := hW'_pl.wins (fun k => π (N + k))
            (by rw [hW'_eq]; simpa using hstay_S' 0)
            (fun k => ⟨by simpa [Nat.add_assoc] using (hπ_succ (N + k)).1,
                       by simpa [Nat.add_assoc] using hstay_S' (k + 1)⟩)
            (fun k hown => by
              have hstep := hπ_con (N + k) hown
              dsimp only [σ_pl] at hstep
              rw [if_pos (hstay_S' k)] at hstep
              simpa [Nat.add_assoc] using hstep)
          exact (playerWins_shift g player π N).mpr hwin_suf
    · exact ⟨Finset.empty_subset S,
             fun _ hv => False.elim (Finset.notMem_empty _ hv),
             fun _ hv => False.elim (Finset.notMem_empty _ hv),
             fun _ hv => False.elim (Finset.notMem_empty _ hv)⟩
  · have hW'_ne : W'_opp.Nonempty := Finset.nonempty_iff_ne_empty.mpr hW'_empty
    have hW'_subS : W'_opp ⊆ S := hW'_opp.sub.trans Finset.sdiff_subset
    let B := attr g S opp W'_opp
    have hWB : W'_opp ⊆ B := (attr_sub g S opp W'_opp hW'_subS).1
    have hBS : B ⊆ S := (attr_sub g S opp W'_opp hW'_subS).2
    have hB_ne : B.Nonempty := hW'_ne.mono hWB
    let σ_B : Fin (g.1 + 1) → Fin (g.1 + 1) := fun v =>
      if v ∈ W'_opp then σ'_opp v else attrStrat g S opp W'_opp v
    have hW'_opp_trap : ∀ v ∈ W'_opp, owner g v ≠ opp → ∀ u ∈ succList g v, u ∈ S → u ∈ W'_opp := by
      intro v hvW hown u hu_succ huS
      have hvS' : v ∈ S \ A := hW'_opp.sub hvW
      have hown_pl : owner g v = player := by
        cases h1 : owner g v <;> cases h2 : player <;> simp_all [opp]
      have hu_notA : u ∉ A := by
        intro huA
        have hncf := not_canForce_of_sdiff_attr g S player U hU_sub hvS'
        unfold CanForce at hncf
        rw [if_pos hown_pl] at hncf
        exact hncf ⟨u, hu_succ, huS, huA⟩
      exact hW'_opp.opp_step v hvW hown u hu_succ (Finset.mem_sdiff.mpr ⟨huS, hu_notA⟩)
    have hWinsB : WinsIn g S opp B σ_B := by
      refine ⟨hBS, ?_, ?_, ?_⟩
      · intro v hvB hown
        dsimp only [σ_B]
        by_cases hvW : v ∈ W'_opp
        · rw [if_pos hvW]
          have hs := hW'_opp.own_step v hvW hown
          exact ⟨hs.1, hWB hs.2⟩
        · rw [if_neg hvW]
          obtain ⟨k, hk_le, hown_k, _⟩ := attrStrat_step_layer g S opp W'_opp hvB hvW
          exact ⟨(hown_k hown).1,
                 attrIter_mono g S opp W'_opp (Nat.le_succ_of_le hk_le) (hown_k hown).2.2⟩
      · intro v hvB hown u hu_succ huS
        by_cases hvW : v ∈ W'_opp
        · exact hWB (hW'_opp_trap v hvW hown u hu_succ huS)
        · obtain ⟨k, hk_le, _, hopp_k⟩ := attrStrat_step_layer g S opp W'_opp hvB hvW
          exact attrIter_mono g S opp W'_opp (Nat.le_succ_of_le hk_le) (hopp_k hown u hu_succ huS)
      · intro π hπ0 hπ_succ hπ_con
        obtain ⟨t, htW⟩ := attrStrat_hits g S opp W'_opp π hπ0 hπ_succ
          (fun n _ hnW hown => by
            have hstep := hπ_con n hown
            dsimp only [σ_B] at hstep
            rwa [if_neg hnW] at hstep)
        have hstay_W : ∀ k : ℕ, π (t + k) ∈ W'_opp := by
          intro k
          induction k with
          | zero => simpa using htW
          | succ k ih_k =>
            have hstep_eq : t + (k + 1) = (t + k) + 1 := by omega
            rw [hstep_eq]
            by_cases hown : owner g (π (t + k)) = opp
            · rw [hπ_con (t + k) hown]
              dsimp only [σ_B]
              rw [if_pos ih_k]
              exact (hW'_opp.own_step _ ih_k hown).2
            · exact hW'_opp_trap _ ih_k hown _ (hπ_succ (t + k)).1 (hπ_succ (t + k)).2
        have hwin_suf := hW'_opp.wins (fun k => π (t + k))
          (by simpa using hstay_W 0)
          (fun k => ⟨by simpa [Nat.add_assoc] using (hπ_succ (t + k)).1,
                     hW'_opp.sub (hstay_W (k + 1))⟩)
          (fun k hown => by
            have hstep := hπ_con (t + k) hown
            dsimp only [σ_B] at hstep
            rw [if_pos (hstay_W k)] at hstep
            simpa [Nat.add_assoc] using hstep)
        exact (playerWins_shift g opp π t).mpr hwin_suf
    let S'' := S \ B
    have hS''_lt : S''.card < S.card := by
      dsimp only [S'']
      have hpos : 0 < B.card := Finset.card_pos.mpr hB_ne
      have hadd := Finset.card_sdiff_add_card_eq_card hBS
      omega
    have hS''_sub : IsSubgame g S'' := isSubgame_sdiff_attr g S opp W'_opp hSub hW'_subS
    obtain ⟨W''_pl, W''_opp, σ''_pl, σ''_opp, hpart'', hdisj'', hW''_pl, hW''_opp⟩ :=
      ih S'' hS''_lt hS''_sub
    let W_pl := W''_pl
    let W_opp := W''_opp ∪ B
    let σ_opp : Fin (g.1 + 1) → Fin (g.1 + 1) := fun v =>
      if v ∈ B then σ_B v else σ''_opp v
    have hpart_S : W_pl ∪ W_opp = S := by
      change W''_pl ∪ (W''_opp ∪ B) = S
      rw [← Finset.union_assoc, hpart'']
      exact Finset.sdiff_union_of_subset hBS
    have hdisj_S : Disjoint W_pl W_opp := by
      rw [Finset.disjoint_union_right]
      refine ⟨hdisj'', ?_⟩
      exact Finset.disjoint_left.mpr fun v hvW hvB => (Finset.mem_sdiff.mp (hW''_pl.sub hvW)).2 hvB
    refine ⟨W_pl, W_opp, σ''_pl, σ_opp, hpart_S, hdisj_S, ?_, ?_⟩
    · have hpl_trap : ∀ v ∈ W''_pl, owner g v ≠ player → ∀ u ∈ succList g v, u ∈ S → u ∈ W''_pl := by
        intro v hvW hown u hu_succ huS
        have hvS'' : v ∈ S \ B := hW''_pl.sub hvW
        have hown_opp : owner g v = opp := by
          cases h1 : owner g v <;> cases h2 : player <;> simp_all [opp]
        have hu_notB : u ∉ B := by
          intro huB
          have hncf := not_canForce_of_sdiff_attr g S opp W'_opp hW'_subS hvS''
          unfold CanForce at hncf
          rw [if_pos hown_opp] at hncf
          exact hncf ⟨u, hu_succ, huS, huB⟩
        exact hW''_pl.opp_step v hvW hown u hu_succ (Finset.mem_sdiff.mpr ⟨huS, hu_notB⟩)
      refine ⟨hW''_pl.sub.trans Finset.sdiff_subset, hW''_pl.own_step, hpl_trap, ?_⟩
      intro π hπ0 hπ_succ hπ_con
      have hstay : ∀ n : ℕ, π n ∈ W''_pl := by
        intro n
        induction n with
        | zero => exact hπ0
        | succ n ih_n =>
          by_cases hown : owner g (π n) = player
          · rw [hπ_con n hown]
            exact (hW''_pl.own_step _ ih_n hown).2
          · exact hpl_trap _ ih_n hown _ (hπ_succ n).1 (hπ_succ n).2
      exact hW''_pl.wins π hπ0 (fun n => ⟨(hπ_succ n).1, hW''_pl.sub (hstay (n + 1))⟩) hπ_con
    · refine ⟨Finset.union_subset (hW''_opp.sub.trans Finset.sdiff_subset) hBS, ?_, ?_, ?_⟩
      · intro v hv hown
        dsimp only [σ_opp]
        by_cases hvB : v ∈ B
        · rw [if_pos hvB]
          have hs := hWinsB.own_step v hvB hown
          exact ⟨hs.1, Finset.mem_union_right _ hs.2⟩
        · rw [if_neg hvB]
          have hvW : v ∈ W''_opp := by
            rcases Finset.mem_union.mp hv with hw | hb
            · exact hw
            · exact False.elim (hvB hb)
          have hs := hW''_opp.own_step v hvW hown
          exact ⟨hs.1, Finset.mem_union_left _ hs.2⟩
      · intro v hv hown u hu_succ huS
        by_cases hvB : v ∈ B
        · exact Finset.mem_union_right _ (hWinsB.opp_step v hvB hown u hu_succ huS)
        · have hvW : v ∈ W''_opp := by
            rcases Finset.mem_union.mp hv with hw | hb
            · exact hw
            · exact False.elim (hvB hb)
          by_cases huB : u ∈ B
          · exact Finset.mem_union_right _ huB
          · exact Finset.mem_union_left _
              (hW''_opp.opp_step v hvW hown u hu_succ (Finset.mem_sdiff.mpr ⟨huS, huB⟩))
      · intro π hπ0 hπ_succ hπ_con
        have hstay_union : ∀ n : ℕ, π n ∈ W''_opp ∪ B := by
          intro n
          induction n with
          | zero => exact hπ0
          | succ n ih_n =>
            by_cases hown : owner g (π n) = opp
            · rw [hπ_con n hown]
              dsimp only [σ_opp]
              by_cases hnB : π n ∈ B
              · rw [if_pos hnB]
                exact Finset.mem_union_right _ (hWinsB.own_step _ hnB hown).2
              · rw [if_neg hnB]
                have hnW : π n ∈ W''_opp := by
                  rcases Finset.mem_union.mp ih_n with hw | hb
                  · exact hw
                  · exact False.elim (hnB hb)
                exact Finset.mem_union_left _ (hW''_opp.own_step _ hnW hown).2
            · by_cases hnB : π n ∈ B
              · exact Finset.mem_union_right _
                  (hWinsB.opp_step _ hnB hown _ (hπ_succ n).1 (hπ_succ n).2)
              · have hnW : π n ∈ W''_opp := by
                  rcases Finset.mem_union.mp ih_n with hw | hb
                  · exact hw
                  · exact False.elim (hnB hb)
                by_cases huB : π (n + 1) ∈ B
                · exact Finset.mem_union_right _ huB
                · exact Finset.mem_union_left _
                    (hW''_opp.opp_step _ hnW hown _ (hπ_succ n).1
                      (Finset.mem_sdiff.mpr ⟨(hπ_succ n).2, huB⟩))
        by_cases hhitB : ∃ N : ℕ, π N ∈ B
        · obtain ⟨N, hNB⟩ := hhitB
          have hstay_B : ∀ k : ℕ, π (N + k) ∈ B := by
            intro k
            induction k with
            | zero => simpa using hNB
            | succ k ih_k =>
              have hstep_eq : N + (k + 1) = (N + k) + 1 := by omega
              rw [hstep_eq]
              by_cases hown : owner g (π (N + k)) = opp
              · rw [hπ_con (N + k) hown]
                dsimp only [σ_opp]
                rw [if_pos ih_k]
                exact (hWinsB.own_step _ ih_k hown).2
              · exact hWinsB.opp_step _ ih_k hown _ (hπ_succ (N + k)).1 (hπ_succ (N + k)).2
          have hwin_suf := hWinsB.wins (fun k => π (N + k))
            (by simpa using hNB)
            (fun k => by simpa [Nat.add_assoc] using hπ_succ (N + k))
            (fun k hown => by
              have hstep := hπ_con (N + k) hown
              dsimp only [σ_opp] at hstep
              rw [if_pos (hstay_B k)] at hstep
              simpa [Nat.add_assoc] using hstep)
          exact (playerWins_shift g opp π N).mpr hwin_suf
        · have hnever_B : ∀ n : ℕ, π n ∉ B := fun n hnB => hhitB ⟨n, hnB⟩
          have hstay_W'' : ∀ n : ℕ, π n ∈ W''_opp := by
            intro n
            rcases Finset.mem_union.mp (hstay_union n) with hw | hb
            · exact hw
            · exact False.elim (hnever_B n hb)
          exact hW''_opp.wins π (hstay_W'' 0)
            (fun n => ⟨(hπ_succ n).1, hW''_opp.sub (hstay_W'' (n + 1))⟩)
            (fun n hown => by
              have hstep := hπ_con n hown
              dsimp only [σ_opp] at hstep
              rwa [if_neg (hnever_B n)] at hstep)

theorem zielonka (g : PGCode) (S : Finset (Fin (g.1 + 1))) (hSub : IsSubgame g S) :
    ∃ (W_true W_false : Finset (Fin (g.1 + 1)))
      (σ_true σ_false : Fin (g.1 + 1) → Fin (g.1 + 1)),
      W_true ∪ W_false = S ∧ Disjoint W_true W_false ∧
      WinsIn g S true W_true σ_true ∧ WinsIn g S false W_false σ_false := by
  classical
  suffices ∀ (n : ℕ) (T : Finset (Fin (g.1 + 1))), T.card = n → IsSubgame g T →
      ∃ (W_true W_false : Finset (Fin (g.1 + 1)))
        (σ_true σ_false : Fin (g.1 + 1) → Fin (g.1 + 1)),
        W_true ∪ W_false = T ∧ Disjoint W_true W_false ∧
        WinsIn g T true W_true σ_true ∧ WinsIn g T false W_false σ_false from
    this S.card S rfl hSub
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro T hcard hSubT
    by_cases hT : T.Nonempty
    · let p := T.inf' hT (prio g)
      rcases Nat.even_or_odd p with heven | hodd
      · apply zielonka_step g T hSubT hT true heven
        intro U hU_lt hSubU
        exact ih U.card (hcard ▸ hU_lt) U rfl hSubU
      · obtain ⟨W_f, W_t, σ_f, σ_t, hpart, hdisj, hWf, hWt⟩ :=
          zielonka_step g T hSubT hT false hodd (fun U hU_lt hSubU => by
            obtain ⟨Wt', Wf', σt', σf', hp', hd', h1, h2⟩ :=
              ih U.card (hcard ▸ hU_lt) U rfl hSubU
            exact ⟨Wf', Wt', σf', σt', Finset.union_comm Wt' Wf' ▸ hp', hd'.symm, h2, h1⟩)
        exact ⟨W_t, W_f, σ_t, σ_f, Finset.union_comm W_f W_t ▸ hpart, hdisj.symm, hWt, hWf⟩
    · have hTeq : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
      subst hTeq
      refine ⟨∅, ∅, fun v => v, fun v => v, by simp, Finset.disjoint_empty_left ∅, ?_, ?_⟩
      · exact ⟨Finset.Subset.refl ∅,
               fun _ hv => False.elim (Finset.notMem_empty _ hv),
               fun _ hv => False.elim (Finset.notMem_empty _ hv),
               fun _ hv => False.elim (Finset.notMem_empty _ hv)⟩
      · exact ⟨Finset.Subset.refl ∅,
               fun _ hv => False.elim (Finset.notMem_empty _ hv),
               fun _ hv => False.elim (Finset.notMem_empty _ hv),
               fun _ hv => False.elim (Finset.notMem_empty _ hv)⟩

/-- Memoryless Adam counterstrategy when `solvePG g v0.val = none`. -/
theorem solvePG_none_adam (g : PGCode) (v0 : Fin (g.1 + 1)) :
    solvePG g v0.val = none →
      ∃ τ : Fin (g.1 + 1) → Fin (g.1 + 1),
        (∀ v : Fin (g.1 + 1), owner g v = false → τ v ∈ succList g v) ∧
        (∀ π : ℕ → Fin (g.1 + 1), π 0 = v0 →
          (∀ n : ℕ, π (n + 1) ∈ succList g (π n)) →
          (∀ n : ℕ, owner g (π n) = false → π (n + 1) = τ (π n)) →
          ¬ ParityCond (fun n => prio g (π n))) := by
  classical
  intro hnone
  obtain ⟨W_true, W_false, σ_true, σ_false, hpart, _, hWt, hWf⟩ :=
    zielonka g Finset.univ (isSubgame_univ g)
  have hv0_not_true : v0 ∉ W_true := by
    intro hv0_t
    let σ_glob : Fin (g.1 + 1) → Fin (g.1 + 1) := fun v =>
      if v ∈ W_true then σ_true v else (succList g v).head (succList_ne_nil g v)
    have hleg : ∀ v : Fin (g.1 + 1), owner g v = true → σ_glob v ∈ succList g v := by
      intro v hown
      dsimp only [σ_glob]
      by_cases hvW : v ∈ W_true
      · rw [if_pos hvW]; exact (hWt.own_step v hvW hown).1
      · rw [if_neg hvW]; exact List.head_mem _
    have hwin : ∀ π : ℕ → Fin (g.1 + 1), π 0 = v0 →
        (∀ n : ℕ, π (n + 1) ∈ succList g (π n)) →
        (∀ n : ℕ, owner g (π n) = true → π (n + 1) = σ_glob (π n)) →
        ParityCond (fun n => prio g (π n)) := by
      intro π hπ0 hπ_succ hπ_con
      have hstay : ∀ n : ℕ, π n ∈ W_true := by
        intro n
        induction n with
        | zero => rw [hπ0]; exact hv0_t
        | succ n ih =>
          by_cases hown : owner g (π n) = true
          · rw [hπ_con n hown]
            dsimp only [σ_glob]
            rw [if_pos ih]
            exact (hWt.own_step _ ih hown).2
          · exact hWt.opp_step _ ih hown _ (hπ_succ n) (Finset.mem_univ _)
      exact hWt.wins π (hπ0 ▸ hv0_t)
        (fun n => ⟨hπ_succ n, Finset.mem_univ _⟩)
        (fun n hown => by
          have hs := hπ_con n hown
          dsimp only [σ_glob] at hs
          rwa [if_pos (hstay n)] at hs)
    exact solvePG_ne_none_of_memless_eve g v0 σ_glob hleg hwin hnone
  have hv0_f : v0 ∈ W_false := by
    have hmem : v0 ∈ W_true ∪ W_false := hpart.symm ▸ Finset.mem_univ v0
    rcases Finset.mem_union.mp hmem with ht | hf
    · exact False.elim (hv0_not_true ht)
    · exact hf
  let τ : Fin (g.1 + 1) → Fin (g.1 + 1) := fun v =>
    if v ∈ W_false then σ_false v else (succList g v).head (succList_ne_nil g v)
  refine ⟨τ, ?_, ?_⟩
  · intro v hown
    dsimp only [τ]
    by_cases hvW : v ∈ W_false
    · rw [if_pos hvW]; exact (hWf.own_step v hvW hown).1
    · rw [if_neg hvW]; exact List.head_mem _
  · intro π hπ0 hπ_succ hπ_con
    have hstay : ∀ n : ℕ, π n ∈ W_false := by
      intro n
      induction n with
      | zero => rw [hπ0]; exact hv0_f
      | succ n ih =>
        by_cases hown : owner g (π n) = false
        · rw [hπ_con n hown]
          dsimp only [τ]
          rw [if_pos ih]
          exact (hWf.own_step _ ih hown).2
        · exact hWf.opp_step _ ih hown _ (hπ_succ n) (Finset.mem_univ _)
    have hodd : OddParityCond (fun n => prio g (π n)) :=
      hWf.wins π (hπ0 ▸ hv0_f)
        (fun n => ⟨hπ_succ n, Finset.mem_univ _⟩)
        (fun n hown => by
          have hs := hπ_con n hown
          dsimp only [τ] at hs
          rwa [if_pos (hstay n)] at hs)
    exact fun heven => not_parityCond_and_oddParityCond _ ⟨heven, hodd⟩

def ValidHistEve (g : PGCode)
    (σ_hist : List (Fin (g.1 + 1)) → Fin (g.1 + 1)) : Prop :=
  ∀ (h : List (Fin (g.1 + 1))) (hne : h ≠ []),
    owner g (h.getLast hne) = true → σ_hist h ∈ succList g (h.getLast hne)

def PlayConsistentEve (g : PGCode) (v0 : Fin (g.1 + 1))
    (σ_hist : List (Fin (g.1 + 1)) → Fin (g.1 + 1))
    (π : ℕ → Fin (g.1 + 1)) : Prop :=
  π 0 = v0 ∧
    (∀ n : ℕ, π (n + 1) ∈ succList g (π n)) ∧
    (∀ n : ℕ, owner g (π n) = true →
      π (n + 1) = σ_hist (List.ofFn (fun i : Fin (n + 1) => π i.val)))

theorem solvePG_iff_histEve (g : PGCode) (v0 : Fin (g.1 + 1)) :
    solvePG g v0.val ≠ none ↔
      ∃ σ_hist : List (Fin (g.1 + 1)) → Fin (g.1 + 1),
        ValidHistEve g σ_hist ∧
          ∀ π : ℕ → Fin (g.1 + 1), PlayConsistentEve g v0 σ_hist π →
            ParityCond (fun n => prio g (π n)) := by
  constructor
  · intro hne
    cases hsol : solvePG g v0.val with
    | none => exact False.elim (hne hsol)
    | some σ =>
      obtain ⟨_, _, hleg, hwin⟩ := solvePG_some_sound g v0 σ hsol
      let σFin := stratToFin g σ
      let σ_hist : List (Fin (g.1 + 1)) → Fin (g.1 + 1) := fun h =>
        if hne_l : h ≠ [] then σFin (h.getLast hne_l) else v0
      refine ⟨σ_hist, ?_, ?_⟩
      · intro h hne_l hown
        dsimp only [σ_hist]
        rw [dif_pos hne_l]
        exact hleg _ hown
      · rintro π ⟨hπ0, hπ_succ, hπ_con⟩
        apply hwin π hπ0 hπ_succ
        intro n hown
        have hc := hπ_con n hown
        dsimp only [σ_hist] at hc
        have hne_fn : List.ofFn (fun i : Fin (n + 1) => π i.val) ≠ [] := by simp
        rw [dif_pos hne_fn] at hc
        have hlast : (List.ofFn (fun i : Fin (n + 1) => π i.val)).getLast hne_fn = π n := by
          rw [List.getLast_eq_getElem]
          simp only [List.length_ofFn, Nat.add_sub_cancel, List.getElem_ofFn]
        rwa [hlast] at hc
  · rintro ⟨σ_hist, hleg_hist, hwin_hist⟩ hnone
    obtain ⟨τ, hleg_τ, hwin_τ⟩ := solvePG_none_adam g v0 hnone
    have hgetLastD_snoc : ∀ (l : List (Fin (g.1 + 1))) (x d : Fin (g.1 + 1)),
        (l ++ [x]).getLastD d = x := by
      intro l x d
      cases l with
      | nil => rfl
      | cons a as => simp [List.getLastD]
    have hgetLastD_eq : ∀ (l : List (Fin (g.1 + 1))) (hne : l ≠ []) (d : Fin (g.1 + 1)),
        l.getLastD d = l.getLast hne := by
      intro l
      induction l with
      | nil => intro hne; exact False.elim (hne rfl)
      | cons a as ih =>
        intro _ _
        cases as with
        | nil => rfl
        | cons b bs => exact ih (List.cons_ne_nil b bs) a
    let stepHist : List (Fin (g.1 + 1)) → List (Fin (g.1 + 1)) := fun h =>
      let cur := h.getLastD v0
      let nxt := if owner g cur = true then σ_hist h else τ cur
      h ++ [nxt]
    let hist : ℕ → List (Fin (g.1 + 1)) := fun n => Nat.rec [v0] (fun _ prev => stepHist prev) n
    let π : ℕ → Fin (g.1 + 1) := fun n => (hist n).getLastD v0
    have hhist_ne : ∀ n : ℕ, hist n ≠ [] := by
      intro n
      cases n with
      | zero => simp [hist]
      | succ n =>
        change stepHist (hist n) ≠ []
        simp [stepHist]
    have hlast_eq : ∀ n : ℕ, (hist n).getLast (hhist_ne n) = π n := by
      intro n
      exact (hgetLastD_eq (hist n) (hhist_ne n) v0).symm
    have hπ0 : π 0 = v0 := rfl
    have hπ_nxt : ∀ n : ℕ,
        π (n + 1) = if owner g (π n) = true then σ_hist (hist n) else τ (π n) := by
      intro n
      change (stepHist (hist n)).getLastD v0 = _
      dsimp only [stepHist]
      rw [hgetLastD_snoc]
    have hhist_eq_ofFn : ∀ n : ℕ, hist n = List.ofFn (fun i : Fin (n + 1) => π i.val) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [List.ofFn_succ', List.concat_eq_append]
        change stepHist (hist n) = _
        dsimp only [stepHist]
        rw [← hπ_nxt n, ih]
        rfl
    have hπ_succ : ∀ n : ℕ, π (n + 1) ∈ succList g (π n) := by
      intro n
      rw [hπ_nxt n]
      by_cases hown : owner g (π n) = true
      · rw [if_pos hown, ← hlast_eq n]
        exact hleg_hist (hist n) (hhist_ne n) (by rwa [hlast_eq n])
      · rw [if_neg hown]
        exact hleg_τ (π n) (Bool.eq_false_iff.mpr hown)
    have hcon_eve : PlayConsistentEve g v0 σ_hist π := by
      refine ⟨hπ0, hπ_succ, fun n hown => ?_⟩
      rw [hπ_nxt n, if_pos hown, hhist_eq_ofFn n]
    have hcon_adam : ∀ n : ℕ, owner g (π n) = false → π (n + 1) = τ (π n) := by
      intro n hown
      rw [hπ_nxt n, hown]
      rfl
    exact hwin_τ π hπ0 hπ_succ hcon_adam (hwin_hist π hcon_eve)

/-! ### Section 5: Parametric `Nat.Partrec.Code` Compiler & Regular Symbolic Tree Solver -/

def encConstCode : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * (2 * Nat.pair 1 (encConstCode n) + 1) + 4

lemma encConstCode_eq (n : ℕ) : encConstCode n = Encodable.encode (Nat.Partrec.Code.const n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 2 * (2 * Nat.pair 1 (encConstCode n) + 1) + 4 =
      Encodable.encode (Nat.Partrec.Code.comp .succ (Nat.Partrec.Code.const n))
    have hcomp : ∀ a b : Nat.Partrec.Code,
        Encodable.encode (Nat.Partrec.Code.comp a b) =
          2 * (2 * Nat.pair (Encodable.encode a) (Encodable.encode b) + 1) + 4 := fun _ _ => rfl
    have hsucc : Encodable.encode Nat.Partrec.Code.succ = 1 := rfl
    rw [hcomp, hsucc, ih]

lemma primrec_encConstCode : Primrec encConstCode := by
  have hstep : Primrec fun p : ℕ × ℕ => 2 * (2 * Nat.pair 1 p.2 + 1) + 4 :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
          (primrec₂_natPair.comp (Primrec.const 1) Primrec.snd))))
      (Primrec.const 4)
  exact (Primrec.nat_rec₁ 0 hstep.to₂).of_eq fun n => by
    induction n with
    | zero => rfl
    | succ n ih => simp [encConstCode, ih]

theorem computable_curry_nat (U : Nat.Partrec.Code) :
    Computable fun n : ℕ => U.curry n := by
  let eU := Encodable.encode U
  let eId := Encodable.encode Nat.Partrec.Code.id
  let encCurry : ℕ → ℕ := fun n =>
    let ePair := 2 * (2 * Nat.pair (encConstCode n) eId) + 4
    2 * (2 * Nat.pair eU ePair + 1) + 4
  have henc_prim : Primrec encCurry := by
    have hePair : Primrec fun n : ℕ => 2 * (2 * Nat.pair (encConstCode n) eId) + 4 :=
      Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 2)
          (Primrec.nat_mul.comp (Primrec.const 2)
            (primrec₂_natPair.comp primrec_encConstCode (Primrec.const eId))))
        (Primrec.const 4)
    exact Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
          (primrec₂_natPair.comp (Primrec.const eU) hePair))))
      (Primrec.const 4)
  have henc_eq : ∀ n : ℕ, encCurry n = Encodable.encode (U.curry n) := by
    intro n
    dsimp only [encCurry, eU, eId]
    rw [encConstCode_eq]
    rfl
  have hcomp : Computable fun n : ℕ => Denumerable.ofNat Nat.Partrec.Code (encCurry n) :=
    (Computable.ofNat Nat.Partrec.Code).comp henc_prim.to_comp
  exact hcomp.of_eq fun n => by rw [henc_eq, Denumerable.ofNat_encode]

/-- General parametric `Nat.Partrec.Code` compiler: any computable family of functions on
`List ℕ` indexed by a `Primcodable` parameter `p : P` compiles computably to `Nat.Partrec.Code`s.
Use `exists_parametric_code_nat` when `P = ℕ` or pre-encode `P` to `ℕ` first! -/
theorem exists_parametric_code_nat
    (evalEnc : ℕ → List ℕ → ℕ) (hcomp : Computable₂ evalEnc) :
    ∃ codeOf : ℕ → Nat.Partrec.Code, Computable codeOf ∧
      ∀ (p : ℕ) (a : List ℕ),
        (codeOf p).eval (Encodable.encode a) = Part.some (evalEnc p a) := by
  let uTot : ℕ → ℕ := fun z =>
    let a := (Encodable.decode (α := List ℕ) z.unpair.2).getD []
    evalEnc z.unpair.1 a
  have huTot_comp : Computable uTot := by
    have ha : Computable fun z : ℕ => (Encodable.decode (α := List ℕ) z.unpair.2).getD [] :=
      (Primrec.option_getD.comp (Primrec.decode.comp (Primrec.snd.comp Primrec.unpair))
        (Primrec.const [])).to_comp
    exact hcomp.comp (Primrec.fst.comp Primrec.unpair).to_comp ha
  have huPart : Nat.Partrec (fun z : ℕ => Part.some (uTot z)) :=
    Partrec.nat_iff.mp huTot_comp.partrec
  obtain ⟨U, hU⟩ := Nat.Partrec.Code.exists_code.mp huPart
  refine ⟨fun p => U.curry p, computable_curry_nat U, ?_⟩
  intro p a
  rw [Nat.Partrec.Code.eval_curry, hU]
  simp [uTot, Nat.unpair_pair]

theorem exists_parametric_code {P : Type} [Primcodable P]
    (evalEnc : P → List ℕ → ℕ) (hcomp : Computable₂ evalEnc) :
    ∃ codeOf : P → Nat.Partrec.Code, Computable codeOf ∧
      ∀ (p : P) (a : List ℕ),
        (codeOf p).eval (Encodable.encode a) = Part.some (evalEnc p a) := by
  let evalNat : ℕ → List ℕ → ℕ := fun n a =>
    match Encodable.decode (α := P) n with
    | none => 0
    | some p => evalEnc p a
  have hevalNat : Computable₂ evalNat := by
    have hdec : Computable fun q : ℕ × List ℕ => Encodable.decode (α := P) q.1 :=
      (Primrec.decode.comp Primrec.fst).to_comp
    have hsome : Computable₂ fun (q : ℕ × List ℕ) (p : P) => evalEnc p q.2 :=
      hcomp.comp Computable.snd (Computable.snd.comp Computable.fst)
    exact (Computable.option_casesOn hdec (Computable.const 0) hsome).of_eq fun q => by
      dsimp only [evalNat]
      cases Encodable.decode (α := P) q.1 <;> rfl
  obtain ⟨cNat, hcNat_comp, hcNat_spec⟩ := exists_parametric_code_nat evalNat hevalNat
  refine ⟨fun p => cNat (Encodable.encode p), hcNat_comp.comp Primrec.encode.to_comp, ?_⟩
  intro p a
  rw [hcNat_spec (Encodable.encode p) a]
  simp [evalNat, Encodable.encodek]

/-! #### Finite Regular Symbolic Tree Solver (`TreeSpecCode`, `treePG`, `solveTreePG`) -/

/-- `(b, A, rootOk, childOk, mN, mTrans, mPrios)` specifying:
branching `b + 1`, node labels `Fin (A + 1)`, root predicate `rootOk`, child relation `childOk`,
and deterministic parity automaton `(mN, mTrans, mPrios)` over `Fin (A + 1) × Fin (b + 1)`. -/
abbrev TreeSpecCode : Type := ℕ × ℕ × List Bool × List Bool × ℕ × List ℕ × List ℕ

def tsRootOk (ts : TreeSpecCode) (a : Fin (ts.2.1 + 1)) : Bool :=
  ts.2.2.1.getD a.val false

def tsChildOk (ts : TreeSpecCode) (a : Fin (ts.2.1 + 1)) (d : Fin (ts.1 + 1))
    (a' : Fin (ts.2.1 + 1)) : Bool :=
  ts.2.2.2.1.getD ((a.val * (ts.1 + 1) + d.val) * (ts.2.1 + 1) + a'.val) false

def tsDPA (ts : TreeSpecCode) :
    DPA (Fin (ts.2.2.2.2.1 + 1)) (Fin (ts.2.1 + 1) × Fin (ts.1 + 1)) where
  init := ⟨0, Nat.succ_pos _⟩
  step q ad :=
    ⟨(ts.2.2.2.2.2.1.getD ((q.val * (ts.2.1 + 1) + ad.1.val) * (ts.1 + 1) + ad.2.val) 0) %
        (ts.2.2.2.2.1 + 1),
      Nat.mod_lt _ (Nat.succ_pos _)⟩
  prio q := ts.2.2.2.2.2.2.getD q.val 0

/-- Pack `TreeSpecCode` into a single `ℕ` so every inner `Primrec` combinator has depth ≤ 2. -/
def packTS (ts : TreeSpecCode) : ℕ :=
  Nat.pair
    (Nat.pair (Nat.pair ts.1 ts.2.1) ts.2.2.2.2.1)
    (Nat.pair
      (Nat.pair (Encodable.encode ts.2.2.1) (Encodable.encode ts.2.2.2.1))
      (Nat.pair (Encodable.encode ts.2.2.2.2.2.1) (Encodable.encode ts.2.2.2.2.2.2)))

lemma primrec_packTS : Primrec packTS := by
  have hb : Primrec fun ts : TreeSpecCode => ts.1 := Primrec.fst
  have hr1 : Primrec fun ts : TreeSpecCode => ts.2 := Primrec.snd
  have hA : Primrec fun ts : TreeSpecCode => ts.2.1 := Primrec.fst.comp hr1
  have hr2 : Primrec fun ts : TreeSpecCode => ts.2.2 := Primrec.snd.comp hr1
  have hrok : Primrec fun ts : TreeSpecCode => Encodable.encode ts.2.2.1 :=
    Primrec.encode.comp (Primrec.fst.comp hr2)
  have hr3 : Primrec fun ts : TreeSpecCode => ts.2.2.2 := Primrec.snd.comp hr2
  have hcok : Primrec fun ts : TreeSpecCode => Encodable.encode ts.2.2.2.1 :=
    Primrec.encode.comp (Primrec.fst.comp hr3)
  have hr4 : Primrec fun ts : TreeSpecCode => ts.2.2.2.2 := Primrec.snd.comp hr3
  have hmN : Primrec fun ts : TreeSpecCode => ts.2.2.2.2.1 := Primrec.fst.comp hr4
  have hr5 : Primrec fun ts : TreeSpecCode => ts.2.2.2.2.2 := Primrec.snd.comp hr4
  have htr : Primrec fun ts : TreeSpecCode => Encodable.encode ts.2.2.2.2.2.1 :=
    Primrec.encode.comp (Primrec.fst.comp hr5)
  have hpr : Primrec fun ts : TreeSpecCode => Encodable.encode ts.2.2.2.2.2.2 :=
    Primrec.encode.comp (Primrec.snd.comp hr5)
  exact primrec₂_natPair.comp
    (primrec₂_natPair.comp (primrec₂_natPair.comp hb hA) hmN)
    (primrec₂_natPair.comp (primrec₂_natPair.comp hrok hcok) (primrec₂_natPair.comp htr hpr))

def tspB (tp : ℕ) : ℕ := tp.unpair.1.unpair.1.unpair.1 + 1
def tspL (tp : ℕ) : ℕ := tp.unpair.1.unpair.1.unpair.2 + 1
def tspQ (tp : ℕ) : ℕ := tp.unpair.1.unpair.2 + 1
def tspRootList (tp : ℕ) : List Bool := (Encodable.decode (α := List Bool) tp.unpair.2.unpair.1.unpair.1).getD []
def tspChildList (tp : ℕ) : List Bool := (Encodable.decode (α := List Bool) tp.unpair.2.unpair.1.unpair.2).getD []
def tspTransList (tp : ℕ) : List ℕ := (Encodable.decode (α := List ℕ) tp.unpair.2.unpair.2.unpair.1).getD []
def tspPrioList (tp : ℕ) : List ℕ := (Encodable.decode (α := List ℕ) tp.unpair.2.unpair.2.unpair.2).getD []

@[simp] lemma tspB_pack (ts : TreeSpecCode) : tspB (packTS ts) = ts.1 + 1 := by
  simp [tspB, packTS, Nat.unpair_pair]
@[simp] lemma tspL_pack (ts : TreeSpecCode) : tspL (packTS ts) = ts.2.1 + 1 := by
  simp [tspL, packTS, Nat.unpair_pair]
@[simp] lemma tspQ_pack (ts : TreeSpecCode) : tspQ (packTS ts) = ts.2.2.2.2.1 + 1 := by
  simp [tspQ, packTS, Nat.unpair_pair]
@[simp] lemma tspRootList_pack (ts : TreeSpecCode) : tspRootList (packTS ts) = ts.2.2.1 := by
  simp [tspRootList, packTS, Nat.unpair_pair, Encodable.encodek]
@[simp] lemma tspChildList_pack (ts : TreeSpecCode) : tspChildList (packTS ts) = ts.2.2.2.1 := by
  simp [tspChildList, packTS, Nat.unpair_pair, Encodable.encodek]
@[simp] lemma tspTransList_pack (ts : TreeSpecCode) : tspTransList (packTS ts) = ts.2.2.2.2.2.1 := by
  simp [tspTransList, packTS, Nat.unpair_pair]
@[simp] lemma tspPrioList_pack (ts : TreeSpecCode) : tspPrioList (packTS ts) = ts.2.2.2.2.2.2 := by
  simp [tspPrioList, packTS, Nat.unpair_pair]

lemma primrec_tspB : Primrec tspB :=
  Primrec.succ.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))))
lemma primrec_tspL : Primrec tspL :=
  Primrec.succ.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))))
lemma primrec_tspQ : Primrec tspQ :=
  Primrec.succ.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
lemma primrec_tspRootList : Primrec tspRootList :=
  Primrec.option_getD.comp
    (Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))))
    (Primrec.const [])
lemma primrec_tspChildList : Primrec tspChildList :=
  Primrec.option_getD.comp
    (Primrec.decode.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))))
    (Primrec.const [])
lemma primrec_tspTransList : Primrec tspTransList :=
  Primrec.option_getD.comp
    (Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))))
    (Primrec.const [])
lemma primrec_tspPrioList : Primrec tspPrioList :=
  Primrec.option_getD.comp
    (Primrec.decode.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))))
    (Primrec.const [])

def tupleAt (L tup d : ℕ) : ℕ :=
  (tup / myPow L d) % L

lemma primrec₂_tupleAt_packed : Primrec₂ fun (lt : ℕ) (d : ℕ) => tupleAt lt.unpair.1 lt.unpair.2 d :=
  Primrec.nat_mod.comp
    (Primrec.nat_div.comp
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))
      (primrec₂_myPow.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)) Primrec.snd))
    (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))

lemma primrec_tupleAt3 {α : Type*} [Primcodable α]
    {fL ftup fd : α → ℕ} (hL : Primrec fL) (htup : Primrec ftup) (hd : Primrec fd) :
    Primrec fun x => tupleAt (fL x) (ftup x) (fd x) :=
  (primrec₂_tupleAt_packed.comp (primrec₂_natPair.comp hL htup) hd).of_eq fun _ => by
    simp [Nat.unpair_pair]

def childOkPacked (tp : ℕ) (ada' : ℕ) : Bool :=
  let a := ada'.unpair.1
  let d := ada'.unpair.2.unpair.1
  let a' := ada'.unpair.2.unpair.2
  (tspChildList tp).getD ((a * tspB tp + d) * tspL tp + a') false

lemma primrec₂_childOkPacked : Primrec₂ childOkPacked := by
  have ha : Primrec fun p : ℕ × ℕ => p.2.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hd : Primrec fun p : ℕ × ℕ => p.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
  have ha' : Primrec fun p : ℕ × ℕ => p.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
  have hidx := Primrec.nat_add.comp
    (Primrec.nat_mul.comp
      (Primrec.nat_add.comp (Primrec.nat_mul.comp ha (primrec_tspB.comp Primrec.fst)) hd)
      (primrec_tspL.comp Primrec.fst))
    ha'
  exact (Primrec.list_getD false).comp (primrec_tspChildList.comp Primrec.fst) hidx

def tupleValidStep (tpa : ℕ) (tup : ℕ) (ok : Bool) (d : ℕ) : Bool :=
  let tp := tpa.unpair.1
  let a := tpa.unpair.2
  let a' := tupleAt (tspL tp) tup d
  andBool ok (childOkPacked tp (Nat.pair a (Nat.pair d a')))

lemma primrec_tupleValidStep :
    Primrec fun q : (ℕ × ℕ) × (Bool × ℕ) => tupleValidStep q.1.1 q.1.2 q.2.1 q.2.2 := by
  have fstQ : Primrec fun q : (ℕ × ℕ) × (Bool × ℕ) => q.1 := Primrec.fst
  have q_tp : Primrec fun q : (ℕ × ℕ) × (Bool × ℕ) => q.1.1.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp fstQ))
  have q_a : Primrec fun q : (ℕ × ℕ) × (Bool × ℕ) => q.1.1.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp fstQ))
  have q_tup : Primrec fun q : (ℕ × ℕ) × (Bool × ℕ) => q.1.2 := Primrec.snd.comp fstQ
  have q_d : Primrec fun q : (ℕ × ℕ) × (Bool × ℕ) => q.2.2 := Primrec.snd.comp Primrec.snd
  have q_a' := primrec_tupleAt3 (primrec_tspL.comp q_tp) q_tup q_d
  exact primrec₂_andBool.comp (Primrec.fst.comp Primrec.snd)
    (primrec₂_childOkPacked.comp q_tp (primrec₂_natPair.comp q_a (primrec₂_natPair.comp q_d q_a')))

def tupleValidPacked (tpa : ℕ) (tup : ℕ) : Bool :=
  (List.range (tspB tpa.unpair.1)).foldl (fun ok d => tupleValidStep tpa tup ok d) true

lemma primrec₂_tupleValidPacked : Primrec₂ tupleValidPacked := by
  have htp : Primrec fun p : ℕ × ℕ => p.1.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  exact primrec_foldl_clean (Primrec.list_range.comp (primrec_tspB.comp htp)) (Primrec.const true)
    primrec_tupleValidStep

def stepMonPacked (tp : ℕ) (qad : ℕ) : ℕ :=
  let q := qad.unpair.1
  let a := qad.unpair.2.unpair.1
  let d := qad.unpair.2.unpair.2
  ((tspTransList tp).getD ((q * tspL tp + a) * tspB tp + d) 0) % tspQ tp

lemma primrec₂_stepMonPacked : Primrec₂ stepMonPacked := by
  have hq : Primrec fun p : ℕ × ℕ => p.2.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have ha : Primrec fun p : ℕ × ℕ => p.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
  have hd : Primrec fun p : ℕ × ℕ => p.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
  have hidx := Primrec.nat_add.comp
    (Primrec.nat_mul.comp
      (Primrec.nat_add.comp (Primrec.nat_mul.comp hq (primrec_tspL.comp Primrec.fst)) ha)
      (primrec_tspB.comp Primrec.fst))
    hd
  exact Primrec.nat_mod.comp
    ((Primrec.list_getD 0).comp (primrec_tspTransList.comp Primrec.fst) hidx)
    (primrec_tspQ.comp Primrec.fst)

def tspTotVerts (tp : ℕ) : ℕ :=
  let B := tspB tp
  let L := tspL tp
  let Q := tspQ tp
  let T := myPow L B
  2 + L * Q + L * T * Q

lemma primrec_tspTotVerts : Primrec tspTotVerts :=
  Primrec.nat_add.comp
    (Primrec.nat_add.comp (Primrec.const 2) (Primrec.nat_mul.comp primrec_tspL primrec_tspQ))
    (Primrec.nat_mul.comp
      (Primrec.nat_mul.comp primrec_tspL (primrec₂_myPow.comp primrec_tspL primrec_tspB))
      primrec_tspQ)

def treeOwnerPacked (tp v : ℕ) : Bool :=
  decide (v < 2 + tspL tp * tspQ tp)

lemma primrec₂_treeOwnerPacked : Primrec₂ treeOwnerPacked :=
  Primrec.ite
    (Primrec.nat_lt.comp Primrec.snd
      (Primrec.nat_add.comp (Primrec.const 2)
        (Primrec.nat_mul.comp (primrec_tspL.comp Primrec.fst) (primrec_tspQ.comp Primrec.fst))))
    (Primrec.const true) (Primrec.const false)

def treePrioPacked (tp v : ℕ) : ℕ :=
  let L := tspL tp
  let Q := tspQ tp
  if v = 0 then 0
  else if v = 1 then 1
  else if v < 2 + L * Q then (tspPrioList tp).getD ((v - 2) % Q) 0
  else (tspPrioList tp).getD ((v - (2 + L * Q)) % Q) 0

lemma primrec₂_treePrioPacked : Primrec₂ treePrioPacked := by
  have fstP : Primrec fun p : ℕ × ℕ => p.1 := Primrec.fst
  have hQ := primrec_tspQ.comp fstP
  have hbase := Primrec.nat_add.comp (Primrec.const 2)
    (Primrec.nat_mul.comp (primrec_tspL.comp fstP) hQ)
  have hpr := primrec_tspPrioList.comp fstP
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const 0)
    (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 1)) (Primrec.const 1)
      (Primrec.ite (Primrec.nat_lt.comp Primrec.snd hbase)
        ((Primrec.list_getD 0).comp hpr (Primrec.nat_mod.comp (Primrec.nat_sub.comp Primrec.snd (Primrec.const 2)) hQ))
        ((Primrec.list_getD 0).comp hpr (Primrec.nat_mod.comp (Primrec.nat_sub.comp Primrec.snd hbase) hQ))))

def treeSuccPacked (tp v : ℕ) : List ℕ :=
  let B := tspB tp
  let L := tspL tp
  let Q := tspQ tp
  let T := myPow L B
  if v = 0 then
    let l := (List.range L).flatMap fun a =>
      if (tspRootList tp).getD a false = true then [2 + a * Q] else []
    if l.length = 0 then [1] else l
  else if v = 1 then [1]
  else if v < 2 + L * Q then
    let a := (v - 2) / Q
    let q := (v - 2) % Q
    let l := (List.range T).flatMap fun tup =>
      if tupleValidPacked (Nat.pair tp a) tup = true then [2 + L * Q + (a * T + tup) * Q + q] else []
    if l.length = 0 then [1] else l
  else
    let idx := v - (2 + L * Q)
    let q := idx % Q
    let atup := idx / Q
    let a := atup / T
    let tup := atup % T
    (List.range B).map fun d =>
      let a' := tupleAt L tup d
      2 + a' * Q + stepMonPacked tp (Nat.pair q (Nat.pair a d))

lemma primrec₂_treeSuccPacked : Primrec₂ treeSuccPacked := by
  have fstP : Primrec fun p : ℕ × ℕ => p.1 := Primrec.fst
  have hB := primrec_tspB.comp fstP
  have hL := primrec_tspL.comp fstP
  have hQ := primrec_tspQ.comp fstP
  have hT := primrec₂_myPow.comp hL hB
  have hbase := Primrec.nat_add.comp (Primrec.const 2) (Primrec.nat_mul.comp hL hQ)
  -- `v = 0`
  have hl0 : Primrec fun p : ℕ × ℕ =>
      (List.range (tspL p.1)).flatMap fun a =>
        if (tspRootList p.1).getD a false = true then [2 + a * tspQ p.1] else [] := by
    have fstQ : Primrec fun q : (ℕ × ℕ) × ℕ => q.1 := Primrec.fst
    have q_rok := (Primrec.list_getD false).comp (primrec_tspRootList.comp (fstP.comp fstQ)) Primrec.snd
    have q_tgt := Primrec.nat_add.comp (Primrec.const 2)
      (Primrec.nat_mul.comp Primrec.snd (hQ.comp fstQ))
    exact Primrec.list_flatMap (Primrec.list_range.comp hL)
      (Primrec.ite (Primrec.eq.comp q_rok (Primrec.const true))
        (Primrec.list_cons.comp q_tgt (Primrec.const [])) (Primrec.const [])).to₂
  have hb0 := Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp hl0) (Primrec.const 0))
    (Primrec.const [1]) hl0
  -- Eve state
  have ha_e := Primrec.nat_div.comp (Primrec.nat_sub.comp Primrec.snd (Primrec.const 2)) hQ
  have hq_e := Primrec.nat_mod.comp (Primrec.nat_sub.comp Primrec.snd (Primrec.const 2)) hQ
  have hl_e : Primrec fun p : ℕ × ℕ =>
      let L := tspL p.1; let Q := tspQ p.1; let T := myPow L (tspB p.1)
      let a := (p.2 - 2) / Q; let q := (p.2 - 2) % Q
      (List.range T).flatMap fun tup =>
        if tupleValidPacked (Nat.pair p.1 a) tup = true
        then [2 + L * Q + (a * T + tup) * Q + q] else [] := by
    have fstQ : Primrec fun q : (ℕ × ℕ) × ℕ => q.1 := Primrec.fst
    have q_tpa := primrec₂_natPair.comp (fstP.comp fstQ) (ha_e.comp fstQ)
    have q_val := primrec₂_tupleValidPacked.comp q_tpa Primrec.snd
    have q_tgt := Primrec.nat_add.comp
      (Primrec.nat_add.comp (hbase.comp fstQ)
        (Primrec.nat_mul.comp
          (Primrec.nat_add.comp (Primrec.nat_mul.comp (ha_e.comp fstQ) (hT.comp fstQ)) Primrec.snd)
          (hQ.comp fstQ)))
      (hq_e.comp fstQ)
    exact Primrec.list_flatMap (Primrec.list_range.comp hT)
      (Primrec.ite (Primrec.eq.comp q_val (Primrec.const true))
        (Primrec.list_cons.comp q_tgt (Primrec.const [])) (Primrec.const [])).to₂
  have hb_e := Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp hl_e) (Primrec.const 0))
    (Primrec.const [1]) hl_e
  -- Adam state
  have hidx_a := Primrec.nat_sub.comp Primrec.snd hbase
  have hq_a := Primrec.nat_mod.comp hidx_a hQ
  have hat_a := Primrec.nat_div.comp hidx_a hQ
  have ha_a := Primrec.nat_div.comp hat_a hT
  have ht_a := Primrec.nat_mod.comp hat_a hT
  have hb_a : Primrec fun p : ℕ × ℕ =>
      let B := tspB p.1; let L := tspL p.1; let Q := tspQ p.1; let T := myPow L B
      let idx := p.2 - (2 + L * Q); let q := idx % Q; let atup := idx / Q
      let a := atup / T; let tup := atup % T
      (List.range B).map fun d =>
        let a' := tupleAt L tup d
        2 + a' * Q + stepMonPacked p.1 (Nat.pair q (Nat.pair a d)) := by
    have fstQ : Primrec fun q : (ℕ × ℕ) × ℕ => q.1 := Primrec.fst
    have r_a' := primrec_tupleAt3 (hL.comp fstQ) (ht_a.comp fstQ) Primrec.snd
    have r_qad := primrec₂_natPair.comp (hq_a.comp fstQ)
      (primrec₂_natPair.comp (ha_a.comp fstQ) Primrec.snd)
    have r_q' := primrec₂_stepMonPacked.comp (fstP.comp fstQ) r_qad
    have r_tgt := Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.const 2) (Primrec.nat_mul.comp r_a' (hQ.comp fstQ)))
      r_q'
    exact Primrec.list_map (Primrec.list_range.comp hB) r_tgt.to₂
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) hb0
    (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 1)) (Primrec.const [1])
      (Primrec.ite (Primrec.nat_lt.comp Primrec.snd hbase) hb_e hb_a))

def treePGPacked (tp : ℕ) : PGCode :=
  let V := tspTotVerts tp
  (V - 1,
   (List.range V).map (treeOwnerPacked tp),
   (List.range V).map (treeSuccPacked tp),
   (List.range V).map (treePrioPacked tp))

def treePG (ts : TreeSpecCode) : PGCode :=
  treePGPacked (packTS ts)

def solveTreePG (ts : TreeSpecCode) : Option (List ℕ) :=
  solvePG (treePG ts) 0

lemma primrec_treePGPacked : Primrec treePGPacked := by
  have hrange : Primrec fun tp : ℕ => List.range (tspTotVerts tp) :=
    Primrec.list_range.comp primrec_tspTotVerts
  exact Primrec.pair (Primrec.nat_sub.comp primrec_tspTotVerts (Primrec.const 1))
    (Primrec.pair (Primrec.list_map hrange primrec₂_treeOwnerPacked)
      (Primrec.pair (Primrec.list_map hrange primrec₂_treeSuccPacked)
        (Primrec.list_map hrange primrec₂_treePrioPacked)))

theorem primrec_treePG : Primrec treePG :=
  primrec_treePGPacked.comp primrec_packTS

theorem primrec_solveTreePG : Primrec solveTreePG := by
  have h : Primrec fun tp : ℕ => solvePGPacked (Nat.pair (packPG (treePGPacked tp)) 0) :=
    primrec_solvePGPacked.comp
      (primrec₂_natPair.comp (primrec_packPG.comp primrec_treePGPacked) (Primrec.const 0))
  exact (h.comp primrec_packTS).of_eq fun ts => solvePGPacked_eq (treePG ts) 0

theorem computable_solveTreePG : Computable solveTreePG :=
  primrec_solveTreePG.to_comp

/-! #### Tree Unfolding (`Primrec`) & `Nat.Partrec.Code` Extractor -/

def unfoldStepPacked (tpσ : ℕ) (aq : ℕ) (d : ℕ) : ℕ :=
  let tp := tpσ.unpair.1
  let σ := (Encodable.decode (α := List ℕ) tpσ.unpair.2).getD []
  let B := tspB tp
  let L := tspL tp
  let Q := tspQ tp
  let T := myPow L B
  let a := aq.unpair.1
  let q := aq.unpair.2
  let d' := d % B
  let vEve := 2 + a * Q + q
  let vAdam := σ.getD vEve 1
  let tup := ((vAdam - (2 + L * Q)) / Q) % T
  let a' := tupleAt L tup d'
  let q' := stepMonPacked tp (Nat.pair q (Nat.pair a d'))
  Nat.pair a' q'

def unfoldStatePacked (tpσ : ℕ) (addr : List ℕ) : ℕ :=
  let tp := tpσ.unpair.1
  let σ := (Encodable.decode (α := List ℕ) tpσ.unpair.2).getD []
  let L := tspL tp
  let Q := tspQ tp
  let v0 := σ.getD 0 1
  let a0 := ((v0 - 2) / Q) % L
  addr.foldl (fun aq d => unfoldStepPacked tpσ aq d) (Nat.pair a0 0)

lemma primrec₂_unfoldStatePacked : Primrec₂ unfoldStatePacked := by
  have htp : Primrec fun p : ℕ × List ℕ => p.1.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  have hσ : Primrec fun p : ℕ × List ℕ => (Encodable.decode (α := List ℕ) p.1.unpair.2).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))) (Primrec.const [])
  have hL := primrec_tspL.comp htp
  have hQ := primrec_tspQ.comp htp
  have hv0 := (Primrec.list_getD 1).comp hσ (Primrec.const 0)
  have ha0 := Primrec.nat_mod.comp (Primrec.nat_div.comp (Primrec.nat_sub.comp hv0 (Primrec.const 2)) hQ) hL
  have hinit := primrec₂_natPair.comp ha0 (Primrec.const 0)
  have hstep : Primrec fun r : (ℕ × List ℕ) × (ℕ × ℕ) => unfoldStepPacked r.1.1 r.2.1 r.2.2 := by
    have fstR : Primrec fun r : (ℕ × List ℕ) × (ℕ × ℕ) => r.1 := Primrec.fst
    have r_tp := htp.comp fstR
    have r_σ := hσ.comp fstR
    have r_B := primrec_tspB.comp r_tp
    have r_L := primrec_tspL.comp r_tp
    have r_Q := primrec_tspQ.comp r_tp
    have r_T := primrec₂_myPow.comp r_L r_B
    have r_a : Primrec fun r : (ℕ × List ℕ) × (ℕ × ℕ) => r.2.1.unpair.1 :=
      Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd))
    have r_q : Primrec fun r : (ℕ × List ℕ) × (ℕ × ℕ) => r.2.1.unpair.2 :=
      Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd))
    have r_d' := Primrec.nat_mod.comp (Primrec.snd.comp Primrec.snd) r_B
    have r_vE := Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.const 2) (Primrec.nat_mul.comp r_a r_Q)) r_q
    have r_vA := (Primrec.list_getD 1).comp r_σ r_vE
    have r_base := Primrec.nat_add.comp (Primrec.const 2) (Primrec.nat_mul.comp r_L r_Q)
    have r_tup := Primrec.nat_mod.comp (Primrec.nat_div.comp (Primrec.nat_sub.comp r_vA r_base) r_Q) r_T
    have r_a' := primrec_tupleAt3 r_L r_tup r_d'
    have r_q' := primrec₂_stepMonPacked.comp r_tp (primrec₂_natPair.comp r_q (primrec₂_natPair.comp r_a r_d'))
    exact primrec₂_natPair.comp r_a' r_q'
  exact Primrec.list_foldl Primrec.snd hinit hstep.to₂

def unfoldLabelNat (ts : TreeSpecCode) (σ : List ℕ) (addr : List ℕ) : ℕ :=
  (unfoldStatePacked (Nat.pair (packTS ts) (Encodable.encode σ)) addr).unpair.1

def unfoldTree (ts : TreeSpecCode) (σ : List ℕ)
    (addr : List (Fin (ts.1 + 1))) : Fin (ts.2.1 + 1) :=
  ⟨(unfoldLabelNat ts σ (addr.map Fin.val)) % (ts.2.1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

def unfoldLabeledTree (ts : TreeSpecCode) (σ : List ℕ) :
    LabeledTree (Fin (ts.2.1 + 1)) where
  label addr := ⟨(unfoldLabelNat ts σ addr) % (ts.2.1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  nChildren _ := ts.1 + 1

/-- Computable `Nat.Partrec.Code` extractor for `unfoldLabeledTree ts σ`. -/
theorem exists_tree_code_extractor :
    ∃ ext : TreeSpecCode × List ℕ → Nat.Partrec.Code, Computable ext ∧
      ∀ (ts : TreeSpecCode) (σ : List ℕ) (a : List ℕ),
        (ext (ts, σ)).eval (Encodable.encode a) =
          Part.some (Encodable.encode ((unfoldLabeledTree ts σ).label a,
            (unfoldLabeledTree ts σ).nChildren a)) := by
  let evalPacked : ℕ → List ℕ → ℕ := fun tpσ a =>
    let tp := tpσ.unpair.1
    let lbl := (unfoldStatePacked tpσ a).unpair.1 % tspL tp
    Nat.pair lbl (tspB tp)
  have heval_prim : Primrec₂ evalPacked := by
    have htp : Primrec fun q : ℕ × List ℕ => q.1.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
    have hlbl := Primrec.nat_mod.comp
      (Primrec.fst.comp (Primrec.unpair.comp primrec₂_unfoldStatePacked))
      (primrec_tspL.comp htp)
    exact primrec₂_natPair.comp hlbl (primrec_tspB.comp htp)
  obtain ⟨cNat, hcNat_comp, hcNat_spec⟩ := exists_parametric_code_nat evalPacked heval_prim.to_comp
  let packPair : TreeSpecCode × List ℕ → ℕ := fun p =>
    Nat.pair (packTS p.1) (Encodable.encode p.2)
  have hpack_prim : Primrec packPair :=
    primrec₂_natPair.comp (primrec_packTS.comp Primrec.fst) (Primrec.encode.comp Primrec.snd)
  refine ⟨fun p => cNat (packPair p), hcNat_comp.comp hpack_prim.to_comp, ?_⟩
  intro ts σ a
  rw [hcNat_spec (packPair (ts, σ)) a]
  dsimp only [evalPacked, packPair, unfoldLabeledTree, unfoldLabelNat]
  simp only [Nat.unpair_pair, tspL_pack, tspB_pack]
  rfl

/-! #### Clean Structural Equation Lemmas for `treePG` -/

lemma tspTotVerts_ge_two (tp : ℕ) : 2 ≤ tspTotVerts tp := by
  unfold tspTotVerts; dsimp only; omega

lemma treePG_card (ts : TreeSpecCode) : (treePG ts).1 + 1 = tspTotVerts (packTS ts) := by
  unfold treePG treePGPacked
  dsimp only
  have := tspTotVerts_ge_two (packTS ts)
  omega

lemma filterLtNat_eq_self {M : ℕ} {l : List ℕ} (hl : ∀ u ∈ l, u < M) :
    filterLtNat M l = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : x < M := hl x (List.mem_cons.mpr (Or.inl rfl))
    have hxs := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    unfold filterLtNat
    rw [List.flatMap_cons, if_pos hx, List.singleton_append]
    exact congrArg (x :: ·) hxs

lemma treeSuccPacked_nonempty_and_lt (tp : ℕ) {v : ℕ} (hv : v < tspTotVerts tp) :
    treeSuccPacked tp v ≠ [] ∧ ∀ u ∈ treeSuccPacked tp v, u < tspTotVerts tp := by
  unfold tspTotVerts at hv ⊢
  unfold treeSuccPacked
  dsimp only at hv ⊢
  set B := tspB tp
  set L := tspL tp
  set Q := tspQ tp
  set T := myPow L B
  have hQ_pos : 0 < Q := Nat.succ_pos _
  have hL_pos : 0 < L := Nat.succ_pos _
  by_cases hv0 : v = 0
  · rw [if_pos hv0]
    set l := (List.range L).flatMap fun a =>
      if (tspRootList tp).getD a false = true then [2 + a * Q] else []
    by_cases hl : l.length = 0
    · rw [if_pos hl]
      exact ⟨by simp, fun u hu => by simp at hu; omega⟩
    · rw [if_neg hl]
      refine ⟨fun hnil => hl (by simp [hnil]), fun u hu => ?_⟩
      simp only [l, List.mem_flatMap, List.mem_range] at hu
      rcases hu with ⟨a, ha_lt, ha_mem⟩
      split_ifs at ha_mem
      · simp only [List.mem_singleton] at ha_mem
        subst ha_mem
        have haQ : a * Q < L * Q := Nat.mul_lt_mul_of_pos_right ha_lt hQ_pos
        omega
      · simp at ha_mem
  · rw [if_neg hv0]
    by_cases hv1 : v = 1
    · rw [if_pos hv1]
      exact ⟨by simp, fun u hu => by simp at hu; omega⟩
    · rw [if_neg hv1]
      by_cases hve : v < 2 + L * Q
      · rw [if_pos hve]
        let a := (v - 2) / Q
        let q := (v - 2) % Q
        have ha_lt : a < L := (Nat.div_lt_iff_lt_mul hQ_pos).mpr (by omega)
        have hq_lt : q < Q := Nat.mod_lt _ hQ_pos
        set l := (List.range T).flatMap fun tup =>
          if tupleValidPacked (Nat.pair tp a) tup = true then [2 + L * Q + (a * T + tup) * Q + q] else []
        by_cases hl : l.length = 0
        · rw [if_pos hl]
          exact ⟨by simp, fun u hu => by simp at hu; omega⟩
        · rw [if_neg hl]
          refine ⟨fun hnil => hl (by simp [hnil]), fun u hu => ?_⟩
          simp only [l, List.mem_flatMap, List.mem_range] at hu
          rcases hu with ⟨tup, htup_lt, ht_mem⟩
          split_ifs at ht_mem
          · simp only [List.mem_singleton] at ht_mem
            subst ht_mem
            have h1 : a + 1 ≤ L := by omega
            have hat_lt : a * T + tup < L * T := by
              calc
                a * T + tup < a * T + T := by omega
                _ = (a + 1) * T := by ring
                _ ≤ L * T := Nat.mul_le_mul_right T h1
            have h2 : a * T + tup + 1 ≤ L * T := by omega
            have hprod_lt : (a * T + tup) * Q + q < L * T * Q := by
              calc
                (a * T + tup) * Q + q < (a * T + tup) * Q + Q := by omega
                _ = (a * T + tup + 1) * Q := by ring
                _ ≤ L * T * Q := Nat.mul_le_mul_right Q h2
            omega
          · simp at ht_mem
      · rw [if_neg hve]
        refine ⟨by simp [B, tspB], fun u hu => ?_⟩
        simp only [List.mem_map, List.mem_range] at hu
        rcases hu with ⟨d, _, rfl⟩
        have ha'_lt : tupleAt L (((v - (2 + L * Q)) / Q) % T) d < L := Nat.mod_lt _ hL_pos
        have hq'_lt : stepMonPacked tp (Nat.pair ((v - (2 + L * Q)) % Q)
            (Nat.pair (((v - (2 + L * Q)) / Q) / T) d)) < Q := Nat.mod_lt _ hQ_pos
        have h1 : tupleAt L (((v - (2 + L * Q)) / Q) % T) d + 1 ≤ L := by omega
        have hprod_lt : tupleAt L (((v - (2 + L * Q)) / Q) % T) d * Q +
            stepMonPacked tp (Nat.pair ((v - (2 + L * Q)) % Q)
              (Nat.pair (((v - (2 + L * Q)) / Q) / T) d)) < L * Q := by
          calc
            _ < tupleAt L (((v - (2 + L * Q)) / Q) % T) d * Q + Q := by omega
            _ = (tupleAt L (((v - (2 + L * Q)) / Q) % T) d + 1) * Q := by ring
            _ ≤ L * Q := Nat.mul_le_mul_right Q h1
        omega

lemma treePG_accessors (ts : TreeSpecCode) (v : Fin ((treePG ts).1 + 1)) :
    owner (treePG ts) v = treeOwnerPacked (packTS ts) v.val ∧
      prio (treePG ts) v = treePrioPacked (packTS ts) v.val ∧
      succNat (treePG ts) v.val = treeSuccPacked (packTS ts) v.val := by
  have hcard : (treePG ts).1 + 1 = tspTotVerts (packTS ts) := treePG_card ts
  have hv_lt : v.val < tspTotVerts (packTS ts) := by omega
  have hown : owner (treePG ts) v = treeOwnerPacked (packTS ts) v.val := by
    unfold owner treePG treePGPacked
    dsimp only
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hv_lt]), Option.getD_some]
    simp
  have hprio : prio (treePG ts) v = treePrioPacked (packTS ts) v.val := by
    unfold prio treePG treePGPacked
    dsimp only
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hv_lt]), Option.getD_some]
    simp
  have hsucc : succNat (treePG ts) v.val = treeSuccPacked (packTS ts) v.val := by
    obtain ⟨hne, hall_lt⟩ := treeSuccPacked_nonempty_and_lt (packTS ts) hv_lt
    unfold succNat
    have hget : (treePG ts).2.2.1.getD v.val [] = treeSuccPacked (packTS ts) v.val := by
      unfold treePG treePGPacked
      dsimp only
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hv_lt]), Option.getD_some]
      simp
    have hall_lt' : ∀ u ∈ treeSuccPacked (packTS ts) v.val, u < (treePG ts).1 + 1 := by
      intro u hu
      rw [hcard]
      exact hall_lt u hu
    have hfilt : filterLtNat ((treePG ts).1 + 1) (treeSuccPacked (packTS ts) v.val) =
        treeSuccPacked (packTS ts) v.val :=
      filterLtNat_eq_self hall_lt'
    dsimp only
    rw [hget, hfilt]
    have hlen_ne : (treeSuccPacked (packTS ts) v.val).length ≠ 0 :=
      fun h0 => hne (List.eq_nil_of_length_eq_zero h0)
    rw [if_neg hlen_ne]
  exact ⟨hown, hprio, hsucc⟩

lemma treeSuccPacked_zero_mem (ts : TreeSpecCode) {u : ℕ}
    (hu : u ∈ treeSuccPacked (packTS ts) 0) (hu1 : u ≠ 1) :
    ∃ a0 < ts.2.1 + 1, ts.2.2.1.getD a0 false = true ∧ u = 2 + a0 * (ts.2.2.2.2.1 + 1) := by
  unfold treeSuccPacked at hu
  simp only [↓reduceIte, tspL_pack, tspQ_pack, tspRootList_pack] at hu
  set l := (List.range (ts.2.1 + 1)).flatMap fun a =>
    if ts.2.2.1.getD a false = true then [2 + a * (ts.2.2.2.2.1 + 1)] else []
  by_cases hl : l.length = 0
  · rw [if_pos hl, List.mem_singleton] at hu
    exact False.elim (hu1 hu)
  · rw [if_neg hl] at hu
    simp only [l, List.mem_flatMap, List.mem_range] at hu
    rcases hu with ⟨a0, ha0_lt, ha0_mem⟩
    split_ifs at ha0_mem with hrok
    · simp only [List.mem_singleton] at ha0_mem
      exact ⟨a0, ha0_lt, hrok, ha0_mem⟩
    · simp at ha0_mem

lemma treeSuccPacked_eve_mem (ts : TreeSpecCode) {a q u : ℕ}
    (ha : a < ts.2.1 + 1) (hq : q < ts.2.2.2.2.1 + 1)
    (hu : u ∈ treeSuccPacked (packTS ts) (2 + a * (ts.2.2.2.2.1 + 1) + q)) (hu1 : u ≠ 1) :
    let L := ts.2.1 + 1
    let Q := ts.2.2.2.2.1 + 1
    let T := myPow L (ts.1 + 1)
    ∃ tup < T, tupleValidPacked (Nat.pair (packTS ts) a) tup = true ∧
      u = 2 + L * Q + (a * T + tup) * Q + q := by
  dsimp only
  let L := ts.2.1 + 1
  let Q := ts.2.2.2.2.1 + 1
  let T := myPow L (ts.1 + 1)
  have hQ_pos : 0 < Q := Nat.succ_pos _
  have h1 : a + 1 ≤ L := by omega
  have hlt_b : 2 + a * Q + q < 2 + L * Q := by
    calc
      2 + a * Q + q < 2 + a * Q + Q := by omega
      _ = 2 + (a + 1) * Q := by ring
      _ ≤ 2 + L * Q := by linarith [Nat.mul_le_mul_right Q h1]
  have hne0 : 2 + a * Q + q ≠ 0 := by omega
  have hne1 : 2 + a * Q + q ≠ 1 := by omega
  unfold treeSuccPacked at hu
  simp only [tspB_pack, tspL_pack, tspQ_pack] at hu
  change u ∈ (if 2 + a * Q + q = 0 then _ else if 2 + a * Q + q = 1 then _
    else if 2 + a * Q + q < 2 + L * Q then _ else _) at hu
  rw [if_neg hne0, if_neg hne1, if_pos hlt_b] at hu
  have hsub : 2 + a * Q + q - 2 = q + Q * a := by
    have h0 : 2 + a * Q + q - 2 = a * Q + q := by omega
    rw [h0]; ring
  have hdiv : (2 + a * Q + q - 2) / Q = a := by
    rw [hsub, Nat.add_mul_div_left _ _ hQ_pos, Nat.div_eq_of_lt hq, zero_add]
  have hmod : (2 + a * Q + q - 2) % Q = q := by
    rw [hsub, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hq]
  rw [hdiv, hmod] at hu
  set le := (List.range T).flatMap fun tup =>
    if tupleValidPacked (Nat.pair (packTS ts) a) tup = true
    then [2 + L * Q + (a * T + tup) * Q + q] else []
  by_cases hle0 : le.length = 0
  · rw [if_pos hle0, List.mem_singleton] at hu
    exact False.elim (hu1 hu)
  · rw [if_neg hle0] at hu
    simp only [le, List.mem_flatMap, List.mem_range] at hu
    rcases hu with ⟨tup, htup_lt, ht_mem⟩
    split_ifs at ht_mem with htok
    · simp only [List.mem_singleton] at ht_mem
      exact ⟨tup, htup_lt, htok, ht_mem⟩
    · simp at ht_mem

lemma treeSuccPacked_adam_eq (ts : TreeSpecCode) {a tup q : ℕ}
    (_ha : a < ts.2.1 + 1) (htup : tup < myPow (ts.2.1 + 1) (ts.1 + 1))
    (hq : q < ts.2.2.2.2.1 + 1) :
    let B := ts.1 + 1
    let L := ts.2.1 + 1
    let Q := ts.2.2.2.2.1 + 1
    let T := myPow L B
    treeSuccPacked (packTS ts) (2 + L * Q + (a * T + tup) * Q + q) =
      (List.range B).map fun d =>
        2 + tupleAt L tup d * Q + stepMonPacked (packTS ts) (Nat.pair q (Nat.pair a d)) := by
  dsimp only
  let B := ts.1 + 1
  let L := ts.2.1 + 1
  let Q := ts.2.2.2.2.1 + 1
  let T := myPow L B
  have hQ_pos : 0 < Q := Nat.succ_pos _
  have hT_pos : 0 < T := by
    change 0 < myPow L B; rw [myPow_eq]
    exact pow_pos (Nat.succ_pos _) B
  have hne0 : 2 + L * Q + (a * T + tup) * Q + q ≠ 0 := by omega
  have hne1 : 2 + L * Q + (a * T + tup) * Q + q ≠ 1 := by omega
  have hnlt : ¬ (2 + L * Q + (a * T + tup) * Q + q < 2 + L * Q) := by omega
  unfold treeSuccPacked
  simp only [tspB_pack, tspL_pack, tspQ_pack]
  change (if 2 + L * Q + (a * T + tup) * Q + q = 0 then _
    else if 2 + L * Q + (a * T + tup) * Q + q = 1 then _
    else if 2 + L * Q + (a * T + tup) * Q + q < 2 + L * Q then _
    else _) = _
  rw [if_neg hne0, if_neg hne1, if_neg hnlt]
  have hidx : 2 + L * Q + (a * T + tup) * Q + q - (2 + L * Q) = q + Q * (tup + T * a) := by
    have h0 : 2 + L * Q + (a * T + tup) * Q + q - (2 + L * Q) = (a * T + tup) * Q + q := by omega
    rw [h0]; ring
  have hq_c : (2 + L * Q + (a * T + tup) * Q + q - (2 + L * Q)) % Q = q := by
    rw [hidx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hq]
  have hat_c : (2 + L * Q + (a * T + tup) * Q + q - (2 + L * Q)) / Q = tup + T * a := by
    rw [hidx, Nat.add_mul_div_left _ _ hQ_pos, Nat.div_eq_of_lt hq, zero_add]
  have ha_c : ((2 + L * Q + (a * T + tup) * Q + q - (2 + L * Q)) / Q) / T = a := by
    rw [hat_c, Nat.add_mul_div_left _ _ hT_pos, Nat.div_eq_of_lt htup, zero_add]
  have ht_c : ((2 + L * Q + (a * T + tup) * Q + q - (2 + L * Q)) / Q) % T = tup := by
    rw [hat_c, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt htup]
  rw [hq_c, ha_c, ht_c]

lemma treePrioPacked_eve_eq (ts : TreeSpecCode) {a q : ℕ}
    (ha : a < ts.2.1 + 1) (hq : q < ts.2.2.2.2.1 + 1) :
    treePrioPacked (packTS ts) (2 + a * (ts.2.2.2.2.1 + 1) + q) = ts.2.2.2.2.2.2.getD q 0 := by
  let L := ts.2.1 + 1
  let Q := ts.2.2.2.2.1 + 1
  have h1 : a + 1 ≤ L := by omega
  have hlt_b : 2 + a * Q + q < 2 + L * Q := by
    calc
      2 + a * Q + q < 2 + a * Q + Q := by omega
      _ = 2 + (a + 1) * Q := by ring
      _ ≤ 2 + L * Q := by linarith [Nat.mul_le_mul_right Q h1]
  have hne0 : 2 + a * Q + q ≠ 0 := by omega
  have hne1 : 2 + a * Q + q ≠ 1 := by omega
  unfold treePrioPacked
  simp only [tspL_pack, tspQ_pack, tspPrioList_pack]
  change (if 2 + a * Q + q = 0 then _ else if 2 + a * Q + q = 1 then _
    else if 2 + a * Q + q < 2 + L * Q then _ else _) = _
  rw [if_neg hne0, if_neg hne1, if_pos hlt_b]
  have hsub : 2 + a * Q + q - 2 = q + Q * a := by
    have h0 : 2 + a * Q + q - 2 = a * Q + q := by omega
    rw [h0]; ring
  rw [hsub, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hq]

lemma treePrioPacked_adam_eq (ts : TreeSpecCode) {a tup q : ℕ}
    (hq : q < ts.2.2.2.2.1 + 1) :
    let L := ts.2.1 + 1
    let Q := ts.2.2.2.2.1 + 1
    let T := myPow L (ts.1 + 1)
    treePrioPacked (packTS ts) (2 + L * Q + (a * T + tup) * Q + q) = ts.2.2.2.2.2.2.getD q 0 := by
  dsimp only
  let L := ts.2.1 + 1
  let Q := ts.2.2.2.2.1 + 1
  let T := myPow L (ts.1 + 1)
  have hne0 : 2 + L * Q + (a * T + tup) * Q + q ≠ 0 := by omega
  have hne1 : 2 + L * Q + (a * T + tup) * Q + q ≠ 1 := by omega
  have hnlt : ¬ (2 + L * Q + (a * T + tup) * Q + q < 2 + L * Q) := by omega
  unfold treePrioPacked
  simp only [tspL_pack, tspQ_pack, tspPrioList_pack]
  change (if 2 + L * Q + (a * T + tup) * Q + q = 0 then _
    else if 2 + L * Q + (a * T + tup) * Q + q = 1 then _
    else if 2 + L * Q + (a * T + tup) * Q + q < 2 + L * Q then _ else _) = _
  rw [if_neg hne0, if_neg hne1, if_neg hnlt]
  have hsub : 2 + L * Q + (a * T + tup) * Q + q - (2 + L * Q) = q + Q * (a * T + tup) := by
    have h0 : 2 + L * Q + (a * T + tup) * Q + q - (2 + L * Q) = (a * T + tup) * Q + q := by omega
    rw [h0]; ring
  rw [hsub, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hq]

/-- A tree `t : List (Fin (ts.1 + 1)) → Fin (ts.2.1 + 1)` satisfies all local and parity
conditions of `ts`. -/
def ValidAcceptingTree (ts : TreeSpecCode)
    (t : List (Fin (ts.1 + 1)) → Fin (ts.2.1 + 1)) : Prop :=
  tsRootOk ts (t []) = true ∧
    (∀ (addr : List (Fin (ts.1 + 1))) (d : Fin (ts.1 + 1)),
      tsChildOk ts (t addr) d (t (addr ++ [d])) = true) ∧
    (∀ branch : ℕ → Fin (ts.1 + 1),
      (tsDPA ts).Accepts
        (fun n => (t (List.ofFn (fun i : Fin n => branch i.val)), branch n)))

lemma sink_unreachable_of_eve_win (g : PGCode) (z0 zSink : Fin (g.1 + 1))
    (σFin : Fin (g.1 + 1) → Fin (g.1 + 1))
    (hsink_mem : zSink ∈ succList g zSink)
    (hsink_succ : σFin zSink = zSink)
    (hsink_prio : prio g zSink = 1)
    (hwin : ∀ π : ℕ → Fin (g.1 + 1), π 0 = z0 →
      (∀ n : ℕ, π (n + 1) ∈ succList g (π n)) →
      (∀ n : ℕ, owner g (π n) = true → π (n + 1) = σFin (π n)) →
      ParityCond (fun n => prio g (π n))) :
    ∀ (k : ℕ) (prePlay : ℕ → Fin (g.1 + 1)),
      prePlay 0 = z0 →
      (∀ i < k, prePlay (i + 1) ∈ succList g (prePlay i) ∧
        (owner g (prePlay i) = true → prePlay (i + 1) = σFin (prePlay i))) →
      prePlay k ≠ zSink := by
  intro k prePlay hp0 hp_step h_eq_sink
  let π : ℕ → Fin (g.1 + 1) := fun n => if n ≤ k then prePlay n else zSink
  have hπ0 : π 0 = z0 := by simp [π, hp0]
  have hπ_step : ∀ n : ℕ, π (n + 1) ∈ succList g (π n) ∧
      (owner g (π n) = true → π (n + 1) = σFin (π n)) := by
    intro n
    by_cases hn1 : n + 1 ≤ k
    · have hn : n ≤ k := by omega
      simp only [π, hn, hn1, ↓reduceIte]
      exact hp_step n (by omega)
    · by_cases hn : n ≤ k
      · have hnk : n = k := by omega
        rw [hnk]
        have hnle : ¬ (k + 1 ≤ k) := by omega
        simp only [π, le_rfl, hnle, ↓reduceIte, h_eq_sink]
        exact ⟨hsink_mem, fun _ => hsink_succ.symm⟩
      · simp only [π, hn, hn1, ↓reduceIte]
        exact ⟨hsink_mem, fun _ => hsink_succ.symm⟩
  have heven := hwin π hπ0 (fun n => (hπ_step n).1) (fun n => (hπ_step n).2)
  have hodd : OddParityCond (fun n => prio g (π n)) := by
    refine ⟨1, odd_one, ?_, ?_⟩
    · rw [Filter.frequently_atTop]
      intro N
      refine ⟨max N (k + 1), le_max_left _ _, ?_⟩
      have hnle : ¬ (max N (k + 1) ≤ k) := by omega
      simp only [π, hnle, ↓reduceIte, hsink_prio]
    · rw [Filter.eventually_atTop]
      refine ⟨k + 1, fun n hn => ?_⟩
      have hnle : ¬ (n ≤ k) := by omega
      simp only [π, hnle, ↓reduceIte, hsink_prio]
      exact le_rfl
  exact not_parityCond_and_oddParityCond _ ⟨heven, hodd⟩

theorem solveTreePG_some_sound (ts : TreeSpecCode) (σ : List ℕ)
    (hsol : solveTreePG ts = some σ) :
    ValidAcceptingTree ts (unfoldTree ts σ) := by
  unfold solveTreePG at hsol
  let tp := packTS ts
  let tpσ := Nat.pair tp (Encodable.encode σ)
  let g := treePG ts
  have hcard : (treePG ts).1 + 1 = tspTotVerts tp := treePG_card ts
  have h2le : 2 ≤ g.1 + 1 := by
    change 2 ≤ (treePG ts).1 + 1
    rw [hcard]
    exact tspTotVerts_ge_two tp
  let z0 : Fin (g.1 + 1) := ⟨0, by omega⟩
  let zSink : Fin (g.1 + 1) := ⟨1, by omega⟩
  obtain ⟨hσ_len, hσ_lt, hleg, hwin⟩ := solvePG_some_sound g z0 σ hsol
  let σFin := stratToFin g σ
  have hσFin_val : ∀ v : Fin (g.1 + 1), (σFin v).val = σ.getD v.val 0 := by
    intro v; unfold σFin stratToFin; dsimp only; exact Nat.mod_eq_of_lt (hσ_lt v)
  have hσ_get1 : ∀ v : Fin (g.1 + 1), σ.getD v.val 1 = (σFin v).val := by
    intro v
    have hlt_len : v.val < σ.length := by omega
    rw [hσFin_val v, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hlt_len]
    rfl
  -- Reachable vertices from `z0` under `σFin` cannot equal `zSink`
  have hsink_own : owner g zSink = true := by
    rw [(treePG_accessors ts zSink).1]
    unfold treeOwnerPacked
    dsimp only [zSink]
    exact decide_eq_true (by simp only [tspL_pack, tspQ_pack]; omega)
  have hsink_self : zSink ∈ succList g zSink := by
    rw [mem_succList_iff_mem_succNat, (treePG_accessors ts zSink).2.2]
    unfold treeSuccPacked; dsimp only [zSink]; simp
  have hsink_succ : σFin zSink = zSink := by
    have hsink_mem := hleg zSink hsink_own
    rw [mem_succList_iff_mem_succNat, (treePG_accessors ts zSink).2.2] at hsink_mem
    unfold treeSuccPacked at hsink_mem
    dsimp only [zSink] at hsink_mem
    simp at hsink_mem
    exact Fin.ext hsink_mem
  have hsink_prio : prio g zSink = 1 := by
    rw [(treePG_accessors ts zSink).2.1]; rfl
  have hnot_sink := sink_unreachable_of_eve_win g z0 zSink σFin hsink_self hsink_succ hsink_prio hwin
  let B := ts.1 + 1
  let L := ts.2.1 + 1
  let Q := ts.2.2.2.2.1 + 1
  let T := myPow L B
  have hQ_pos : 0 < Q := Nat.succ_pos _
  have hL_pos : 0 < L := Nat.succ_pos _
  have hvEve_lt : ∀ a q : ℕ, a < L → q < Q → 2 + a * Q + q < g.1 + 1 := by
    intro a q ha hq
    change 2 + a * Q + q < (treePG ts).1 + 1
    rw [hcard]
    unfold tspTotVerts
    simp only [tp, tspB_pack, tspL_pack, tspQ_pack]
    have h1 : a + 1 ≤ L := by omega
    have hprod : a * Q + q < L * Q := by
      calc
        a * Q + q < a * Q + Q := by omega
        _ = (a + 1) * Q := by ring
        _ ≤ L * Q := Nat.mul_le_mul_right Q h1
    change 2 + a * Q + q < 2 + L * Q + L * T * Q
    omega
  -- Root move from `z0`
  have hz0_own : owner g z0 = true := by
    rw [(treePG_accessors ts z0).1]; unfold treeOwnerPacked; dsimp only [z0]; simp
  have hz0_ne_sink : σFin z0 ≠ zSink := by
    have hne := hnot_sink 1 (fun i => if i = 0 then z0 else σFin z0) rfl
      (fun i hi => by
        have hi0 : i = 0 := by omega
        rw [hi0]
        exact ⟨hleg z0 hz0_own, fun _ => rfl⟩)
    simpa using hne
  have hz0_mem : (σFin z0).val ∈ treeSuccPacked tp 0 := by
    rw [← (treePG_accessors ts z0).2.2, ← mem_succList_iff_mem_succNat]
    exact hleg z0 hz0_own
  obtain ⟨a0, ha0_lt, ha0_ok, ha0_val⟩ :=
    treeSuccPacked_zero_mem ts hz0_mem (fun h1 => hz0_ne_sink (Fin.ext h1))
  -- Root state of `unfoldStatePacked`
  have hstate_nil : unfoldStatePacked tpσ [] = Nat.pair a0 0 := by
    unfold unfoldStatePacked
    simp only [tpσ, tp, Nat.unpair_pair, Encodable.encodek, Option.getD_some,
      tspL_pack, tspQ_pack, List.foldl_nil]
    have hg0 : σ.getD 0 1 = 2 + a0 * Q := by
      rw [show (0 : ℕ) = z0.val from rfl, hσ_get1 z0, ha0_val]
    rw [hg0]
    have hsub : 2 + a0 * Q - 2 = a0 * Q := by omega
    rw [hsub, Nat.mul_div_cancel _ hQ_pos, Nat.mod_eq_of_lt ha0_lt]
  -- Inductive invariant along `addr : List (Fin B)`
  have hunfold_inv : ∀ (addr : List (Fin B)),
      let st := unfoldStatePacked tpσ (addr.map Fin.val)
      let a := st.unpair.1
      let q := st.unpair.2
      a < L ∧ q < Q ∧ st = Nat.pair a q ∧
      (∃ prePlay : ℕ → Fin (g.1 + 1),
        prePlay 0 = z0 ∧
        (prePlay (2 * addr.length + 1)).val = 2 + a * Q + q ∧
        (∀ i < 2 * addr.length + 1,
          prePlay (i + 1) ∈ succList g (prePlay i) ∧
          (owner g (prePlay i) = true → prePlay (i + 1) = σFin (prePlay i)))) := by
    intro addr
    induction addr using List.reverseRecOn with
    | nil =>
      dsimp only
      rw [List.map_nil, hstate_nil, Nat.unpair_pair]
      dsimp only
      refine ⟨ha0_lt, hQ_pos, rfl, fun i => if i = 0 then z0 else σFin z0, rfl, ?_, ?_⟩
      · dsimp only [Q]
        simp [ha0_val]
      · intro i hi
        simp only [List.length_nil] at hi
        have hi0 : i = 0 := by omega
        rw [hi0]
        exact ⟨hleg z0 hz0_own, fun _ => rfl⟩
    | append_singleton addr d ih =>
      dsimp only at ih
      rcases ih with ⟨ha_lt, hq_lt, hst_pair, prePlay, hp0, hp_end, hp_step⟩
      set st := unfoldStatePacked tpσ (addr.map Fin.val)
      set a := st.unpair.1
      set q := st.unpair.2
      let vE : Fin (g.1 + 1) := ⟨2 + a * Q + q, hvEve_lt a q ha_lt hq_lt⟩
      have hpre_vE : prePlay (2 * addr.length + 1) = vE := Fin.ext hp_end
      have hvE_own : owner g vE = true := by
        rw [(treePG_accessors ts vE).1]
        unfold treeOwnerPacked
        simp only [tspL_pack, tspQ_pack, decide_eq_true_eq]
        dsimp only [vE]
        change 2 + a * Q + q < 2 + L * Q
        have h1 : a + 1 ≤ L := by omega
        calc
          2 + a * Q + q < 2 + a * Q + Q := by omega
          _ = 2 + (a + 1) * Q := by ring
          _ ≤ 2 + L * Q := by linarith [Nat.mul_le_mul_right Q h1]
      have hvE_ne_sink : σFin vE ≠ zSink := by
        let extPlay : ℕ → Fin (g.1 + 1) := fun i =>
          if i ≤ 2 * addr.length + 1 then prePlay i else σFin vE
        have hne := hnot_sink (2 * addr.length + 2) extPlay (by simp [extPlay, hp0])
          (fun i hi => by
            by_cases hi_lt : i < 2 * addr.length + 1
            · have s1 : i ≤ 2 * addr.length + 1 := by omega
              have s2 : i + 1 ≤ 2 * addr.length + 1 := by omega
              simp only [extPlay, s1, s2, ↓reduceIte]
              exact hp_step i hi_lt
            · have hieq : i = 2 * addr.length + 1 := by omega
              rw [hieq]
              have hnle : ¬ (2 * addr.length + 1 + 1 ≤ 2 * addr.length + 1) := by omega
              have he1 : extPlay (2 * addr.length + 1) = vE := by simp [extPlay, hpre_vE]
              have he2 : extPlay (2 * addr.length + 1 + 1) = σFin vE := by simp [extPlay, hnle]
              rw [he1, he2]
              exact ⟨hleg vE hvE_own, fun _ => rfl⟩)
        have hnle : ¬ (2 * addr.length + 2 ≤ 2 * addr.length + 1) := by omega
        simpa [extPlay, hnle] using hne
      have hvE_mem : (σFin vE).val ∈ treeSuccPacked tp (2 + a * Q + q) := by
        have hm := hleg vE hvE_own
        rwa [mem_succList_iff_mem_succNat, (treePG_accessors ts vE).2.2] at hm
      obtain ⟨tup, htup_lt, _, hvA_val⟩ :=
        treeSuccPacked_eve_mem ts ha_lt hq_lt hvE_mem (fun h1 => hvE_ne_sink (Fin.ext h1))
      have hget1_vE : σ.getD (2 + a * Q + q) 1 = 2 + L * Q + (a * T + tup) * Q + q := by
        rw [show 2 + a * Q + q = vE.val from rfl, hσ_get1 vE, hvA_val]
      have htup_calc : ((σ.getD (2 + a * Q + q) 1 - (2 + (ts.2.1 + 1) * (ts.2.2.2.2.1 + 1))) /
          (ts.2.2.2.2.1 + 1)) % myPow (ts.2.1 + 1) (ts.1 + 1) = tup := by
        change ((σ.getD (2 + a * Q + q) 1 - (2 + L * Q)) / Q) % T = tup
        rw [hget1_vE]
        have hsub : 2 + L * Q + (a * T + tup) * Q + q - (2 + L * Q) = q + Q * (tup + T * a) := by
          have h0 : 2 + L * Q + (a * T + tup) * Q + q - (2 + L * Q) = (a * T + tup) * Q + q := by omega
          rw [h0]; ring
        rw [hsub, Nat.add_mul_div_left _ _ hQ_pos, Nat.div_eq_of_lt hq_lt, zero_add,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt htup_lt]
      have hd_mod : d.val % (ts.1 + 1) = d.val := Nat.mod_eq_of_lt d.isLt
      have hst_next : unfoldStatePacked tpσ ((addr ++ [d]).map Fin.val) =
          Nat.pair (tupleAt L tup d.val) (stepMonPacked tp (Nat.pair q (Nat.pair a d.val))) := by
        simp only [List.map_append, List.map_singleton, unfoldStatePacked, List.foldl_append,
          List.foldl_cons, List.foldl_nil]
        change unfoldStepPacked tpσ st d.val = _
        rw [hst_pair]
        unfold unfoldStepPacked
        simp only [tpσ, tp, Nat.unpair_pair, Encodable.encodek, Option.getD_some,
          tspB_pack, tspL_pack, tspQ_pack, hd_mod]
        dsimp only [L]
        rw [htup_calc]
      dsimp only
      rw [hst_next, Nat.unpair_pair]
      dsimp only
      have ha'_lt : tupleAt L tup d.val < L := Nat.mod_lt _ hL_pos
      have hq'_lt : stepMonPacked tp (Nat.pair q (Nat.pair a d.val)) < Q := by
        unfold stepMonPacked; simp only [tp, tspQ_pack]; exact Nat.mod_lt _ hQ_pos
      refine ⟨ha'_lt, hq'_lt, rfl, ?_⟩
      let vA := σFin vE
      let vE' : Fin (g.1 + 1) :=
        ⟨2 + tupleAt L tup d.val * Q + stepMonPacked tp (Nat.pair q (Nat.pair a d.val)),
          hvEve_lt _ _ ha'_lt hq'_lt⟩
      have hvA_not_eve : ¬ (owner g vA = true) := by
        rw [(treePG_accessors ts vA).1]
        unfold treeOwnerPacked
        simp only [tspL_pack, tspQ_pack, decide_eq_true_eq]
        rw [hvA_val]
        omega
      have hvE'_mem : vE' ∈ succList g vA := by
        rw [mem_succList_iff_mem_succNat, (treePG_accessors ts vA).2.2, hvA_val,
          treeSuccPacked_adam_eq ts ha_lt htup_lt hq_lt, List.mem_map]
        exact ⟨d.val, List.mem_range.mpr d.isLt, rfl⟩
      let prePlay' : ℕ → Fin (g.1 + 1) := fun i =>
        if i ≤ 2 * addr.length + 1 then prePlay i
        else if i = 2 * addr.length + 2 then vA
        else vE'
      refine ⟨prePlay', by simp [prePlay', hp0], ?_, ?_⟩
      · have hlen_app : 2 * (addr ++ [d]).length + 1 = 2 * addr.length + 3 := by simp; omega
        rw [hlen_app]
        have hn1 : ¬ (2 * addr.length + 3 ≤ 2 * addr.length + 1) := by omega
        simp [prePlay', hn1, vE']
      · intro i hi
        have hlen_app : 2 * (addr ++ [d]).length + 1 = 2 * addr.length + 3 := by simp; omega
        rw [hlen_app] at hi
        by_cases hi1 : i < 2 * addr.length + 1
        · have s1 : i ≤ 2 * addr.length + 1 := by omega
          have s2 : i + 1 ≤ 2 * addr.length + 1 := by omega
          simp only [prePlay', s1, s2, ↓reduceIte]
          exact hp_step i hi1
        · by_cases hi2 : i = 2 * addr.length + 1
          · rw [hi2]
            have hnle : ¬ (2 * addr.length + 1 + 1 ≤ 2 * addr.length + 1) := by omega
            have heq2 : 2 * addr.length + 1 + 1 = 2 * addr.length + 2 := by omega
            have he1 : prePlay' (2 * addr.length + 1) = vE := by simp [prePlay', hpre_vE]
            have he2 : prePlay' (2 * addr.length + 1 + 1) = vA := by simp [prePlay', hnle, heq2]
            rw [he1, he2]
            exact ⟨hleg vE hvE_own, fun _ => rfl⟩
          · have hi3 : i = 2 * addr.length + 2 := by omega
            rw [hi3]
            have hn1 : ¬ (2 * addr.length + 2 ≤ 2 * addr.length + 1) := by omega
            have hn2 : ¬ (2 * addr.length + 2 + 1 ≤ 2 * addr.length + 1) := by omega
            have he1 : prePlay' (2 * addr.length + 2) = vA := by simp [prePlay', hn1]
            have he2 : prePlay' (2 * addr.length + 2 + 1) = vE' := by simp [prePlay', hn2]
            rw [he1, he2]
            exact ⟨hvE'_mem, fun hown => False.elim (hvA_not_eve hown)⟩
  -- Helper extracting the child-tuple `tup` at any `addr`
  have hextract_at : ∀ addr : List (Fin B),
      let st := unfoldStatePacked tpσ (addr.map Fin.val)
      let a := st.unpair.1
      let q := st.unpair.2
      ∃ (ha : a < L) (hq : q < Q) (tup : ℕ),
        tup < T ∧
        tupleValidPacked (Nat.pair tp a) tup = true ∧
        (σFin ⟨2 + a * Q + q, hvEve_lt a q ha hq⟩).val = 2 + L * Q + (a * T + tup) * Q + q ∧
        ∀ d : Fin B, unfoldStatePacked tpσ ((addr ++ [d]).map Fin.val) =
          Nat.pair (tupleAt L tup d.val) (stepMonPacked tp (Nat.pair q (Nat.pair a d.val))) := by
    intro addr
    obtain ⟨ha_lt, hq_lt, hst_pair, prePlay, hp0, hp_end, hp_step⟩ := hunfold_inv addr
    set st := unfoldStatePacked tpσ (addr.map Fin.val)
    set a := st.unpair.1
    set q := st.unpair.2
    let vE : Fin (g.1 + 1) := ⟨2 + a * Q + q, hvEve_lt a q ha_lt hq_lt⟩
    have hpre_vE : prePlay (2 * addr.length + 1) = vE := Fin.ext hp_end
    have hvE_own : owner g vE = true := by
      rw [(treePG_accessors ts vE).1]; unfold treeOwnerPacked
      simp only [tspL_pack, tspQ_pack, decide_eq_true_eq]; dsimp only [vE]
      change 2 + a * Q + q < 2 + L * Q
      have h1 : a + 1 ≤ L := by omega
      calc
        2 + a * Q + q < 2 + a * Q + Q := by omega
        _ = 2 + (a + 1) * Q := by ring
        _ ≤ 2 + L * Q := by linarith [Nat.mul_le_mul_right Q h1]
    have hvE_ne_sink : σFin vE ≠ zSink := by
      let extPlay : ℕ → Fin (g.1 + 1) := fun i =>
        if i ≤ 2 * addr.length + 1 then prePlay i else σFin vE
      have hne := hnot_sink (2 * addr.length + 2) extPlay (by simp [extPlay, hp0])
        (fun i hi => by
          by_cases hi_lt : i < 2 * addr.length + 1
          · have s1 : i ≤ 2 * addr.length + 1 := by omega
            have s2 : i + 1 ≤ 2 * addr.length + 1 := by omega
            simp only [extPlay, s1, s2, ↓reduceIte]; exact hp_step i hi_lt
          · have hieq : i = 2 * addr.length + 1 := by omega
            rw [hieq]
            have hnle : ¬ (2 * addr.length + 1 + 1 ≤ 2 * addr.length + 1) := by omega
            have he1 : extPlay (2 * addr.length + 1) = vE := by simp [extPlay, hpre_vE]
            have he2 : extPlay (2 * addr.length + 1 + 1) = σFin vE := by simp [extPlay, hnle]
            rw [he1, he2]
            exact ⟨hleg vE hvE_own, fun _ => rfl⟩)
      have hnle : ¬ (2 * addr.length + 2 ≤ 2 * addr.length + 1) := by omega
      simpa [extPlay, hnle] using hne
    have hvE_mem : (σFin vE).val ∈ treeSuccPacked tp (2 + a * Q + q) := by
      have hm := hleg vE hvE_own
      rwa [mem_succList_iff_mem_succNat, (treePG_accessors ts vE).2.2] at hm
    obtain ⟨tup, htup_lt, htup_ok, hvA_val⟩ :=
      treeSuccPacked_eve_mem ts ha_lt hq_lt hvE_mem (fun h1 => hvE_ne_sink (Fin.ext h1))
    refine ⟨ha_lt, hq_lt, tup, htup_lt, htup_ok, hvA_val, fun d => ?_⟩
    have hget1_vE : σ.getD (2 + a * Q + q) 1 = 2 + L * Q + (a * T + tup) * Q + q := by
      rw [show 2 + a * Q + q = vE.val from rfl, hσ_get1 vE, hvA_val]
    have htup_calc : ((σ.getD (2 + a * Q + q) 1 - (2 + (ts.2.1 + 1) * (ts.2.2.2.2.1 + 1))) /
        (ts.2.2.2.2.1 + 1)) % myPow (ts.2.1 + 1) (ts.1 + 1) = tup := by
      change ((σ.getD (2 + a * Q + q) 1 - (2 + L * Q)) / Q) % T = tup
      rw [hget1_vE]
      have hsub : 2 + L * Q + (a * T + tup) * Q + q - (2 + L * Q) = q + Q * (tup + T * a) := by
        have h0 : 2 + L * Q + (a * T + tup) * Q + q - (2 + L * Q) = (a * T + tup) * Q + q := by omega
        rw [h0]; ring
      rw [hsub, Nat.add_mul_div_left _ _ hQ_pos, Nat.div_eq_of_lt hq_lt, zero_add,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt htup_lt]
    have hd_mod : d.val % (ts.1 + 1) = d.val := Nat.mod_eq_of_lt d.isLt
    simp only [List.map_append, List.map_singleton, unfoldStatePacked, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    change unfoldStepPacked tpσ st d.val = _
    rw [hst_pair]
    unfold unfoldStepPacked
    simp only [tpσ, tp, Nat.unpair_pair, Encodable.encodek, Option.getD_some,
      tspB_pack, tspL_pack, tspQ_pack, hd_mod]
    dsimp only [L]
    rw [htup_calc]
  refine ⟨?_, ?_, ?_⟩
  · -- 1. Root validity
    unfold tsRootOk unfoldTree unfoldLabelNat
    dsimp only
    rw [List.map_nil, hstate_nil, Nat.unpair_pair]
    dsimp only [L]
    rw [Nat.mod_eq_of_lt ha0_lt]
    exact ha0_ok
  · -- 2. Child validity
    intro addr d
    obtain ⟨ha_lt, _, tup, _, htup_ok, _, hstep_st⟩ := hextract_at addr
    set st := unfoldStatePacked tpσ (addr.map Fin.val)
    set a := st.unpair.1
    have hall_d : ∀ dir ∈ List.range B,
        childOkPacked tp (Nat.pair a (Nat.pair dir (tupleAt L tup dir))) = true := by
      unfold tupleValidPacked at htup_ok
      simp only [Nat.unpair_pair, tp, tspB_pack] at htup_ok
      have hstep_eq : (fun ok dir => tupleValidStep (Nat.pair (packTS ts) a) tup ok dir) =
          fun ok dir => andBool ok
            (childOkPacked (packTS ts) (Nat.pair a (Nat.pair dir (tupleAt L tup dir)))) := by
        funext ok dir
        unfold tupleValidStep
        simp only [Nat.unpair_pair, tspL_pack]
        rfl
      rw [hstep_eq] at htup_ok
      have hfold_iff : ∀ (l : List ℕ) (init : Bool),
          l.foldl (fun ok dir => andBool ok
            (childOkPacked (packTS ts) (Nat.pair a (Nat.pair dir (tupleAt L tup dir))))) init = true ↔
          init = true ∧ ∀ dir ∈ l,
            childOkPacked (packTS ts) (Nat.pair a (Nat.pair dir (tupleAt L tup dir))) = true := by
        intro l
        induction l with
        | nil => intro init; simp
        | cons x xs ih_l =>
          intro init
          rw [List.foldl_cons, ih_l]
          simp only [andBool_eq, Bool.and_eq_true, List.mem_cons]
          constructor
          · rintro ⟨⟨h1, hx⟩, hxs⟩
            refine ⟨h1, fun dir hdir => ?_⟩
            rcases hdir with rfl | hdir
            · exact hx
            · exact hxs dir hdir
          · rintro ⟨h1, hall⟩
            exact ⟨⟨h1, hall x (Or.inl rfl)⟩, fun dir hdir => hall dir (Or.inr hdir)⟩
      exact ((hfold_iff (List.range B) true).mp htup_ok).2
    have hd_ok := hall_d d.val (List.mem_range.mpr d.isLt)
    unfold childOkPacked at hd_ok
    simp only [Nat.unpair_pair, tp, tspChildList_pack, tspB_pack, tspL_pack] at hd_ok
    unfold tsChildOk unfoldTree unfoldLabelNat
    dsimp only
    change ts.2.2.2.1.getD (((a % L) * B + d.val) * L +
      (unfoldStatePacked tpσ ((addr ++ [d]).map Fin.val)).unpair.1 % L) false = true
    have htup_mod : tupleAt L tup d.val % L = tupleAt L tup d.val :=
      Nat.mod_eq_of_lt (Nat.mod_lt _ hL_pos)
    rw [hstep_st d, Nat.unpair_pair]
    dsimp only
    rw [Nat.mod_eq_of_lt ha_lt, htup_mod]
    exact hd_ok
  · -- 3. Branch acceptance
    intro branch
    let prefAddr : ℕ → List (Fin B) := fun k => List.ofFn (fun i : Fin k => branch i.val)
    let stAt : ℕ → ℕ := fun k => unfoldStatePacked tpσ ((prefAddr k).map Fin.val)
    have hrun_eq : ∀ k : ℕ,
        (stAt k).unpair.2 = ((tsDPA ts).run (fun n => (unfoldTree ts σ (prefAddr n), branch n)) k).val := by
      intro k
      induction k with
      | zero =>
        simp only [stAt, prefAddr, List.ofFn_zero, List.map_nil, DPA.run, tsDPA]
        rw [hstate_nil, Nat.unpair_pair]
      | succ k ih_k =>
        have hpref_succ : prefAddr (k + 1) = prefAddr k ++ [branch k] := by
          simp only [prefAddr, List.ofFn_succ', List.concat_eq_append]
          rfl
        obtain ⟨ha_lt, _, _, _, _, _, hstep_st⟩ := hextract_at (prefAddr k)
        have ha_lt' : (stAt k).unpair.1 < L := ha_lt
        have hst_k1 : stAt (k + 1) = unfoldStatePacked tpσ ((prefAddr k ++ [branch k]).map Fin.val) := by
          dsimp only [stAt]; rw [hpref_succ]
        rw [hst_k1, hstep_st (branch k), Nat.unpair_pair]
        unfold stepMonPacked
        simp only [Nat.unpair_pair, tp, tspTransList_pack, tspL_pack, tspB_pack, tspQ_pack]
        have hut_val : (unfoldTree ts σ (prefAddr k)).val = (stAt k).unpair.1 := by
          unfold unfoldTree unfoldLabelNat
          dsimp only
          exact Nat.mod_eq_of_lt ha_lt'
        have hrhs : ((tsDPA ts).run (fun n => (unfoldTree ts σ (prefAddr n), branch n)) (k + 1)).val =
            (ts.2.2.2.2.2.1.getD ((((tsDPA ts).run (fun n => (unfoldTree ts σ (prefAddr n), branch n)) k).val *
              (ts.2.1 + 1) + (unfoldTree ts σ (prefAddr k)).val) * (ts.1 + 1) + (branch k).val) 0) %
              (ts.2.2.2.2.1 + 1) := rfl
        rw [hrhs, ← ih_k, hut_val]
    let vEveAt : ℕ → Fin (g.1 + 1) := fun k =>
      ⟨2 + (stAt k).unpair.1 * Q + (stAt k).unpair.2,
        hvEve_lt _ _ (hunfold_inv (prefAddr k)).1 (hunfold_inv (prefAddr k)).2.1⟩
    let π : ℕ → Fin (g.1 + 1) := fun n =>
      if n = 0 then z0
      else if (n - 1) % 2 = 0 then vEveAt ((n - 1) / 2)
      else σFin (vEveAt ((n - 1) / 2))
    have hπ_even : ∀ k : ℕ, π (2 * k + 1) = vEveAt k := by
      intro k
      have hne0 : 2 * k + 1 ≠ 0 := by omega
      have hrem : (2 * k + 1 - 1) % 2 = 0 := by omega
      have hdiv : (2 * k + 1 - 1) / 2 = k := by omega
      dsimp only [π]
      rw [if_neg hne0, if_pos hrem, hdiv]
    have hπ_odd : ∀ k : ℕ, π (2 * k + 2) = σFin (vEveAt k) := by
      intro k
      have hne0 : 2 * k + 2 ≠ 0 := by omega
      have hrem : ¬ ((2 * k + 2 - 1) % 2 = 0) := by omega
      have hdiv : (2 * k + 2 - 1) / 2 = k := by omega
      dsimp only [π]
      rw [if_neg hne0, if_neg hrem, hdiv]
    have hπ0 : π 0 = z0 := rfl
    have hπ_step : ∀ n : ℕ, π (n + 1) ∈ succList g (π n) ∧
        (owner g (π n) = true → π (n + 1) = σFin (π n)) := by
      intro n
      by_cases hn0 : n = 0
      · rw [hn0, hπ0, show (0 : ℕ) + 1 = 2 * 0 + 1 by omega, hπ_even 0]
        have hvE0 : vEveAt 0 = σFin z0 := by
          apply Fin.ext
          simp only [vEveAt, stAt, prefAddr, List.ofFn_zero, List.map_nil]
          rw [hstate_nil, Nat.unpair_pair, ha0_val, Nat.add_zero]
        rw [hvE0]
        exact ⟨hleg z0 hz0_own, fun _ => rfl⟩
      · let k := (n - 1) / 2
        have hcases : n = 2 * k + 1 ∨ n = 2 * k + 2 := by omega
        rcases hcases with h1 | h2
        · rw [h1, hπ_even k, show 2 * k + 1 + 1 = 2 * k + 2 by omega, hπ_odd k]
          have hown_k : owner g (vEveAt k) = true := by
            rw [(treePG_accessors ts (vEveAt k)).1]; unfold treeOwnerPacked
            simp only [tspL_pack, tspQ_pack, decide_eq_true_eq]; dsimp only [vEveAt]
            change 2 + (stAt k).unpair.1 * Q + (stAt k).unpair.2 < 2 + L * Q
            have ha_lt : (stAt k).unpair.1 < L := (hunfold_inv (prefAddr k)).1
            have hq_lt : (stAt k).unpair.2 < Q := (hunfold_inv (prefAddr k)).2.1
            have h1' : (stAt k).unpair.1 + 1 ≤ L := by omega
            calc
              2 + (stAt k).unpair.1 * Q + (stAt k).unpair.2 < 2 + (stAt k).unpair.1 * Q + Q := by omega
              _ = 2 + ((stAt k).unpair.1 + 1) * Q := by ring
              _ ≤ 2 + L * Q := by linarith [Nat.mul_le_mul_right Q h1']
          exact ⟨hleg (vEveAt k) hown_k, fun _ => rfl⟩
        · rw [h2, hπ_odd k, show 2 * k + 2 + 1 = 2 * (k + 1) + 1 by omega, hπ_even (k + 1)]
          obtain ⟨ha_lt, hq_lt, tup, htup_lt, _, hvA_val, hstep_st⟩ := hextract_at (prefAddr k)
          have hvA_not_eve : ¬ (owner g (σFin (vEveAt k)) = true) := by
            rw [(treePG_accessors ts (σFin (vEveAt k))).1]; unfold treeOwnerPacked
            simp only [tspL_pack, tspQ_pack, decide_eq_true_eq]
            change ¬ ((σFin ⟨2 + (stAt k).unpair.1 * Q + (stAt k).unpair.2, _⟩).val < 2 + L * Q)
            rw [hvA_val]; omega
          refine ⟨?_, fun hown => False.elim (hvA_not_eve hown)⟩
          rw [mem_succList_iff_mem_succNat, (treePG_accessors ts (σFin (vEveAt k))).2.2]
          change (vEveAt (k + 1)).val ∈ treeSuccPacked tp (σFin ⟨2 + (stAt k).unpair.1 * Q + (stAt k).unpair.2, _⟩).val
          rw [hvA_val, treeSuccPacked_adam_eq ts ha_lt htup_lt hq_lt, List.mem_map]
          refine ⟨(branch k).val, List.mem_range.mpr (branch k).isLt, ?_⟩
          have hpref_succ : prefAddr (k + 1) = prefAddr k ++ [branch k] := by
            simp only [prefAddr, List.ofFn_succ', List.concat_eq_append]
            rfl
          have hst_k1 : stAt (k + 1) = unfoldStatePacked tpσ ((prefAddr k ++ [branch k]).map Fin.val) := by
            dsimp only [stAt]; rw [hpref_succ]
          dsimp only [vEveAt]
          rw [hst_k1, hstep_st (branch k), Nat.unpair_pair]
    have hwin_π := hwin π hπ0 (fun n => (hπ_step n).1) (fun n => (hπ_step n).2)
    unfold DPA.Accepts
    apply (parityCond_double_step (fun n => prio g (π n)) _ ?_).mp hwin_π
    intro k
    obtain ⟨ha_lt, hq_lt, tup, _, _, hvA_val, _⟩ := hextract_at (prefAddr k)
    constructor
    · rw [hπ_even k, (treePG_accessors ts (vEveAt k)).2.1]
      change treePrioPacked (packTS ts) (2 + (stAt k).unpair.1 * Q + (stAt k).unpair.2) = _
      rw [treePrioPacked_eve_eq ts ha_lt hq_lt, hrun_eq k]
      rfl
    · rw [hπ_odd k, (treePG_accessors ts (σFin (vEveAt k))).2.1]
      change treePrioPacked (packTS ts) (σFin ⟨2 + (stAt k).unpair.1 * Q + (stAt k).unpair.2, _⟩).val = _
      rw [hvA_val, treePrioPacked_adam_eq ts hq_lt, hrun_eq k]
      rfl

theorem solveTreePG_iff_exists_tree (ts : TreeSpecCode) :
    solveTreePG ts ≠ none ↔
      ∃ t : List (Fin (ts.1 + 1)) → Fin (ts.2.1 + 1), ValidAcceptingTree ts t := by
  classical
  constructor
  · intro hne
    cases hsol : solveTreePG ts with
    | none => exact False.elim (hne hsol)
    | some σ => exact ⟨unfoldTree ts σ, solveTreePG_some_sound ts σ hsol⟩
  · rintro ⟨t, hroot, hchild, hacc⟩ hnone
    unfold solveTreePG at hnone
    let tp := packTS ts
    let g := treePG ts
    have hcard : (treePG ts).1 + 1 = tspTotVerts tp := treePG_card ts
    have h2le : 2 ≤ (treePG ts).1 + 1 := by rw [hcard]; exact tspTotVerts_ge_two tp
    let z0 : Fin (g.1 + 1) := ⟨0, by omega⟩
    obtain ⟨τ, hleg_τ, hwin_τ⟩ := solvePG_none_adam g z0 hnone
    let B := ts.1 + 1
    let L := ts.2.1 + 1
    let Q := ts.2.2.2.2.1 + 1
    let T := myPow L B
    have hL_pos : 0 < L := Nat.succ_pos _
    have hex_tup : ∀ addr : List (Fin B),
        ∃ tup < T, ∀ d : Fin B, tupleAt L tup d.val = (t (addr ++ [d])).val := by
      intro addr
      obtain ⟨c, hc_lt, hc_eq⟩ := exists_code_of_finFun hL_pos B (fun d => t (addr ++ [d]))
      refine ⟨c, ?_, ?_⟩
      · change c < myPow L B; rw [myPow_eq]; exact hc_lt
      · intro d; unfold tupleAt; rw [myPow_eq]; exact hc_eq d
    let tupOf : List (Fin B) → ℕ := fun addr => (hex_tup addr).choose
    have htup_lt : ∀ addr : List (Fin B), tupOf addr < T :=
      fun addr => (hex_tup addr).choose_spec.1
    have htup_at : ∀ (addr : List (Fin B)) (d : Fin B),
        tupleAt L (tupOf addr) d.val = (t (addr ++ [d])).val :=
      fun addr d => (hex_tup addr).choose_spec.2 d
    have htup_valid : ∀ addr : List (Fin B),
        tupleValidPacked (Nat.pair tp (t addr).val) (tupOf addr) = true := by
      intro addr
      unfold tupleValidPacked
      simp only [Nat.unpair_pair, tp, tspB_pack]
      have hfold_ok : ∀ l : List ℕ, (∀ d ∈ l, d < B) →
          l.foldl (fun ok d => tupleValidStep (Nat.pair (packTS ts) (t addr).val) (tupOf addr) ok d) true = true := by
        intro l hl
        induction l with
        | nil => rfl
        | cons d ds ih =>
          have hd : d < B := hl d (List.mem_cons.mpr (Or.inl rfl))
          let df : Fin B := ⟨d, hd⟩
          have hd_ok : childOkPacked (packTS ts)
              (Nat.pair (t addr).val (Nat.pair d (tupleAt L (tupOf addr) d))) = true := by
            unfold childOkPacked
            simp only [Nat.unpair_pair, tspChildList_pack, tspB_pack, tspL_pack]
            rw [htup_at addr df]
            exact hchild addr df
          have hstep_d : tupleValidStep (Nat.pair (packTS ts) (t addr).val) (tupOf addr) true d = true := by
            unfold tupleValidStep
            simp only [Nat.unpair_pair, tspL_pack]
            change andBool true (childOkPacked (packTS ts)
              (Nat.pair (t addr).val (Nat.pair d (tupleAt L (tupOf addr) d)))) = true
            rw [hd_ok]
            rfl
          rw [List.foldl_cons, hstep_d]
          exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      exact hfold_ok (List.range B) (fun _ hd => List.mem_range.mp hd)
    have hvEve_lt : ∀ (a : Fin L) (q : Fin Q), 2 + a.val * Q + q.val < g.1 + 1 := by
      intro a q
      change 2 + a.val * Q + q.val < (treePG ts).1 + 1
      rw [hcard]; unfold tspTotVerts; simp only [tp, tspB_pack, tspL_pack, tspQ_pack]
      have h1 : a.val + 1 ≤ L := by omega
      have hp : a.val * Q + q.val < L * Q := by
        calc
          a.val * Q + q.val < a.val * Q + Q := by omega
          _ = (a.val + 1) * Q := by ring
          _ ≤ L * Q := Nat.mul_le_mul_right Q h1
      change 2 + a.val * Q + q.val < 2 + L * Q + L * T * Q
      omega
    have hvAdam_lt : ∀ (a : Fin L) (tup : ℕ) (_ : tup < T) (q : Fin Q),
        2 + L * Q + (a.val * T + tup) * Q + q.val < g.1 + 1 := by
      intro a tup ht q
      change 2 + L * Q + (a.val * T + tup) * Q + q.val < (treePG ts).1 + 1
      rw [hcard]; unfold tspTotVerts; simp only [tp, tspB_pack, tspL_pack, tspQ_pack]
      have h1 : a.val + 1 ≤ L := by omega
      have hat : a.val * T + tup < L * T := by
        calc
          a.val * T + tup < a.val * T + T := by omega
          _ = (a.val + 1) * T := by ring
          _ ≤ L * T := Nat.mul_le_mul_right T h1
      have h2 : a.val * T + tup + 1 ≤ L * T := by omega
      have hp : (a.val * T + tup) * Q + q.val < L * T * Q := by
        calc
          (a.val * T + tup) * Q + q.val < (a.val * T + tup) * Q + Q := by omega
          _ = (a.val * T + tup + 1) * Q := by ring
          _ ≤ L * T * Q := Nat.mul_le_mul_right Q h2
      change 2 + L * Q + (a.val * T + tup) * Q + q.val < 2 + L * Q + L * T * Q
      omega
    let vAdamOf : List (Fin B) → Fin Q → Fin (g.1 + 1) := fun addr q =>
      ⟨2 + L * Q + ((t addr).val * T + tupOf addr) * Q + q.val,
        hvAdam_lt (t addr) (tupOf addr) (htup_lt addr) q⟩
    have hadam_dir : ∀ (addr : List (Fin B)) (q : Fin Q),
        owner g (vAdamOf addr q) = false ∧
        ∃ d : Fin B,
          (τ (vAdamOf addr q)).val =
            2 + (t (addr ++ [d])).val * Q + ((tsDPA ts).step q (t addr, d)).val := by
      intro addr q
      have hown_f : owner g (vAdamOf addr q) = false := by
        rw [(treePG_accessors ts (vAdamOf addr q)).1]
        unfold treeOwnerPacked
        simp only [tspL_pack, tspQ_pack, decide_eq_false_iff_not, vAdamOf]
        change ¬ (2 + L * Q + ((t addr).val * T + tupOf addr) * Q + q.val < 2 + L * Q)
        omega
      refine ⟨hown_f, ?_⟩
      have hmem := hleg_τ (vAdamOf addr q) hown_f
      rw [mem_succList_iff_mem_succNat, (treePG_accessors ts (vAdamOf addr q)).2.2] at hmem
      change (τ (vAdamOf addr q)).val ∈
        treeSuccPacked (packTS ts) (2 + L * Q + ((t addr).val * T + tupOf addr) * Q + q.val) at hmem
      rw [treeSuccPacked_adam_eq ts (t addr).isLt (htup_lt addr) q.isLt, List.mem_map] at hmem
      rcases hmem with ⟨d, hd_range, hd_eq⟩
      let df : Fin B := ⟨d, List.mem_range.mp hd_range⟩
      refine ⟨df, ?_⟩
      rw [← hd_eq, htup_at addr df]
      unfold stepMonPacked tsDPA
      simp [Nat.unpair_pair, B, Q, df]
    let stepAQ : List (Fin B) × Fin Q → List (Fin B) × Fin Q := fun aq =>
      let d := (hadam_dir aq.1 aq.2).2.choose
      (aq.1 ++ [d], (tsDPA ts).step aq.2 (t aq.1, d))
    let seqAQ : ℕ → List (Fin B) × Fin Q := fun k =>
      Nat.rec ([], (tsDPA ts).init) (fun _ prev => stepAQ prev) k
    let branch : ℕ → Fin B := fun k => (hadam_dir (seqAQ k).1 (seqAQ k).2).2.choose
    have hseq_pref : ∀ k : ℕ, (seqAQ k).1 = List.ofFn (fun i : Fin k => branch i.val) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        change (seqAQ k).1 ++ [branch k] = _
        rw [List.ofFn_succ', List.concat_eq_append, ← ih]
    have hseq_run : ∀ k : ℕ,
        (seqAQ k).2 = (tsDPA ts).run (fun n => (t (List.ofFn (fun i : Fin n => branch i.val)), branch n)) k := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        change (tsDPA ts).step (seqAQ k).2 (t (seqAQ k).1, branch k) = _
        rw [ih, hseq_pref k]; rfl
    let vEveSeq : ℕ → Fin (g.1 + 1) := fun k =>
      ⟨2 + (t (seqAQ k).1).val * Q + (seqAQ k).2.val, hvEve_lt _ _⟩
    let vAdamSeq : ℕ → Fin (g.1 + 1) := fun k => vAdamOf (seqAQ k).1 (seqAQ k).2
    let π : ℕ → Fin (g.1 + 1) := fun n =>
      if n = 0 then z0
      else if (n - 1) % 2 = 0 then vEveSeq ((n - 1) / 2)
      else vAdamSeq ((n - 1) / 2)
    have hπ_even : ∀ k : ℕ, π (2 * k + 1) = vEveSeq k := by
      intro k
      have hne0 : 2 * k + 1 ≠ 0 := by omega
      have hrem : (2 * k + 1 - 1) % 2 = 0 := by omega
      have hdiv : (2 * k + 1 - 1) / 2 = k := by omega
      dsimp only [π]; rw [if_neg hne0, if_pos hrem, hdiv]
    have hπ_odd : ∀ k : ℕ, π (2 * k + 2) = vAdamSeq k := by
      intro k
      have hne0 : 2 * k + 2 ≠ 0 := by omega
      have hrem : ¬ ((2 * k + 2 - 1) % 2 = 0) := by omega
      have hdiv : (2 * k + 2 - 1) / 2 = k := by omega
      dsimp only [π]; rw [if_neg hne0, if_neg hrem, hdiv]
    have hπ0 : π 0 = z0 := rfl
    have hπ_succ_con : ∀ n : ℕ,
        π (n + 1) ∈ succList g (π n) ∧ (owner g (π n) = false → π (n + 1) = τ (π n)) := by
      intro n
      by_cases hn0 : n = 0
      · rw [hn0, hπ0, show (0 : ℕ) + 1 = 2 * 0 + 1 by omega, hπ_even 0]
        have hz0_own : owner g z0 = true := by
          rw [(treePG_accessors ts z0).1]; unfold treeOwnerPacked; dsimp only [z0]; simp
        refine ⟨?_, fun hf => by rw [hz0_own] at hf; cases hf⟩
        have hv0_val : (vEveSeq 0).val = 2 + (t []).val * Q := Nat.add_zero _
        rw [mem_succList_iff_mem_succNat, (treePG_accessors ts z0).2.2, hv0_val]
        unfold treeSuccPacked
        dsimp only [z0]
        simp only [↓reduceIte, tspL_pack, tspQ_pack, tspRootList_pack]
        set l0 := (List.range L).flatMap fun a =>
          if ts.2.2.1.getD a false = true then [2 + a * Q] else []
        have hmem_l0 : 2 + (t []).val * Q ∈ l0 := by
          simp only [l0, List.mem_flatMap, List.mem_range]
          refine ⟨(t []).val, (t []).isLt, ?_⟩
          have hr : ts.2.2.1.getD (t []).val false = true := hroot
          rw [hr]
          simp
        have hl0_ne : l0.length ≠ 0 :=
          fun h0 => by rw [List.eq_nil_of_length_eq_zero h0] at hmem_l0; cases hmem_l0
        rw [if_neg hl0_ne]
        exact hmem_l0
      · let k := (n - 1) / 2
        have hcases : n = 2 * k + 1 ∨ n = 2 * k + 2 := by omega
        rcases hcases with h1 | h2
        · rw [h1, hπ_even k, show 2 * k + 1 + 1 = 2 * k + 2 by omega, hπ_odd k]
          have hown_e : owner g (vEveSeq k) = true := by
            rw [(treePG_accessors ts (vEveSeq k)).1]; unfold treeOwnerPacked
            simp only [tspL_pack, tspQ_pack, decide_eq_true_eq]; dsimp only [vEveSeq]
            change 2 + (t (seqAQ k).1).val * Q + (seqAQ k).2.val < 2 + L * Q
            have h1' : (t (seqAQ k).1).val + 1 ≤ L := by omega
            calc
              2 + (t (seqAQ k).1).val * Q + (seqAQ k).2.val < 2 + (t (seqAQ k).1).val * Q + Q := by omega
              _ = 2 + ((t (seqAQ k).1).val + 1) * Q := by ring
              _ ≤ 2 + L * Q := by linarith [Nat.mul_le_mul_right Q h1']
          refine ⟨?_, fun hf => by rw [hown_e] at hf; cases hf⟩
          rw [mem_succList_iff_mem_succNat, (treePG_accessors ts (vEveSeq k)).2.2]
          unfold treeSuccPacked
          simp only [tspB_pack, tspL_pack, tspQ_pack]
          dsimp only [vEveSeq]
          have hQ_pos : 0 < Q := Nat.succ_pos _
          have h1' : (t (seqAQ k).1).val + 1 ≤ L := by omega
          have hlt_b : 2 + (t (seqAQ k).1).val * Q + (seqAQ k).2.val < 2 + L * Q := by
            calc
              2 + (t (seqAQ k).1).val * Q + (seqAQ k).2.val < 2 + (t (seqAQ k).1).val * Q + Q := by omega
              _ = 2 + ((t (seqAQ k).1).val + 1) * Q := by ring
              _ ≤ 2 + L * Q := by linarith [Nat.mul_le_mul_right Q h1']
          have hne0' : 2 + (t (seqAQ k).1).val * Q + (seqAQ k).2.val ≠ 0 := by omega
          have hne1' : 2 + (t (seqAQ k).1).val * Q + (seqAQ k).2.val ≠ 1 := by omega
          change (vAdamSeq k).val ∈
            (if 2 + (t (seqAQ k).1).val * Q + (seqAQ k).2.val = 0 then _
             else if 2 + (t (seqAQ k).1).val * Q + (seqAQ k).2.val = 1 then _
             else if 2 + (t (seqAQ k).1).val * Q + (seqAQ k).2.val < 2 + L * Q then _ else _)
          rw [if_neg hne0', if_neg hne1', if_pos hlt_b]
          have hsub : 2 + (t (seqAQ k).1).val * Q + (seqAQ k).2.val - 2 =
              (seqAQ k).2.val + Q * (t (seqAQ k).1).val := by
            have h0 : 2 + (t (seqAQ k).1).val * Q + (seqAQ k).2.val - 2 =
                (t (seqAQ k).1).val * Q + (seqAQ k).2.val := by omega
            rw [h0]; ring
          have ha_c : (2 + (t (seqAQ k).1).val * Q + (seqAQ k).2.val - 2) / Q = (t (seqAQ k).1).val := by
            rw [hsub, Nat.add_mul_div_left _ _ hQ_pos, Nat.div_eq_of_lt (seqAQ k).2.isLt, zero_add]
          have hq_c : (2 + (t (seqAQ k).1).val * Q + (seqAQ k).2.val - 2) % Q = (seqAQ k).2.val := by
            rw [hsub, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (seqAQ k).2.isLt]
          rw [ha_c, hq_c]
          set le := (List.range T).flatMap fun tup =>
            if tupleValidPacked (Nat.pair (packTS ts) (t (seqAQ k).1).val) tup = true
            then [2 + L * Q + ((t (seqAQ k).1).val * T + tup) * Q + (seqAQ k).2.val] else []
          have hmem_le : (vAdamSeq k).val ∈ le := by
            simp only [le, List.mem_flatMap, List.mem_range]
            refine ⟨tupOf (seqAQ k).1, htup_lt (seqAQ k).1, ?_⟩
            rw [if_pos (htup_valid (seqAQ k).1)]
            exact List.mem_singleton.mpr rfl
          have hle_ne : le.length ≠ 0 :=
            fun h0 => by rw [List.eq_nil_of_length_eq_zero h0] at hmem_le; cases hmem_le
          rw [if_neg hle_ne]
          exact hmem_le
        · rw [h2, hπ_odd k, show 2 * k + 2 + 1 = 2 * (k + 1) + 1 by omega, hπ_even (k + 1)]
          have hown_f := (hadam_dir (seqAQ k).1 (seqAQ k).2).1
          have hτ_eq : vEveSeq (k + 1) = τ (vAdamSeq k) := by
            apply Fin.ext
            rw [(hadam_dir (seqAQ k).1 (seqAQ k).2).2.choose_spec]
          rw [hτ_eq]
          exact ⟨hleg_τ (vAdamSeq k) hown_f, fun _ => rfl⟩
    have hnot_even := hwin_τ π hπ0 (fun n => (hπ_succ_con n).1) (fun n => (hπ_succ_con n).2)
    have heven_branch := hacc branch
    unfold DPA.Accepts at heven_branch
    apply hnot_even
    apply (parityCond_double_step (fun n => prio g (π n)) _ ?_).mpr heven_branch
    intro k
    constructor
    · rw [hπ_even k, (treePG_accessors ts (vEveSeq k)).2.1]
      change treePrioPacked (packTS ts) (2 + (t (seqAQ k).1).val * Q + (seqAQ k).2.val) = _
      rw [treePrioPacked_eve_eq ts (t (seqAQ k).1).isLt (seqAQ k).2.isLt, hseq_run k]
      rfl
    · rw [hπ_odd k, (treePG_accessors ts (vAdamSeq k)).2.1]
      change treePrioPacked (packTS ts)
        (2 + L * Q + ((t (seqAQ k).1).val * T + tupOf (seqAQ k).1) * Q + (seqAQ k).2.val) = _
      rw [treePrioPacked_adam_eq ts (seqAQ k).2.isLt, hseq_run k]
      rfl

end DistLTLSynth.Char.Thm34ParityGameAux

open DistLTLSynth.Char DistLTLSynth.Char.Thm34ParityGameAux in
theorem solution :
    ∃ (solveTreePG : DistLTLSynth.Char.TreeSpecCode → Option (List ℕ))
      (packTS : DistLTLSynth.Char.TreeSpecCode → ℕ)
      (unfoldLabelPacked : ℕ → List ℕ → ℕ),
      Primrec solveTreePG ∧
      Primrec packTS ∧
      Primrec₂ unfoldLabelPacked ∧
      (∀ (ts : DistLTLSynth.Char.TreeSpecCode) (σ : List ℕ),
        solveTreePG ts = some σ →
          DistLTLSynth.Char.ValidAcceptingTree ts (fun addr =>
            ⟨(unfoldLabelPacked (Nat.pair (packTS ts) (Encodable.encode σ)) (addr.map Fin.val)) % (ts.2.1 + 1),
              Nat.mod_lt _ (Nat.succ_pos _)⟩)) ∧
      (∀ (ts : DistLTLSynth.Char.TreeSpecCode),
        solveTreePG ts ≠ none ↔
          ∃ t : List (Fin (ts.1 + 1)) → Fin (ts.2.1 + 1), DistLTLSynth.Char.ValidAcceptingTree ts t) :=
  ⟨Thm34ParityGameAux.solveTreePG,
   Thm34ParityGameAux.packTS,
   fun tpσ addr => (Thm34ParityGameAux.unfoldStatePacked tpσ addr).unpair.1,
   Thm34ParityGameAux.primrec_solveTreePG,
   Thm34ParityGameAux.primrec_packTS,
   Primrec.fst.comp (Primrec.unpair.comp Thm34ParityGameAux.primrec₂_unfoldStatePacked),
   fun ts σ hsol => Thm34ParityGameAux.solveTreePG_some_sound ts σ hsol,
   fun ts => Thm34ParityGameAux.solveTreePG_iff_exists_tree ts⟩
