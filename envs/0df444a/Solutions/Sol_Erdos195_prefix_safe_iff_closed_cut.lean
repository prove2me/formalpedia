-- Prove2me | solution 1 for Erdos195.prefix_safe_iff_closed_cut
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T01:22:57.577492+00:00
-- url     : https://prove2.me/submissions/c5786bbb-841d-4165-aa0e-52c30a579e52

import Mathlib
import Definitions.Def_Erdos195_defs


/-!
# Erdős Problem 195 — definitions

* `Erdos195.ListIsAPOfLengthWith`, `Erdos195.ListIsAPOfLength`, `Erdos195.HasMonotoneAP`:
  verbatim copies of `List.IsAPOfLengthWith`, `List.IsAPOfLength`, `HasMonotoneAP` from
  google-deepmind/formal-conjectures (`FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`).
* `Erdos195.bitOne`, `Erdos195.epsLt`: the ε-orders on ℤ (2-adic lexicographic orders).
* `Erdos195.compLt`, `Erdos195.Safe`: completion of a finite word and Ho's notion of safety.
* `Erdos195.No3AP`, `Erdos195.Star`: the two order axioms used in Ho's argument.
-/

namespace E195Aux

/-- List version of an arithmetic progression of length `l` with first term `a` and difference
`d`, listed either forwards or backwards (formal-conjectures `List.IsAPOfLengthWith`). -/
def ListIsAPOfLengthWith {α : Type*} [AddCommMonoid α] (s : List α) (l : ℕ) (a d : α) : Prop :=
  s = (List.range l).map (fun n ↦ a + n • d) ∨ s = (List.range l).reverse.map (fun n ↦ a + n • d)

/-- `s` is an arithmetic progression of length `l` (formal-conjectures `List.IsAPOfLength`). -/
def ListIsAPOfLength {α : Type*} [AddCommMonoid α] (s : List α) (l : ℕ) : Prop :=
  ∃ a d : α, ListIsAPOfLengthWith s l a d

/-- `f` has a monotone `k`-term AP: indices `b₁ < ⋯ < b_k` with `f b₁, …, f b_k` an increasing or
decreasing AP (formal-conjectures `HasMonotoneAP`). -/
def HasMonotoneAP {α β : Type*} [AddCommMonoid α] [Preorder β] (f : β → α) (k : ℕ) : Prop :=
  ∃ l : List β, ListIsAPOfLength (l.map f) k ∧ l.Pairwise (· < ·)

/-- The `k`-th two's-complement binary digit of `x` equals `1`. -/
def bitOne (x : ℤ) (k : ℕ) : Prop := x / 2 ^ k % 2 = 1

/-- The ε-order on ℤ: `x ≺_ε y` iff `x ≠ y` and, at the lowest binary position `k = ν₂(y - x)`
where `x` and `y` differ, the digit of `x` is `1` exactly when `ε k = true`. -/
def epsLt (ε : ℕ → Bool) (x y : ℤ) : Prop :=
  x ≠ y ∧ (bitOne x (padicValInt 2 (y - x)) ↔ ε (padicValInt 2 (y - x)) = true)

/-- The order of the completion `C(P)` of a finite word `P`: elements of `P` first, in list
order, then every other integer, ordered by `R`. -/
def compLt (R : ℤ → ℤ → Prop) (P : List ℤ) (x y : ℤ) : Prop :=
  (x ∈ P ∧ y ∈ P ∧ P.idxOf x < P.idxOf y) ∨ (x ∈ P ∧ y ∉ P) ∨ (x ∉ P ∧ y ∉ P ∧ R x y)

/-- `P` is safe for `R`: the completion order contains no monotone 4-term AP. -/
def Safe (R : ℤ → ℤ → Prop) (P : List ℤ) : Prop :=
  ∀ a r : ℤ, r ≠ 0 →
    ¬ (compLt R P a (a + r) ∧ compLt R P (a + r) (a + 2 * r) ∧ compLt R P (a + 2 * r) (a + 3 * r))

/-- `R` has no monotone 3-term AP. -/
def No3AP (R : ℤ → ℤ → Prop) : Prop :=
  ∀ a r : ℤ, r ≠ 0 → ¬ (R a (a + r) ∧ R (a + r) (a + 2 * r))

/-- Ho's identity (*): `a ≺ a + r ↔ a + 2r ≺ a + 3r`. -/
def Star (R : ℤ → ℤ → Prop) : Prop :=
  ∀ a r : ℤ, r ≠ 0 → (R a (a + r) ↔ R (a + 2 * r) (a + 3 * r))

theorem hasAP4_of' (f : ℕ → ℤ) (i j k l : ℕ) (a d : ℤ) (hij : i < j) (hjk : j < k) (hkl : k < l)
    (hi : f i = a) (hj : f j = a + d) (hk : f k = a + 2 * d) (hl : f l = a + 3 * d) :
    HasMonotoneAP f 4 := by
  refine ⟨[i, j, k, l], ⟨a, d, Or.inl ?_⟩, ?_⟩
  · simp [List.range_succ, hi, hj, hk, hl]
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨by omega, by omega, by omega⟩, ⟨by omega, by omega⟩, hkl, fun _ h => h.elim⟩

theorem mem_pref (f : ℕ ≃ ℤ) (N : ℕ) (x : ℤ) :
    x ∈ (List.range N).map f ↔ f.symm x < N := by
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; simpa using hi
  · intro h; exact ⟨f.symm x, h, by simp⟩

theorem idx_pref (f : ℕ ≃ ℤ) (N : ℕ) (x : ℤ) (h : f.symm x < N) :
    ((List.range N).map f).idxOf x = f.symm x := by
  have hnd : ((List.range N).map f).Nodup := List.Nodup.map f.injective List.nodup_range
  have hlen : f.symm x < ((List.range N).map f).length := by simpa using h
  have hget : ((List.range N).map f)[f.symm x]'hlen = x := by simp
  have := List.Nodup.idxOf_getElem hnd (f.symm x) hlen
  rw [hget] at this
  exact this

theorem compLt_pref (R : ℤ → ℤ → Prop) (f : ℕ ≃ ℤ) (N : ℕ) (x y : ℤ) :
    compLt R ((List.range N).map f) x y ↔
      (f.symm x < N ∧ f.symm y < N ∧ f.symm x < f.symm y) ∨ (f.symm x < N ∧ N ≤ f.symm y) ∨
      (N ≤ f.symm x ∧ N ≤ f.symm y ∧ R x y) := by
  unfold compLt
  simp only [mem_pref, not_lt]
  constructor
  · rintro (⟨h1, h2, h3⟩ | h | h)
    · rw [idx_pref f N x h1, idx_pref f N y h2] at h3; exact Or.inl ⟨h1, h2, h3⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (⟨h1, h2, h3⟩ | h | h)
    · refine Or.inl ⟨h1, h2, ?_⟩; rw [idx_pref f N x h1, idx_pref f N y h2]; exact h3
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

/-- **Safe prefixes of a 4AP-free permutation ("closed cuts").** Let `R` be a relation on `ℤ` with
no monotone 3-AP and Ho's property (*), and let `f : ℕ ≃ ℤ` have no monotone 4-AP. Then the
prefix `f 0, …, f (N-1)` is an `R`-safe word iff the cut at `N` is `R`-closed: whenever `i < j < N`,
`R (f i) (f j)` and `2 f j - f i` occurs at a position `≥ N`, the value `3 f j - 2 f i` occurs
at a position `< N`. Hence a Ho-type construction (prefix chain of `R`-safe words exhausting `ℤ`)
is the same thing as a 4AP-free permutation with infinitely many `R`-closed cuts. -/
theorem prefix_safe_iff_closed_cut (R : ℤ → ℤ → Prop) (hA : No3AP R) (hB : Star R)
    (f : ℕ ≃ ℤ) (hf : ¬ HasMonotoneAP f 4) (N : ℕ) :
    Safe R ((List.range N).map f) ↔
      ∀ i j : ℕ, i < j → j < N → R (f i) (f j) → N ≤ f.symm (2 * f j - f i) →
        f.symm (3 * f j - 2 * f i) < N := by
  constructor
  · intro hS i j hij hjN hR h2
    by_contra h3
    push Not at h3
    have hne : f j - f i ≠ 0 := by
      intro h; have := f.injective (show f j = f i by linarith); omega
    apply hS (f i) (f j - f i) hne
    have e1 : f i + (f j - f i) = f j := by ring
    have e2 : f i + 2 * (f j - f i) = 2 * f j - f i := by ring
    have e3 : f i + 3 * (f j - f i) = 3 * f j - 2 * f i := by ring
    rw [e1, e2, e3, compLt_pref, compLt_pref, compLt_pref]
    simp only [Equiv.symm_apply_apply]
    refine ⟨Or.inl ⟨by omega, hjN, hij⟩, Or.inr (Or.inl ⟨hjN, h2⟩), Or.inr (Or.inr ⟨h2, h3, ?_⟩)⟩
    have := (hB (f i) (f j - f i) hne).1
    rw [e1, e2, e3] at this
    exact this hR
  · intro H a r hr ⟨h1, h2, h3⟩
    rw [compLt_pref] at h1 h2 h3
    set p0 := f.symm a with hp0
    set p1 := f.symm (a + r) with hp1
    set p2 := f.symm (a + 2 * r) with hp2
    set p3 := f.symm (a + 3 * r) with hp3
    have f0 : f p0 = a := by simp [hp0]
    have f1 : f p1 = a + r := by simp [hp1]
    have f2 : f p2 = a + 2 * r := by simp [hp2]
    have f3 : f p3 = a + 3 * r := by simp [hp3]
    have ap : ∀ (_ : p0 < p1) (_ : p1 < p2) (_ : p2 < p3), False := fun q1 q2 q3 =>
      hf (hasAP4_of' f p0 p1 p2 p3 a r q1 q2 q3 f0 f1 f2 f3)
    rcases h1 with ⟨a1, a2, a3⟩ | ⟨a1, a2⟩ | ⟨a1, a2, a3⟩
    · rcases h2 with ⟨b1, b2, b3⟩ | ⟨b1, b2⟩ | ⟨b1, b2, b3⟩
      · rcases h3 with ⟨c1, c2, c3⟩ | ⟨c1, c2⟩ | ⟨c1, c2, c3⟩
        · exact ap a3 b3 c3
        · exact ap a3 b3 (by omega)
        · omega
      · rcases h3 with ⟨c1, c2, c3⟩ | ⟨c1, c2⟩ | ⟨c1, c2, c3⟩
        · omega
        · omega
        · have hR : R (f p0) (f p1) := by
            rw [f0, f1]
            have := (hB a r hr).2 c3
            exact this
          have hq2 : f.symm (2 * f p1 - f p0) = p2 := by
            rw [f0, f1, hp2]; congr 1; ring
          have hq3 : f.symm (3 * f p1 - 2 * f p0) = p3 := by
            rw [f0, f1, hp3]; congr 1; ring
          have := H p0 p1 a3 b1 hR (by rw [hq2]; exact b2)
          rw [hq3] at this
          omega
      · omega
    · rcases h2 with ⟨b1, b2, b3⟩ | ⟨b1, b2⟩ | ⟨b1, b2, b3⟩
      · omega
      · omega
      · rcases h3 with ⟨c1, c2, c3⟩ | ⟨c1, c2⟩ | ⟨c1, c2, c3⟩
        · omega
        · omega
        · apply hA (a + r) r hr
          have e1 : a + r + r = a + 2 * r := by ring
          have e2 : a + r + 2 * r = a + 3 * r := by ring
          rw [e1, e2]
          exact ⟨b3, c3⟩
    · rcases h2 with ⟨b1, b2, b3⟩ | ⟨b1, b2⟩ | ⟨b1, b2, b3⟩
      · omega
      · omega
      · exact hA a r hr ⟨a3, b3⟩

end E195Aux



open Erdos195 in
theorem solution (R : ℤ → ℤ → Prop) (hA : No3AP R) (hB : Star R)
    (f : ℕ ≃ ℤ) (hf : ¬ HasMonotoneAP f 4) (N : ℕ) :
    Safe R ((List.range N).map f) ↔
      ∀ i j : ℕ, i < j → j < N → R (f i) (f j) → N ≤ f.symm (2 * f j - f i) →
        f.symm (3 * f j - 2 * f i) < N :=
  E195Aux.prefix_safe_iff_closed_cut R hA hB f hf N
