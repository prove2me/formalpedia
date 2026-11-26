-- Prove2me | solution 1 for Erdos287.consecutive_omissions_from_residue_mass_intervals
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T06:39:08.334561+00:00
-- url     : https://prove2.me/submissions/bfa6e0d3-fca8-4867-9f60-ca3d75d643e0

import Mathlib

open Finset

set_option autoImplicit false

private def mergeBounds (a b : Option (ℕ × ℕ)) : Option (ℕ × ℕ) :=
  match a, b with
  | none, b => b
  | a, none => a
  | some a, some b => some (min a.1 b.1, max a.2 b.2)

private def shiftBounds (w : ℕ) (a : Option (ℕ × ℕ)) : Option (ℕ × ℕ) :=
  a.map (fun i => (w + i.1, w + i.2))

private def InBounds (a : Option (ℕ × ℕ)) (w : ℕ) : Prop :=
  ∃ l u, a = some (l, u) ∧ l ≤ w ∧ w ≤ u

private theorem in_merge_left {a b : Option (ℕ × ℕ)} {w : ℕ} (h : InBounds a w) :
    InBounds (mergeBounds a b) w := by
  obtain ⟨l, u, rfl, hl, hu⟩ := h
  cases b with
  | none => exact ⟨l, u, rfl, hl, hu⟩
  | some p => exact ⟨min l p.1, max u p.2, rfl, (min_le_left _ _).trans hl,
      hu.trans (le_max_left _ _)⟩

private theorem in_merge_right {a b : Option (ℕ × ℕ)} {w : ℕ} (h : InBounds b w) :
    InBounds (mergeBounds a b) w := by
  obtain ⟨l, u, rfl, hl, hu⟩ := h
  cases a with
  | none => exact ⟨l, u, rfl, hl, hu⟩
  | some p => exact ⟨min p.1 l, max p.2 u, rfl, (min_le_right _ _).trans hl,
      hu.trans (le_max_right _ _)⟩

private theorem in_shift {a : Option (ℕ × ℕ)} {u v : ℕ} (h : InBounds a v) :
    InBounds (shiftBounds u a) (u + v) := by
  obtain ⟨l, h, rfl, hl, hu⟩ := h
  exact ⟨u + l, u + h, rfl, Nat.add_le_add_left hl _, Nat.add_le_add_left hu _⟩

private def intervalStep {G : Type} [AddCommGroup G] (H R : Finset ℕ) (w : ℕ → G)
    (c : ℕ → ℕ) (n : ℕ)
    (s : Option ℕ × (G → Option (ℕ × ℕ)) × (G → Option (ℕ × ℕ))) :
    Option ℕ × (G → Option (ℕ × ℕ)) × (G → Option (ℕ × ℕ)) :=
  (some n,
    fun g => if n ∈ H then none else
      shiftBounds (c n) (mergeBounds (s.2.1 (g - w n)) (s.2.2 (g - w n))),
    fun g => if n ∈ R then none else
      if s.1 = some (n + 1) then s.2.1 g else mergeBounds (s.2.1 g) (s.2.2 g))

private def emptyBounds {G : Type} [Zero G] [DecidableEq G] (g : G) : Option (ℕ × ℕ) :=
  if g = 0 then some (0, 0) else none

private theorem interval_scan_sound {G : Type} [AddCommGroup G] [DecidableEq G]
    (H R D : Finset ℕ) (w : ℕ → G) (c : ℕ → ℕ)
    (hD : Disjoint D H) (hR : R ⊆ D) (m M : ℕ)
    (hnext : ∀ n, m ≤ n → n + 1 ≤ M → n ∉ D → n + 1 ∈ D)
    (xs : List ℕ) (hspan : ∀ n ∈ xs, m ≤ n ∧ n ≤ M) :
    let s := xs.foldr (intervalStep H R w c) (none, emptyBounds, emptyBounds)
    let u := (xs.map fun n => if n ∈ D then w n else 0).sum
    let v := (xs.map fun n => if n ∈ D then c n else 0).sum
    s.1 = xs.head? ∧ InBounds (mergeBounds (s.2.1 u) (s.2.2 u)) v ∧
      (∀ n, xs.head? = some n → n ∈ D → InBounds (s.2.1 u) v) := by
  induction xs with
  | nil => simp [emptyBounds, mergeBounds, InBounds]
  | cons n xs ih =>
    let s := xs.foldr (intervalStep H R w c) (none, emptyBounds, emptyBounds)
    let t := intervalStep H R w c n s
    let u := (xs.map fun n => if n ∈ D then w n else 0).sum
    let v := (xs.map fun n => if n ∈ D then c n else 0).sum
    let x := (if n ∈ D then w n else 0) + u
    let y := (if n ∈ D then c n else 0) + v
    have ⟨hs, hmass, hfirst⟩ := ih fun j hj => hspan j (List.mem_cons_of_mem n hj)
    change s.1 = xs.head? at hs
    change InBounds (mergeBounds (s.2.1 u) (s.2.2 u)) v at hmass
    change ∀ k, xs.head? = some k → k ∈ D → InBounds (s.2.1 u) v at hfirst
    change t.1 = some n ∧ InBounds (mergeBounds (t.2.1 x) (t.2.2 x)) y ∧
      (∀ k, some n = some k → k ∈ D → InBounds (t.2.1 x) y)
    have hkept (hn : n ∈ D) : InBounds (t.2.1 x) y := by
      have hh := disjoint_left.mp hD hn
      have hx : x - w n = u := by simp [x, hn, add_comm (w n) u]
      simpa only [t, intervalStep, if_neg hh, hx, y, if_pos hn] using in_shift (u := c n) hmass
    refine ⟨rfl, ?_, ?_⟩
    · by_cases hn : n ∈ D
      · exact in_merge_left (hkept hn)
      · apply in_merge_right
        have hnR : n ∉ R := fun h => hn (hR h)
        simp only [t, intervalStep, if_neg hnR, x, y, if_neg hn, zero_add]
        by_cases hsuc : s.1 = some (n + 1)
        · rw [if_pos hsuc]
          have hhead := hs.symm.trans hsuc
          have hmem : n + 1 ∈ xs := List.mem_of_mem_head? (by rw [hhead]; simp)
          exact hfirst (n + 1) hhead (hnext n (hspan n (by simp)).1
            (hspan (n + 1) (List.mem_cons_of_mem n hmem)).2 hn)
        · rwa [if_neg hsuc]
    · intro k hk hDk
      have he := Option.some.inj hk
      subst k
      exact hkept hDk

private theorem list_sum_to_finset {G : Type} [AddCommMonoid G]
    (w : ℕ → G) (xs : List ℕ) (hx : xs.Nodup) :
    (xs.map w).sum = ∑ n ∈ xs.toFinset, w n := by
  induction xs with
  | nil => simp
  | cons n xs ih =>
    obtain ⟨hn, hu⟩ := List.nodup_cons.mp hx
    have hmem : n ∉ xs.toFinset := by simpa using hn
    simp only [List.map_cons, List.sum_cons, List.toFinset_cons]
    rw [sum_insert hmem, ih hu]

/-- A residue-specific interval test excludes an exact unit reciprocal sum
whenever the target residue cannot reach the target mass. -/
theorem solution (D H R : Finset ℕ) (m M C q : ℕ)
    (hpos : ∀ n ∈ D, 0 < n) (hdiv : ∀ n ∈ D, n ∣ C)
    (hH : Disjoint D H) (hR : R ⊆ D)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1) (xs : List ℕ) (hxs : xs.Nodup)
    (hcover : D ⊆ xs.toFinset) (hspan : ∀ n ∈ xs, m ≤ n ∧ n ≤ M)
    (hcert :
      let merge (a b : Option (ℕ × ℕ)) := match a, b with
        | none, b => b
        | a, none => a
        | some a, some b => some (min a.1 b.1, max a.2 b.2)
      let start (g : ZMod q) := if g = 0 then some (0, 0) else none
      let s := xs.foldr
        (fun n (s : Option ℕ × (ZMod q → Option (ℕ × ℕ)) × (ZMod q → Option (ℕ × ℕ))) =>
          (some n,
            fun g => if n ∈ H then none else
              (merge (s.2.1 (g - (C / n : ℕ))) (s.2.2 (g - (C / n : ℕ)))).map
                (fun i => (C / n + i.1, C / n + i.2)),
            fun g => if n ∈ R then none else
              if s.1 = some (n + 1) then s.2.1 g else merge (s.2.1 g) (s.2.2 g)))
        (none, start, start)
      match merge (s.2.1 (C : ZMod q)) (s.2.2 (C : ZMod q)) with
      | none => True
      | some i => C < i.1 ∨ i.2 < C) :
    ∃ n, m ≤ n ∧ n + 1 ≤ M ∧ n ∉ D ∧ n + 1 ∉ D := by
  by_contra hno
  have hnext (n : ℕ) (hl : m ≤ n) (hr : n + 1 ≤ M) (hn : n ∉ D) : n + 1 ∈ D := by
    by_contra hh
    exact hno ⟨n, hl, hr, hn, hh⟩
  let c (n : ℕ) := C / n
  let w (n : ℕ) := (c n : ZMod q)
  let s := xs.foldr (intervalStep H R w c) (none, emptyBounds, emptyBounds)
  let mass := ∑ n ∈ D, c n
  have hscaled : (C : ℚ) * (∑ n ∈ D, (1 : ℚ) / n) = (mass : ℚ) := by
    rw [mul_sum, show (mass : ℚ) = ∑ n ∈ D, (c n : ℚ) by simp only [mass, Nat.cast_sum]]
    refine sum_congr rfl fun n hn => ?_
    rw [mul_one_div]
    apply (div_eq_iff (Nat.cast_ne_zero.mpr (hpos n hn).ne')).mpr
    exact_mod_cast (Nat.div_mul_cancel (hdiv n hn)).symm
  have hmass : mass = C := by
    rw [hsum, mul_one] at hscaled
    exact_mod_cast hscaled.symm
  have hset : xs.toFinset.filter (fun n => n ∈ D) = D := by
    ext n
    exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨hcover h, h⟩⟩
  have hlist : (xs.map fun n => if n ∈ D then c n else 0).sum = C := by
    rw [list_sum_to_finset _ xs hxs, ← sum_filter, hset]
    exact hmass
  have hres : (xs.map fun n => if n ∈ D then w n else 0).sum = (C : ZMod q) := by
    rw [list_sum_to_finset _ xs hxs, ← sum_filter, hset]
    change (∑ n ∈ D, (c n : ZMod q)) = (C : ZMod q)
    rw [← Nat.cast_sum]
    exact congrArg (fun k : ℕ => (k : ZMod q)) hmass
  have h := (interval_scan_sound H R D w c hH hR m M hnext xs hspan).2.1
  change InBounds (mergeBounds (s.2.1 _) (s.2.2 _)) _ at h
  rw [hlist, hres] at h
  change (match mergeBounds (s.2.1 (C : ZMod q)) (s.2.2 (C : ZMod q)) with
    | none => True
    | some i => C < i.1 ∨ i.2 < C) at hcert
  obtain ⟨l, u, he, hl, hu⟩ := h
  rw [he] at hcert
  exact hcert.elim (not_lt_of_ge hl) (not_lt_of_ge hu)

