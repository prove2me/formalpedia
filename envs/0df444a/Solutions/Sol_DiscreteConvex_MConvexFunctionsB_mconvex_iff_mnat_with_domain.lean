-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsB.mconvex_iff_mnat_with_domain
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T05:53:21.49968+00:00
-- url     : https://prove2.me/submissions/0edd413c-83a1-4c38-b19f-6024687bf87d

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ

set_option autoImplicit false

namespace P191cc676

open DiscreteConvex.MConvexFunctionsB

lemma dom_exch {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) :
    ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
      (fun w => x w - CharVec u w + CharVec v w) ∈ DomZ f ∧
      (fun w => y w + CharVec u w - CharVec v w) ∈ DomZ f := by
  intro x hx y hy u hu
  obtain ⟨v, hv, hle⟩ := hf x hx y hy u hu
  refine ⟨v, hv, ?_⟩
  have hxy : f x + f y ≠ ⊤ := by
    rw [Ne, WithTop.add_eq_top, not_or]; exact ⟨hx, hy⟩
  have h2 := ne_top_of_le_ne_top hxy hle
  rw [Ne, WithTop.add_eq_top, not_or] at h2
  exact ⟨h2.1, h2.2⟩

lemma sum_move {V : Type*} [Fintype V] [DecidableEq V] (x : V → ℤ) (u v : V) :
    ∑ w, (x w - CharVec u w + CharVec v w) = ∑ w, x w := by
  simp [CharVec, Finset.sum_add_distrib, Finset.sum_sub_distrib]

lemma sum_move' {V : Type*} [Fintype V] [DecidableEq V] (x : V → ℤ) (u v : V) :
    ∑ w, (x w + CharVec u w - CharVec v w) = ∑ w, x w := by
  simp [CharVec, Finset.sum_add_distrib, Finset.sum_sub_distrib]

lemma dist_move {V : Type*} [Fintype V] [DecidableEq V] (x y : V → ℤ) (u v : V)
    (hu : y u < x u) (hv : x v < y v) :
    ∑ w, |(x w - CharVec u w + CharVec v w) - y w| < ∑ w, |x w - y w| := by
  have huv : u ≠ v := by
    rintro rfl; omega
  apply Finset.sum_lt_sum
  · intro w _
    rcases abs_cases (x w - y w) with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rw [h3] <;> apply abs_le.mpr <;>
      simp only [CharVec] <;> split_ifs with h1 h2 <;> subst_vars <;> constructor <;> omega
  · refine ⟨u, Finset.mem_univ _, ?_⟩
    rcases abs_cases (x u - y u) with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rw [h3] <;> apply abs_lt.mpr <;>
      simp only [CharVec] <;> split_ifs with h1 h2 <;> subst_vars <;> constructor <;> omega

lemma const_sum {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (hf : MExchangeAxiom f) :
    ∀ n : ℕ, ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, ∑ w, |x w - y w| < (n : ℤ) →
      ∑ w, x w = ∑ w, y w := by
  have hB := dom_exch f hf
  intro n
  induction n with
  | zero =>
    intro x _ y _ h
    exact absurd h (not_lt.mpr (Finset.sum_nonneg (fun w _ => abs_nonneg _)))
  | succ n ih =>
    intro x hx y hy h
    by_cases hp : (SuppPos x y).Nonempty
    · obtain ⟨u, hu⟩ := hp
      obtain ⟨v, hv, hx', _⟩ := hB x hx y hy u hu
      have hu' : y u < x u := by simpa [SuppPos] using hu
      have hv' : x v < y v := by simpa [SuppNeg] using hv
      have hd := dist_move x y u v hu' hv'
      have := ih _ hx' y hy (by push_cast at h; omega)
      rw [← this, sum_move]
    · by_cases hq : (SuppPos y x).Nonempty
      · obtain ⟨u, hu⟩ := hq
        obtain ⟨v, hv, hy', _⟩ := hB y hy x hx u hu
        have hu' : x u < y u := by simpa [SuppPos] using hu
        have hv' : y v < x v := by simpa [SuppNeg] using hv
        have hd := dist_move y x u v hu' hv'
        have hsym : ∑ w, |y w - x w| = ∑ w, |x w - y w| := by
          refine Finset.sum_congr rfl (fun w _ => abs_sub_comm _ _)
        have := ih _ hy' x hx (by push_cast at h; omega)
        rw [sum_move] at this
        exact this.symm
      · have hxy : x = y := by
          funext w
          rw [Finset.not_nonempty_iff_eq_empty] at hp hq
          have h1 : w ∉ SuppPos x y := by rw [hp]; simp
          have h2 : w ∉ SuppPos y x := by rw [hq]; simp
          simp [SuppPos] at h1 h2
          omega
        rw [hxy]

lemma msum {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (hf : MExchangeAxiom f) (x : V → ℤ) (hx : x ∈ DomZ f) (y : V → ℤ) (hy : y ∈ DomZ f) :
    ∑ w, x w = ∑ w, y w := by
  have h0 : (0 : ℤ) ≤ ∑ w, |x w - y w| := Finset.sum_nonneg (fun w _ => abs_nonneg _)
  exact const_sum f hf ((∑ w, |x w - y w|).toNat + 1) x hx y hy
    (by push_cast; rw [Int.toNat_of_nonneg h0]; omega)

lemma exists_sum {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (hf : MExchangeAxiom f) : ∃ r : ℤ, ∀ x ∈ DomZ f, ∑ v, x v = r := by
  by_cases hne : (DomZ f).Nonempty
  · obtain ⟨x0, hx0⟩ := hne
    exact ⟨∑ v, x0 v, fun x hx => msum f hf x hx x0 hx0⟩
  · exact ⟨0, fun x hx => absurd ⟨x, hx⟩ hne⟩

lemma lift_eval {V : Type*} [Fintype V] (f : (V → ℤ) → WithTop ℝ) (X : Option V → ℤ)
    (h : X none = -(∑ v : V, X (some v))) :
    LiftedFunction f X = f (fun v => X (some v)) := by
  unfold LiftedFunction; rw [if_pos h]

lemma lift_dom {V : Type*} [Fintype V] (f : (V → ℤ) → WithTop ℝ) (X : Option V → ℤ)
    (hX : X ∈ DomZ (LiftedFunction f)) :
    X none = -(∑ v : V, X (some v)) ∧ (fun v => X (some v)) ∈ DomZ f := by
  unfold DomZ LiftedFunction at *
  simp only [Set.mem_setOf_eq] at *
  split_ifs at hX with h
  · exact ⟨h, hX⟩
  · exact absurd rfl hX

lemma cv_some {V : Type*} [DecidableEq V] (u w : V) :
    CharVec (some u) (some w) = CharVec u w := by
  simp [CharVec]

lemma cv_none {V : Type*} [DecidableEq V] (u : V) :
    CharVec (some u) (none : Option V) = 0 := by
  simp [CharVec]

lemma lift_move {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (X : Option V → ℤ) (h : X none = -(∑ v : V, X (some v))) (u v : V) :
    LiftedFunction f (fun w => X w - CharVec (some u) w + CharVec (some v) w) =
      f (fun w => X (some w) - CharVec u w + CharVec v w) := by
  rw [lift_eval f _ ?_]
  · simp only [cv_some]
  · simp only [cv_none, cv_some, sub_zero, add_zero]
    rw [sum_move (fun w => X (some w)) u v]
    exact h

lemma lift_move' {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (X : Option V → ℤ) (h : X none = -(∑ v : V, X (some v))) (u v : V) :
    LiftedFunction f (fun w => X w + CharVec (some u) w - CharVec (some v) w) =
      f (fun w => X (some w) + CharVec u w - CharVec v w) := by
  rw [lift_eval f _ ?_]
  · simp only [cv_some]
  · simp only [cv_none, cv_some, sub_zero, add_zero]
    rw [sum_move' (fun w => X (some w)) u v]
    exact h

lemma part1 {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (hf : MExchangeAxiom f) : MNaturalConvex f := by
  unfold MNaturalConvex
  intro X hX Y hY u hu
  obtain ⟨hX0, hx⟩ := lift_dom f X hX
  obtain ⟨hY0, hy⟩ := lift_dom f Y hY
  have hs := msum f hf _ hx _ hy
  cases u with
  | none =>
    simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rw [hX0, hY0, hs] at hu
    exact absurd hu (lt_irrefl _)
  | some u =>
    have hu' : u ∈ SuppPos (fun v => X (some v)) (fun v => Y (some v)) := by
      simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      exact hu
    obtain ⟨v, hv, hle⟩ := hf _ hx _ hy u hu'
    refine ⟨some v, ?_, ?_⟩
    · simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact hv
    · rw [lift_eval f X hX0, lift_eval f Y hY0, lift_move f X hX0 u v, lift_move' f Y hY0 u v]
      exact hle

lemma part2 {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (hn : MNaturalConvex f) (r : ℤ) (hr : ∀ x ∈ DomZ f, ∑ v, x v = r) :
    MExchangeAxiom f := by
  intro x hx y hy u hu
  let X : Option V → ℤ := fun o => o.elim (-r) x
  let Y : Option V → ℤ := fun o => o.elim (-r) y
  have hX0 : X none = -(∑ v : V, X (some v)) := by
    show -r = -(∑ v : V, x v)
    rw [hr x hx]
  have hY0 : Y none = -(∑ v : V, Y (some v)) := by
    show -r = -(∑ v : V, y v)
    rw [hr y hy]
  have hX : X ∈ DomZ (LiftedFunction f) := by
    show LiftedFunction f X ≠ ⊤
    rw [lift_eval f X hX0]; exact hx
  have hY : Y ∈ DomZ (LiftedFunction f) := by
    show LiftedFunction f Y ≠ ⊤
    rw [lift_eval f Y hY0]; exact hy
  have hu' : some u ∈ SuppPos X Y := by
    simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact hu
  obtain ⟨v', hv', hle⟩ := hn X hX Y hY (some u) hu'
  cases v' with
  | none =>
    simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hv'
    exact absurd hv' (lt_irrefl _)
  | some v =>
    refine ⟨v, ?_, ?_⟩
    · simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hv' ⊢
      exact hv'
    · rw [lift_eval f X hX0, lift_eval f Y hY0, lift_move f X hX0 u v,
        lift_move' f Y hY0 u v] at hle
      exact hle

end P191cc676

open DiscreteConvex.MConvexFunctionsB in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) :
    (MExchangeAxiom f → MNaturalConvex f) ∧
    (MNaturalConvex f → (MExchangeAxiom f ↔ ∃ r : ℤ, ∀ x ∈ DomZ f, ∑ v, x v = r)) := by
  refine ⟨fun hf => P191cc676.part1 f hf, fun hn => ⟨fun hf => P191cc676.exists_sum f hf, ?_⟩⟩
  rintro ⟨r, hr⟩
  exact P191cc676.part2 f hn r hr
