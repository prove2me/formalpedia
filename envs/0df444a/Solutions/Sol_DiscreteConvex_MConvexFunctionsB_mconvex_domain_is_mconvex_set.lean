-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsB.mconvex_domain_is_mconvex_set
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T06:18:18.45569+00:00
-- url     : https://prove2.me/submissions/34794280-5e7b-4364-b7dc-0175a614730d

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_ExchangeAxiomB

set_option autoImplicit false

namespace P85d7bb66

open DiscreteConvex.MConvexFunctionsB

lemma dom_exchange {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) :
    ExchangeAxiomB (DomZ f) := by
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

lemma const_sum {V : Type*} [Fintype V] [DecidableEq V] (B : Set (V → ℤ))
    (hB : ExchangeAxiomB B) :
    ∀ n : ℕ, ∀ x ∈ B, ∀ y ∈ B, ∑ w, |x w - y w| < (n : ℤ) → ∑ w, x w = ∑ w, y w := by
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

end P85d7bb66

open DiscreteConvex.MConvexFunctionsB in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) :
    ExchangeAxiomB (DomZ f) ∧ ∃ r : ℤ, ∀ x ∈ DomZ f, ∑ v, x v = r := by
  have hB := P85d7bb66.dom_exchange f hf
  refine ⟨hB, ?_⟩
  by_cases hne : (DomZ f).Nonempty
  · obtain ⟨x0, hx0⟩ := hne
    refine ⟨∑ v, x0 v, fun x hx => ?_⟩
    have h0 : (0 : ℤ) ≤ ∑ w, |x w - x0 w| := Finset.sum_nonneg (fun w _ => abs_nonneg _)
    exact P85d7bb66.const_sum _ hB ((∑ w, |x w - x0 w|).toNat + 1) x hx x0 hx0
      (by push_cast; rw [Int.toNat_of_nonneg h0]; omega)
  · refine ⟨0, fun x hx => absurd ⟨x, hx⟩ hne⟩
