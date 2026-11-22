-- Prove2me | solution 1 for CriticalPortraits.Cycle.cycle_lemma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:27:52.94018+00:00
-- url     : https://prove2.me/submissions/4d04131a-f6f1-4c38-bab5-769f031f9362

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_CycleLemma
public import Theorems.Thm_CriticalPortraits_Cycle_Q_periodic

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits CriticalPortraits.Cycle
variable {n : ℕ}
namespace CriticalPortraits.Cycle
theorem _root_.solution (a : ℕ → ℤ) (hn : 0 < n) (hper : ∀ k, a (k + n) = a k)
    (hsum : Q a n = 1) : ∃! i, i < n ∧ Good n a i := by
  classical
  have hne : (Finset.range n).Nonempty := Finset.nonempty_range_iff.mpr hn.ne'
  obtain ⟨i0, hi0r, hi0min⟩ := Finset.exists_min_image (Finset.range n) (Q a) hne
  -- the last argmin (max index among minimizers)
  set S := (Finset.range n).filter (fun i => Q a i = Q a i0) with hSdef
  have hSne : S.Nonempty := ⟨i0, Finset.mem_filter.mpr ⟨hi0r, rfl⟩⟩
  set istar := S.max' hSne with hist
  have histS : istar ∈ S := Finset.max'_mem _ _
  have histrange : istar < n := Finset.mem_range.mp (Finset.filter_subset _ _ histS)
  have histeq : Q a istar = Q a i0 := (Finset.mem_filter.mp histS).2
  have hMle : ∀ t, t < n → Q a istar ≤ Q a t := by
    intro t ht; rw [histeq]; exact hi0min t (Finset.mem_range.mpr ht)
  -- existence: istar is good
  have hGoodStar : Good n a istar := by
    intro t hlt hlt2
    rcases lt_or_ge t n with htn | htn
    · have hle : Q a istar ≤ Q a t := hMle t htn
      rcases eq_or_lt_of_le hle with heq | hlt3
      · exfalso
        have hQt : Q a t = Q a i0 := by rw [← heq]; exact histeq
        have htS : t ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr htn, hQt⟩
        have : t ≤ istar := Finset.le_max' _ _ htS
        omega
      · exact hlt3
    · have hsub : t - n + n = t := Nat.sub_add_cancel htn
      have hper' := Q_periodic a hper hsum (t - n)
      rw [hsub] at hper'
      have hle : Q a istar ≤ Q a (t - n) := hMle (t - n) (by omega)
      rw [hper']; omega
  -- uniqueness
  refine ⟨istar, ⟨histrange, hGoodStar⟩, ?_⟩
  rintro y ⟨hyn, hyGood⟩
  rcases lt_trichotomy y istar with h | h | h
  · have h1 : Q a y < Q a istar := hyGood istar (by omega) (by omega)
    have h2 : Q a istar < Q a (y + n) := hGoodStar (y + n) (by omega) (by omega)
    rw [Q_periodic a hper hsum y] at h2; omega
  · exact h
  · have h1 : Q a istar < Q a y := hGoodStar y (by omega) (by omega)
    have h2 : Q a y < Q a (istar + n) := hyGood (istar + n) (by omega) (by omega)
    rw [Q_periodic a hper hsum istar] at h2; omega
end CriticalPortraits.Cycle
