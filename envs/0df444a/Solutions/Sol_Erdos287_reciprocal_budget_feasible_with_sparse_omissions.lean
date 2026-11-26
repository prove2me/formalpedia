-- Prove2me | solution 1 for Erdos287.reciprocal_budget_feasible_with_sparse_omissions
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T05:58:21.578431+00:00
-- url     : https://prove2.me/submissions/26f46d33-4151-4127-9adf-f77d178f8f3e

import Mathlib

open Finset

set_option autoImplicit false

/-- If allowed omissions are nonconsecutive, one can choose the lower endpoint
so that the remaining reciprocal sum reaches one with an error less than its
first reciprocal. -/
theorem solution (lo M : ℕ) (hlo : 2 ≤ lo) (hlM : lo ≤ M)
    (H : Finset ℕ) (hM : M ∉ H)
    (hsep : ∀ n, lo ≤ n → n + 1 ≤ M → n ∈ H → n + 1 ∉ H)
    (hfull : (1 : ℚ) ≤ ∑ n ∈ Finset.Icc lo M \ H, (1 : ℚ) / n) :
    ∃ m, lo ≤ m ∧ m < M ∧ m ∉ H ∧
      (1 : ℚ) ≤ (∑ n ∈ Finset.Icc m M \ H, (1 : ℚ) / n) ∧
      (∑ n ∈ Finset.Icc m M \ H, (1 : ℚ) / n) < 1 + (1 : ℚ) / m ∧
      (∀ n, m ≤ n → n + 1 ≤ M → n ∈ Finset.Icc m M \ H ∨ n + 1 ∈ Finset.Icc m M \ H) ∧
      (∑ n ∈ Finset.Icc m M ∩ H, (1 : ℚ) / n) ≤ (∑ n ∈ Finset.Icc m M, (1 : ℚ) / n) - 1 := by
  let D (m : ℕ) := Icc m M \ H
  let mass (m : ℕ) : ℚ := ∑ n ∈ D m, (1 : ℚ) / n
  let good := (Icc lo M).filter (fun m => 1 ≤ mass m)
  have hgood : good.Nonempty := ⟨lo, mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl, hlM⟩, hfull⟩⟩
  let m := good.max' hgood
  have hm := mem_filter.mp (good.max'_mem hgood)
  change m ∈ Icc lo M ∧ 1 ≤ mass m at hm
  have ⟨hml, hmM⟩ := mem_Icc.mp hm.1
  have hm_lt : m < M := by
    by_contra! he
    have heq : m = M := le_antisymm hmM he
    have hsingle : ({M} : Finset ℕ) \ H = {M} := by
      ext n
      by_cases hn : n = M
      · subst n
        simp [hM]
      · simp [hn]
    have hmassM : mass M = (1 : ℚ) / M := by simp [mass, D, hsingle]
    have hge := hm.2
    rw [heq, hmassM] at hge
    have hlt : (1 : ℚ) < M := by exact_mod_cast (show 1 < M by omega)
    exact (not_le_of_gt ((div_lt_one (by positivity)).mpr hlt)) hge
  have hnext : mass (m + 1) < 1 := by
    by_contra! hn
    have hin : m + 1 ∈ good := mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hn⟩
    have hb := good.le_max' (m + 1) hin
    change m + 1 ≤ m at hb
    omega
  have herase : D (m + 1) = (D m).erase m := by
    ext n
    simp only [D, mem_erase, mem_sdiff, mem_Icc]
    constructor
    · rintro ⟨⟨hn, hn'⟩, hh⟩
      exact ⟨by omega, ⟨by omega, hn'⟩, hh⟩
    · rintro ⟨hne, ⟨hn, hn'⟩, hh⟩
      exact ⟨⟨by omega, hn'⟩, hh⟩
  have hmH : m ∉ H := by
    intro hh
    have hmD : m ∉ D m := fun hd => (mem_sdiff.mp hd).2 hh
    have heq : mass (m + 1) = mass m := by
      simp only [mass, herase, erase_eq_of_notMem hmD]
    rw [heq] at hnext
    exact (not_le_of_gt hnext) hm.2
  have hmD : m ∈ D m := mem_sdiff.mpr ⟨mem_Icc.mpr ⟨le_rfl, hmM⟩, hmH⟩
  have hstep : mass (m + 1) + (1 : ℚ) / m = mass m := by
    simpa only [mass, herase] using sum_erase_add (D m) (fun n => (1 : ℚ) / n) hmD
  have hupper : mass m < 1 + (1 : ℚ) / m := by
    rw [← hstep]
    linarith only [hnext]
  refine ⟨m, hml, hm_lt, hmH, hm.2, hupper, ?_, ?_⟩
  · intro n hn hn'
    by_cases h : n ∈ H
    · exact Or.inr (mem_sdiff.mpr ⟨mem_Icc.mpr ⟨by omega, hn'⟩, hsep n (hml.trans hn) hn' h⟩)
    · exact Or.inl (mem_sdiff.mpr ⟨mem_Icc.mpr ⟨hn, by omega⟩, h⟩)
  · have hpartition : D m ∪ (Icc m M ∩ H) = Icc m M := by
      ext n
      simp only [D, mem_union, mem_sdiff, mem_inter]
      tauto
    have hdisj : Disjoint (D m) (Icc m M ∩ H) :=
      disjoint_left.mpr fun _ h₁ h₂ => (mem_sdiff.mp h₁).2 (mem_inter.mp h₂).2
    have hsplit := sum_union (f := fun n : ℕ => (1 : ℚ) / n) hdisj
    rw [hpartition] at hsplit
    have hmass := hm.2
    change 1 ≤ ∑ n ∈ D m, (1 : ℚ) / n at hmass
    linarith only [hmass, hsplit]

