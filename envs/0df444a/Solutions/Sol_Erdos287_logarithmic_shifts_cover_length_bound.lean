-- Prove2me | solution 1 for Erdos287.logarithmic_shifts_cover_length_bound
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T07:58:38.531695+00:00
-- url     : https://prove2.me/submissions/1b07fbe9-c10e-4771-ba8a-52d6d512b876

import Mathlib

open Finset MeasureTheory

set_option autoImplicit false

/-- A translated copy of a whole band must start before the end of its
containing interval. Grouping the logarithmic shifts bounds how much of
the parameter axis those start positions can cover. -/
theorem solution (J : Finset ℕ) (l u : ℕ → ℝ) (a b r ε : ℝ) (N k : ℕ)
    (hε : 0 ≤ ε) (hk : 1 ≤ k) (hkN : k ≤ N)
    (hl : ∀ i ∈ J, r ≤ u i - l i)
    (hcover : ∀ x ∈ Set.Icc a b, ∃ i ∈ J, ∃ z ∈ Set.Icc (l i) (u i - r),
      ∃ d ∈ Finset.Icc 1 N, |x - (z + Real.log d)| ≤ ε) :
    b - a ≤ ∑ i ∈ J, ((k : ℝ) * (u i - l i - r + 2 * ε) +
      (Real.log (N : ℝ) - Real.log k)) := by
  let K := Icc 1 k
  let top (j : ℕ) := if j = k then Real.log N else Real.log j
  let cover (i j : ℕ) :=
    Set.Icc (l i + Real.log j - ε) (u i - r + top j + ε)
  let width (i j : ℕ) := (u i - l i - r + 2 * ε) +
    (if j = k then Real.log (N : ℝ) - Real.log k else 0)
  have hgap : 0 ≤ Real.log (N : ℝ) - Real.log k := by
    apply sub_nonneg.mpr
    exact Real.log_le_log (by exact_mod_cast hk) (by exact_mod_cast hkN)
  have hw (i : ℕ) (hi : i ∈ J) (j : ℕ) : 0 ≤ width i j := by
    have hbase := hl i hi
    by_cases h : j = k <;> simp only [width, h, if_true, if_false] <;> linarith
  have hcoverJ : Set.Icc a b ⊆ ⋃ i ∈ J, ⋃ j ∈ K, cover i j := by
    intro x hx
    obtain ⟨i, hi, z, hz, d, hd, hclose⟩ := hcover x hx
    obtain ⟨hld, hud⟩ := mem_Icc.mp hd
    let j := min d k
    have hj : j ∈ K := mem_Icc.mpr ⟨le_min hld hk, min_le_right _ _⟩
    have hjd : Real.log (j : ℝ) ≤ Real.log d :=
      Real.log_le_log (by exact_mod_cast (mem_Icc.mp hj).1) (by exact_mod_cast min_le_left d k)
    have hdu : Real.log (d : ℝ) ≤ top j := by
      by_cases h : k ≤ d
      · have he : j = k := min_eq_right h
        simp only [top, he, if_true]
        exact Real.log_le_log (by exact_mod_cast hld) (by exact_mod_cast hud)
      · have he : j = d := min_eq_left (by omega)
        have hne : j ≠ k := by omega
        rw [show top j = Real.log j from if_neg hne, he]
    apply Set.mem_iUnion₂.mpr
    refine ⟨i, hi, Set.mem_iUnion₂.mpr ⟨j, hj, ?_⟩⟩
    change l i + Real.log j - ε ≤ x ∧ x ≤ u i - r + top j + ε
    obtain ⟨h₁, h₂⟩ := abs_le.mp hclose
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hvol (i j : ℕ) : volume (cover i j) = ENNReal.ofReal (width i j) := by
    rw [Real.volume_Icc]
    congr 1
    by_cases h : j = k
    · subst j
      simp only [top, width, if_true]
      ring
    · simp only [top, width, h, if_false]
      ring
  have hwidth (i : ℕ) :
      (∑ j ∈ K, width i j) = (k : ℝ) * (u i - l i - r + 2 * ε) +
        (Real.log (N : ℝ) - Real.log k) := by
    simp [width, sum_add_distrib, K, hk]
    ring
  have hmeasure : volume (Set.Icc a b) ≤ ∑ i ∈ J, ∑ j ∈ K, volume (cover i j) := calc
    _ ≤ volume (⋃ i ∈ J, ⋃ j ∈ K, cover i j) := measure_mono hcoverJ
    _ ≤ ∑ i ∈ J, volume (⋃ j ∈ K, cover i j) := measure_biUnion_finset_le J _
    _ ≤ _ := sum_le_sum (fun i _ => measure_biUnion_finset_le K (cover i))
  have hnonneg : 0 ≤ ∑ i ∈ J, ∑ j ∈ K, width i j :=
    sum_nonneg (fun i hi => sum_nonneg (fun j _ => hw i hi j))
  rw [Real.volume_Icc] at hmeasure
  have hrhs : (∑ i ∈ J, ∑ j ∈ K, volume (cover i j)) =
      ENNReal.ofReal (∑ i ∈ J, ∑ j ∈ K, width i j) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => sum_nonneg (fun j _ => hw i hi j))]
    refine sum_congr rfl (fun i hi => ?_)
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => hw i hi j)]
    exact sum_congr rfl (fun j _ => hvol i j)
  rw [hrhs] at hmeasure
  have h := (ENNReal.ofReal_le_ofReal_iff hnonneg).mp hmeasure
  simpa only [hwidth] using h

