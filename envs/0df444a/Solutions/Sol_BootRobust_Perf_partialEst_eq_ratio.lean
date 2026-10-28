-- Prove2me | solution 1 for BootRobust.Perf.partialEst_eq_ratio
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:50:29.198128+00:00
-- url     : https://prove2.me/submissions/81e11f88-96c1-4db0-92aa-8255a56b1f31

import Mathlib
import Definitions.Def_BootRobust_Perf_Setting

open BootRobust.Perf in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (n k : ℕ) (hn : 1 ≤ n)
    (hk : 1 ≤ k) (N : ℕ → Finset ι) (w : ι → ℝ) (hw : ∀ i, 0 < w i) (ℓ : ι → ℝ) (j : ℕ)
    (D : ι → ℝ) (hD : D ∈ Dj n k N j) :
    partialEst n k N w ℓ j D =
      (((∑ i ∈ N j, ℓ i * w i * D i) / (∑ i ∈ N j, w i * D i) : ℝ) : EReal) := by
  obtain ⟨⟨hD0, hD1⟩, hlo, hhi⟩ := hD
  unfold mass at hlo hhi
  set W := ∑ i ∈ N j, w i * D i with hWdef
  have hkn : (0 : ℝ) < (k : ℝ) / n := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hW : 0 < W := by
    apply lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => mul_nonneg (hw i).le (hD0 i)))
    intro h0
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_nonneg (hw i).le (hD0 i))).mp h0.symm
    have hm : ∑ i ∈ N j, D i = 0 := Finset.sum_eq_zero (fun i hi => by
      rcases mul_eq_zero.mp (hz i hi) with h | h
      · linarith [hw i]
      · exact h)
    linarith
  have hval : ∀ p : ℝ × (ι → ℝ), lpFeasible n k N w j D p.1 p.2 →
      (∑ i ∈ N j, w i * ℓ i * p.2 i) = (∑ i ∈ N j, ℓ i * w i * D i) / W := by
    rintro ⟨s, P⟩ hp
    obtain ⟨hs, -, hP, -, hw1, -, -⟩ := hp
    simp only at hP hw1 ⊢
    have h1 : s * W = 1 := by
      rw [← hw1, hWdef, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← hP i]
      ring
    rw [eq_div_iff hW.ne']
    have : ∑ i ∈ N j, w i * ℓ i * P i = s * ∑ i ∈ N j, ℓ i * w i * D i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← hP i]
      ring
    rw [this]
    calc s * (∑ i ∈ N j, ℓ i * w i * D i) * W = (s * W) * ∑ i ∈ N j, ℓ i * w i * D i := by ring
      _ = _ := by rw [h1, one_mul]
  have hfeas : lpFeasible n k N w j D (1 / W) (fun i => 1 / W * D i) := by
    have hWi : 0 < 1 / W := by positivity
    refine ⟨hWi, fun i => mul_nonneg hWi.le (hD0 i), fun i => rfl, ?_, ?_, ?_, ?_⟩
    · rw [← Finset.mul_sum, hD1, mul_one]
    · have : ∑ i ∈ N j, w i * (1 / W * D i) = 1 / W * W := by
        rw [hWdef, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [this]
      field_simp
    · rw [← Finset.mul_sum]
      nlinarith
    · rw [← Finset.mul_sum]
      nlinarith
  unfold partialEst
  apply le_antisymm
  · apply iSup₂_le
    intro p hp
    exact le_of_eq (congrArg (fun x : ℝ => (x : EReal)) (hval p hp))
  · refine le_iSup₂_of_le (f := fun (p : ℝ × (ι → ℝ)) _ => ((∑ i ∈ N j, w i * ℓ i * p.2 i : ℝ) : EReal))
      ((1 / W, fun i => 1 / W * D i) : ℝ × (ι → ℝ)) hfeas ?_
    exact le_of_eq (congrArg (fun x : ℝ => (x : EReal)) (hval _ hfeas)).symm
