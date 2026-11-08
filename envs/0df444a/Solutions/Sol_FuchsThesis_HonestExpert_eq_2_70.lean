-- Prove2me | solution 1 for FuchsThesis.HonestExpert.eq_2_70
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-07T16:09:25.272874+00:00
-- url     : https://prove2.me/submissions/2902436e-f8f1-4752-8485-bd7cb87af446

import Mathlib

/-- Gibbs' inequality: `∑ p log q ≤ ∑ p log p`, with equality iff `p = q`. -/
theorem solution {n : ℕ} (p q : Fin n → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∑ k, p k = 1)
    (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1) (hpq : ∀ k, 0 < p k → 0 < q k) :
    ∑ k, p k * Real.log (q k) ≤ ∑ k, p k * Real.log (p k) ∧
      (∑ k, p k * Real.log (q k) = ∑ k, p k * Real.log (p k) ↔ p = q) := by
  classical
  set S := Finset.univ.filter (fun k => 0 < p k) with hSdef
  have hzero : ∀ k, ¬ 0 < p k → p k = 0 := by
    intro k hk
    rcases lt_or_eq_of_le (hp0 k) with h | h
    · exact absurd h hk
    · exact h.symm
  have hstrict : ∀ {x : ℝ}, 0 < x → x ≠ 1 → 1 - x⁻¹ < Real.log x := by
    intro x hx hx1
    have hxinv : x⁻¹ ≠ 1 := by
      intro h
      apply hx1
      have : x = (x⁻¹)⁻¹ := by simp
      rw [this, h]
      simp
    have h := Real.log_lt_sub_one_of_pos (inv_pos.mpr hx) hxinv
    rw [Real.log_inv] at h
    linarith
  have hD : ∑ k, p k * Real.log (p k) - ∑ k, p k * Real.log (q k) =
      ∑ k ∈ S, p k * (Real.log (p k) - Real.log (q k)) := by
    rw [← Finset.sum_sub_distrib]
    have hcongr : ∑ k ∈ S, p k * (Real.log (p k) - Real.log (q k)) =
        ∑ k ∈ S, (p k * Real.log (p k) - p k * Real.log (q k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hcongr]
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro k _ hk
    have hpk : p k = 0 := hzero k (by simpa [hSdef] using hk)
    simp [hpk]
  have hE : ∀ k ∈ S, 0 ≤ p k * (Real.log (p k) - Real.log (q k)) - (p k - q k) := by
    intro k hk
    have hpk : 0 < p k := (Finset.mem_filter.mp hk).2
    have hqk : 0 < q k := hpq k hpk
    have hlogeq : Real.log (p k) - Real.log (q k) = Real.log (p k / q k) := by
      rw [Real.log_div hpk.ne' hqk.ne']
    rw [hlogeq]
    have hlow := Real.one_sub_inv_le_log_of_pos (div_pos hpk hqk)
    have hcoef : p k * (1 - (p k / q k)⁻¹) = p k - q k := by
      field_simp
    nlinarith [hlow, hpk]
  have hDge : ∑ k ∈ S, (p k - q k) ≤
      ∑ k ∈ S, p k * (Real.log (p k) - Real.log (q k)) := by
    have h := Finset.sum_nonneg hE
    rw [Finset.sum_sub_distrib] at h
    linarith
  have hpS : ∑ k ∈ S, p k = 1 := by
    rw [← hp1]
    apply Finset.sum_subset (Finset.subset_univ S)
    intro k _ hk
    exact hzero k (by simpa [hSdef] using hk)
  have hpqsum : ∑ k ∈ S, (p k - q k) = ∑ k ∈ (Finset.univ \ S), q k := by
    rw [Finset.sum_sub_distrib, hpS]
    have hqsplit := Finset.sum_sdiff (s₁ := S) (s₂ := (Finset.univ : Finset (Fin n)))
      (f := q) (Finset.subset_univ S)
    rw [hq1] at hqsplit
    linarith
  have hq_nonneg : 0 ≤ ∑ k ∈ (Finset.univ \ S), q k := Finset.sum_nonneg (fun k _ => hq0 k)
  have hfirst : ∑ k, p k * Real.log (q k) ≤ ∑ k, p k * Real.log (p k) := by
    have hDnonneg : 0 ≤ ∑ k ∈ S, p k * (Real.log (p k) - Real.log (q k)) := by
      linarith [hDge, hpqsum, hq_nonneg]
    linarith [hD]
  constructor
  · exact hfirst
  · constructor
    · intro heq
      have hDsum0 : ∑ k ∈ S, p k * (Real.log (p k) - Real.log (q k)) = 0 := by
        linarith [hD]
      have hpq0 : ∑ k ∈ S, (p k - q k) = 0 := by
        have hle : ∑ k ∈ S, (p k - q k) ≤ 0 := by linarith [hDge, hDsum0]
        linarith [hpqsum, hq_nonneg]
      have hE0 : ∑ k ∈ S,
          (p k * (Real.log (p k) - Real.log (q k)) - (p k - q k)) = 0 := by
        rw [Finset.sum_sub_distrib, hDsum0, hpq0]
        ring
      have hterm : ∀ k ∈ S,
          p k * (Real.log (p k) - Real.log (q k)) - (p k - q k) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun k hk => hE k hk)).mp hE0
      have hqout : ∀ k ∈ (Finset.univ \ S), q k = 0 := by
        have hsum0 : ∑ k ∈ (Finset.univ \ S), q k = 0 := by linarith [hpqsum, hpq0]
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hq0 k)).mp hsum0
      funext k
      by_cases hk : k ∈ S
      · have hpk : 0 < p k := (Finset.mem_filter.mp hk).2
        have hqk : 0 < q k := hpq k hpk
        have ht := hterm k hk
        have hlog : Real.log (p k / q k) = 1 - q k / p k := by
          rw [Real.log_div hpk.ne' hqk.ne']
          field_simp at ht ⊢
          linarith
        by_contra hne
        have hx : 0 < p k / q k := div_pos hpk hqk
        have hxne : p k / q k ≠ 1 := by
          intro h
          apply hne
          field_simp at h
          linarith
        have hlt := hstrict hx hxne
        have hinv : (p k / q k)⁻¹ = q k / p k := by
          field_simp
        rw [hinv] at hlt
        linarith
      · have hpk0 : p k = 0 := hzero k (by simpa [hSdef] using hk)
        have hqk0 : q k = 0 := hqout k (Finset.mem_sdiff.mpr ⟨Finset.mem_univ k, hk⟩)
        rw [hpk0, hqk0]
    · intro hpq_eq
      rw [hpq_eq]
