-- Prove2me | solution 1 for BotNguyenADMM.KL.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T09:23:28.528392+00:00
-- url     : https://prove2.me/submissions/5b0defe5-d873-4136-a772-0779ca015f03

import Mathlib

open Filter Topology

theorem solution (N : ℕ) (a : ℕ → Fin N → ℝ) (ha : ∀ k i, 0 ≤ a k i) (δ : ℕ → ℝ)
    (c₀ c₁ c₂ : Fin N → ℝ) (hc₁ : ∀ i, 0 ≤ c₁ i) (hc₂ : ∀ i, 0 ≤ c₂ i)
    (hc : ∀ i, c₀ i + c₁ i + c₂ i < 1)
    (h9 : ∀ k, 2 ≤ k → ∑ i, a (k + 1) i ≤
      ∑ i, c₀ i * a k i + ∑ i, c₁ i * a (k - 1) i + ∑ i, c₂ i * a (k - 2) i + δ k)
    (δbar : ℝ) (hδbar : 0 ≤ δbar)
    (hδ : ∀ Klo Khi : ℕ, 2 ≤ Klo → Klo ≤ Khi → ∑ k ∈ Finset.Icc Klo Khi, δ k ≤ δbar) :
    (∀ i, Summable (fun k => a k i)) ∧
    ∀ (i : Fin N) (Klo Khi : ℕ), 2 ≤ Klo → Klo ≤ Khi →
      ∑ k ∈ Finset.Icc Klo Khi, a k i ≤
        (∑ j, ((1 - c₀ j - c₁ j) * a Klo j + (1 - c₀ j) * a (Klo + 1) j + a (Klo + 2) j)
          + δbar) / (1 - c₀ i - c₁ i - c₂ i) := by
  classical
  -- the potential
  let Φ : ℕ → ℝ := fun k =>
    ∑ j, ((1 - c₀ j - c₁ j) * a k j + (1 - c₀ j) * a (k + 1) j + a (k + 2) j)
  have hdpos : ∀ j, 0 < 1 - c₀ j - c₁ j - c₂ j := by
    intro j
    linarith [hc j, hc₁ j, hc₂ j]
  have hα : ∀ j, 0 ≤ 1 - c₀ j - c₁ j := by
    intro j
    linarith [hc j, hc₁ j, hc₂ j]
  have hβ : ∀ j, 0 ≤ 1 - c₀ j := by
    intro j
    linarith [hc j, hc₁ j, hc₂ j]
  have hΦ : ∀ k, 0 ≤ Φ k := by
    intro k
    apply Finset.sum_nonneg
    intro j _
    have h1 : 0 ≤ (1 - c₀ j - c₁ j) * a k j := mul_nonneg (hα j) (ha k j)
    have h2 : 0 ≤ (1 - c₀ j) * a (k + 1) j := mul_nonneg (hβ j) (ha (k + 1) j)
    have h3 : 0 ≤ a (k + 2) j := ha (k + 2) j
    linarith
  -- the per-step identity
  have hkey : ∀ k, 2 ≤ k →
      ∑ j, (1 - c₀ j - c₁ j - c₂ j) * a k j ≤ Φ k - Φ (k + 1) + δ (k + 2) := by
    intro k hk
    have h9k := h9 (k + 2) (by omega)
    have h9k' : ∑ i, a (k + 3) i ≤
        ∑ i, c₀ i * a (k + 2) i + ∑ i, c₁ i * a (k + 1) i + ∑ i, c₂ i * a k i + δ (k + 2) := by
      simpa only [show k + 2 + 1 = k + 3 by omega, show k + 2 - 1 = k + 1 by omega,
        show k + 2 - 2 = k by omega] using h9k
    have h1 : Φ k - Φ (k + 1) =
        ∑ j, ((1 - c₀ j - c₁ j) * a k j + (1 - c₀ j) * a (k + 1) j + a (k + 2) j
          - ((1 - c₀ j - c₁ j) * a (k + 1) j + (1 - c₀ j) * a (k + 2) j + a (k + 3) j)) := by
      simp only [Φ]
      rw [← Finset.sum_sub_distrib]
    have h2 : (∑ j, ((1 - c₀ j - c₁ j) * a k j + (1 - c₀ j) * a (k + 1) j + a (k + 2) j
          - ((1 - c₀ j - c₁ j) * a (k + 1) j + (1 - c₀ j) * a (k + 2) j + a (k + 3) j))) =
        ∑ j, (c₀ j * a (k + 2) j + c₁ j * a (k + 1) j + c₂ j * a k j - a (k + 3) j
          + (1 - c₀ j - c₁ j - c₂ j) * a k j) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    have h3 : (∑ j, (c₀ j * a (k + 2) j + c₁ j * a (k + 1) j + c₂ j * a k j - a (k + 3) j
          + (1 - c₀ j - c₁ j - c₂ j) * a k j)) =
        (∑ j, c₀ j * a (k + 2) j) + (∑ j, c₁ j * a (k + 1) j) + (∑ j, c₂ j * a k j)
          - (∑ j, a (k + 3) j) + (∑ j, (1 - c₀ j - c₁ j - c₂ j) * a k j) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hA : Φ k - Φ (k + 1) = (∑ j, c₀ j * a (k + 2) j) + (∑ j, c₁ j * a (k + 1) j)
        + (∑ j, c₂ j * a k j) - (∑ j, a (k + 3) j)
        + (∑ j, (1 - c₀ j - c₁ j - c₂ j) * a k j) := h1.trans (h2.trans h3)
    linarith
  -- telescoping
  have htel : ∀ Klo Khi : ℕ, 2 ≤ Klo → Klo ≤ Khi →
      ∑ k ∈ Finset.Icc Klo Khi, (∑ j, (1 - c₀ j - c₁ j - c₂ j) * a k j) ≤ Φ Klo + δbar := by
    intro Klo Khi hKlo hKhi
    have htele : ∀ Khi, Klo ≤ Khi →
        ∑ k ∈ Finset.Icc Klo Khi, (∑ j, (1 - c₀ j - c₁ j - c₂ j) * a k j) + Φ (Khi + 1)
          ≤ Φ Klo + ∑ k ∈ Finset.Icc Klo Khi, δ (k + 2) := by
      intro Khi hK
      induction Khi, hK using Nat.le_induction with
      | base =>
          simp only [Finset.Icc_self, Finset.sum_singleton]
          have h := hkey Klo hKlo
          linarith
      | succ Khi hK ih =>
          rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
          have hk := hkey (Khi + 1) (by omega)
          rw [show Khi + 1 + 1 = Khi + 2 by omega, show Khi + 1 + 2 = Khi + 3 by omega]
          linarith
    have hbound : ∑ k ∈ Finset.Icc Klo Khi, δ (k + 2) ≤ δbar := by
      have hshift : (∑ k ∈ Finset.Icc Klo Khi, δ (k + 2)) = ∑ k ∈ Finset.Icc (Klo + 2) (Khi + 2), δ k := by
        apply Finset.sum_bij (fun k _ => k + 2)
        · intro k hk
          simp only [Finset.mem_Icc] at hk ⊢
          omega
        · intro k1 _ k2 _ h
          omega
        · intro b hb
          simp only [Finset.mem_Icc] at hb
          refine ⟨b - 2, ?_, ?_⟩
          · simp only [Finset.mem_Icc]; omega
          · omega
        · intro k _
          rfl
      rw [hshift]
      exact hδ (Klo + 2) (Khi + 2) (by omega) (by omega)
    have h := htele Khi hKhi
    linarith [hΦ (Khi + 1), hbound]
  -- per-coordinate bound
  have hmain : ∀ (i : Fin N) (Klo Khi : ℕ), 2 ≤ Klo → Klo ≤ Khi →
      (1 - c₀ i - c₁ i - c₂ i) * ∑ k ∈ Finset.Icc Klo Khi, a k i ≤ Φ Klo + δbar := by
    intro i Klo Khi h1 h2
    have hsingle : (1 - c₀ i - c₁ i - c₂ i) * ∑ k ∈ Finset.Icc Klo Khi, a k i
        ≤ ∑ k ∈ Finset.Icc Klo Khi, (∑ j, (1 - c₀ j - c₁ j - c₂ j) * a k j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _
      exact Finset.single_le_sum (fun j _ => mul_nonneg (le_of_lt (hdpos j)) (ha k j)) (Finset.mem_univ i)
    linarith [htel Klo Khi h1 h2]
  refine ⟨?_, ?_⟩
  · -- summability
    intro i
    have hdi := hdpos i
    have hshift : ∀ n, (∑ k ∈ Finset.range n, a (k + 2) i) = ∑ k ∈ Finset.Icc 2 (n + 1), a k i := by
      intro n
      apply Finset.sum_bij (fun k _ => k + 2)
      · intro k hk
        simp only [Finset.mem_range] at hk
        simp only [Finset.mem_Icc]
        omega
      · intro k1 _ k2 _ h
        omega
      · intro b hb
        simp only [Finset.mem_Icc] at hb
        refine ⟨b - 2, ?_, ?_⟩
        · simp only [Finset.mem_range]; omega
        · omega
      · intro k _
        rfl
    have hb : ∀ n, ∑ k ∈ Finset.range n, a (k + 2) i ≤
        (Φ 2 + δbar) / (1 - c₀ i - c₁ i - c₂ i) := by
      intro n
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        simp only [Finset.range_zero, Finset.sum_empty]
        exact div_nonneg (by linarith [hΦ 2, hδbar]) hdi.le
      · rw [hshift n, le_div_iff₀ hdi]
        have h := hmain i 2 (n + 1) (by norm_num) (by omega)
        rwa [mul_comm] at h
    have hs : Summable (fun k => a (k + 2) i) :=
      summable_of_sum_range_le (fun n => ha (n + 2) i) hb
    exact (summable_nat_add_iff 2).mp hs
  · -- the quantitative bound
    intro i Klo Khi h1 h2
    have hdi := hdpos i
    change ∑ k ∈ Finset.Icc Klo Khi, a k i ≤ (Φ Klo + δbar) / (1 - c₀ i - c₁ i - c₂ i)
    rw [le_div_iff₀ hdi, mul_comm]
    exact hmain i Klo Khi h1 h2

