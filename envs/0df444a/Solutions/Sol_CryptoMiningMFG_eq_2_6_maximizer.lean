-- Prove2me | solution 1 for CryptoMiningMFG.eq_2_6_maximizer
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-16T15:09:16.562954+00:00
-- url     : https://prove2.me/submissions/ad196f3b-6d14-4a89-b628-f0a9e073e822

import Mathlib

theorem solution (K c M abar p q : ℝ) (hK : 0 < K) (hc : 0 < c) (hM : 0 < M)
    (habar : 0 < abar) (hp : 0 < p) (hq : 0 < q) :
    let H : ℝ → ℝ := fun α => -c * α * p + K * α / (α + M * abar) * q
    let αstar : ℝ := if abar < K * q / (M * c * p) then
      -M * abar + Real.sqrt (K * M * abar * q / (c * p)) else 0
    0 ≤ αstar ∧ ∀ α : ℝ, 0 ≤ α → α ≠ αstar → H α < H αstar := by
  classical
  dsimp only
  set s := Real.sqrt (K * q / (c * p)) with hs
  set u := Real.sqrt (M * abar) with hu
  have hcp : 0 < c * p := mul_pos hc hp
  have hKq : 0 < K * q := mul_pos hK hq
  have hMab : 0 < M * abar := mul_pos hM habar
  have hs_nn : 0 ≤ s := Real.sqrt_nonneg _
  have hu_nn : 0 ≤ u := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = K * q / (c * p) := by
    rw [hs, Real.sq_sqrt (le_of_lt (div_pos hKq hcp))]
  have hu2 : u ^ 2 = M * abar := by
    rw [hu, Real.sq_sqrt (le_of_lt hMab)]
  have hu2pos : 0 < u ^ 2 := by rw [hu2]; exact hMab
  have hkey : ∀ α : ℝ, 0 ≤ α → -c * α * p + K * α / (α + M * abar) * q =
      c * p * ((s - u) ^ 2 - (α + u ^ 2 - s * u) ^ 2 / (α + u ^ 2)) := by
    intro α hα
    have ht : 0 < α + u ^ 2 := by linarith
    have hstep : K * α / (α + M * abar) * q = K * q * α / (α + M * abar) := by ring
    have hKq' : K * q = c * p * s ^ 2 := by rw [hs2]; field_simp
    rw [hstep, ← hu2, hKq']
    field_simp
    ring
  have hkey2 : ∀ α : ℝ, 0 ≤ α → -c * α * p + K * α / (α + M * abar) * q =
      -(c * p * (((α + u ^ 2) - s ^ 2) * ((α + u ^ 2) - u ^ 2) / (α + u ^ 2))) := by
    intro α hα
    have ht : 0 < α + u ^ 2 := by linarith
    have hstep : K * α / (α + M * abar) * q = K * q * α / (α + M * abar) := by ring
    have hKq' : K * q = c * p * s ^ 2 := by rw [hs2]; field_simp
    rw [hstep, ← hu2, hKq']
    field_simp
    ring
  have hMcp : (0 : ℝ) < M * c * p := by positivity
  by_cases hcase : abar < K * q / (M * c * p)
  · rw [if_pos hcase]
    have hlt : M * abar < K * q / (c * p) := by
      rw [lt_div_iff₀ hcp]
      have h1 : abar * (M * c * p) < K * q := (lt_div_iff₀ hMcp).mp hcase
      nlinarith [h1]
    have hus : u < s := by
      have h2 : u ^ 2 < s ^ 2 := by rw [hu2, hs2]; exact hlt
      have habs : |u| < |s| := sq_lt_sq.mp h2
      rwa [abs_of_nonneg hu_nn, abs_of_nonneg hs_nn] at habs
    have hα : -M * abar + Real.sqrt (K * M * abar * q / (c * p)) = u * (s - u) := by
      have h1 : Real.sqrt (K * M * abar * q / (c * p)) = u * s := by
        have h2 : K * M * abar * q / (c * p) = (M * abar) * (K * q / (c * p)) := by
          field_simp
        rw [h2, Real.sqrt_mul (le_of_lt hMab), hu, hs]
      rw [h1]
      have h3 : M * abar = u ^ 2 := hu2.symm
      linear_combination (-1 : ℝ) * h3
    constructor
    · rw [hα]
      exact mul_nonneg hu_nn (by linarith)
    · intro α hα0 hne
      rw [hα] at hne ⊢
      have hHstar : -c * (u * (s - u)) * p +
          K * (u * (s - u)) / (u * (s - u) + M * abar) * q = c * p * (s - u) ^ 2 := by
        have h := hkey (u * (s - u)) (mul_nonneg hu_nn (by linarith))
        rw [h]
        have hzero : u * (s - u) + u ^ 2 - s * u = 0 := by ring
        rw [hzero]
        simp
      rw [hHstar, hkey α hα0]
      have ht : 0 < α + u ^ 2 := by linarith
      have hne' : α + u ^ 2 - s * u ≠ 0 := by
        intro h
        exact hne (by linear_combination h)
      have hX : 0 < (α + u ^ 2 - s * u) ^ 2 / (α + u ^ 2) :=
        div_pos (sq_pos_of_ne_zero hne') ht
      nlinarith [hX, hcp]
  · rw [if_neg hcase]
    have hle : K * q / (c * p) ≤ M * abar := by
      rw [div_le_iff₀ hcp]
      have h1 : K * q ≤ abar * (M * c * p) := (div_le_iff₀ hMcp).mp (le_of_not_gt hcase)
      nlinarith [h1]
    have hsu_le : s ≤ u := by
      have h2 : s ^ 2 ≤ u ^ 2 := by rw [hu2, hs2]; exact hle
      have habs : |s| ≤ |u| := sq_le_sq.mp h2
      rwa [abs_of_nonneg hs_nn, abs_of_nonneg hu_nn] at habs
    constructor
    · norm_num
    · intro α hα0 hne
      have hαpos : 0 < α := by
        rcases lt_or_eq_of_le hα0 with h | h
        · exact h
        · exact absurd h.symm hne
      rw [hkey2 α hα0]
      have hH0 : -c * 0 * p + K * 0 / (0 + M * abar) * q = 0 := by norm_num
      rw [hH0]
      have ht : 0 < α + u ^ 2 := by linarith
      have h1 : 0 < (α + u ^ 2) - s ^ 2 := by nlinarith [hsu_le, hs_nn, hu_nn]
      have h2 : 0 < (α + u ^ 2) - u ^ 2 := by linarith
      have hX : 0 < ((α + u ^ 2) - s ^ 2) * ((α + u ^ 2) - u ^ 2) / (α + u ^ 2) :=
        div_pos (mul_pos h1 h2) ht
      nlinarith [hX, hcp]
