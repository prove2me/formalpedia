-- Prove2me | solution 1 for CryptoMiningMFG.eq_2_7_max_hamiltonian
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-16T14:16:36.191065+00:00
-- url     : https://prove2.me/submissions/046d253b-4a8d-4d76-8156-50aa8bf91e96

import Mathlib

theorem solution (K c M abar p q : ℝ) (hK : 0 < K) (hc : 0 < c) (hM : 0 < M)
    (habar : 0 < abar) (hp : 0 < p) (hq : 0 < q) :
    IsGreatest ((fun α : ℝ => -c * α * p + K * α / (α + M * abar) * q) '' Set.Ici 0)
      (if abar < K * q / (M * c * p) then
        (Real.sqrt (M * c * abar * p) - Real.sqrt (K * q)) ^ 2 else 0) := by
  classical
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
  have hsu : Real.sqrt (c * p) * s = Real.sqrt (K * q) := by
    rw [hs, ← Real.sqrt_mul (le_of_lt hcp)]
    congr 1
    field_simp
  have hcu : Real.sqrt (c * p) * u = Real.sqrt (M * c * abar * p) := by
    rw [hu, ← Real.sqrt_mul (le_of_lt hcp)]
    congr 1
    ring
  have hconv : c * p * (s - u) ^ 2 =
      (Real.sqrt (M * c * abar * p) - Real.sqrt (K * q)) ^ 2 := by
    have hsq : (Real.sqrt (c * p)) ^ 2 = c * p := Real.sq_sqrt (le_of_lt hcp)
    have hfac : Real.sqrt (c * p) * u - Real.sqrt (c * p) * s =
        Real.sqrt (c * p) * (u - s) := by ring
    rw [← hcu, ← hsu, hfac, mul_pow, hsq]
    ring
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
    have hmem : (0 : ℝ) ≤ u * (s - u) := mul_nonneg hu_nn (by linarith)
    constructor
    · refine ⟨u * (s - u), ?_, ?_⟩
      · show (0 : ℝ) ≤ u * (s - u)
        exact hmem
      · show -c * (u * (s - u)) * p +
            K * (u * (s - u)) / (u * (s - u) + M * abar) * q =
          (Real.sqrt (M * c * abar * p) - Real.sqrt (K * q)) ^ 2
        rw [hkey (u * (s - u)) hmem]
        have hzero : u * (s - u) + u ^ 2 - s * u = 0 := by ring
        rw [hzero]
        simp
        exact hconv
    · rintro x ⟨α, hα, rfl⟩
      change -c * α * p + K * α / (α + M * abar) * q ≤
        (Real.sqrt (M * c * abar * p) - Real.sqrt (K * q)) ^ 2
      have hα0 : 0 ≤ α := hα
      rw [← hconv, hkey α hα0]
      have ht : 0 < α + u ^ 2 := by linarith
      have hX : 0 ≤ (α + u ^ 2 - s * u) ^ 2 / (α + u ^ 2) :=
        div_nonneg (sq_nonneg _) ht.le
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
    · refine ⟨0, ?_, ?_⟩
      · show (0 : ℝ) ≤ 0
        exact le_rfl
      · show -c * 0 * p + K * 0 / (0 + M * abar) * q = 0
        simp
    · rintro x ⟨α, hα, rfl⟩
      change -c * α * p + K * α / (α + M * abar) * q ≤ 0
      have hα0 : 0 ≤ α := hα
      rw [hkey2 α hα0]
      have ht : 0 < α + u ^ 2 := by linarith
      have hs2le : s ^ 2 ≤ u ^ 2 := by nlinarith [hsu_le]
      have h1 : 0 ≤ (α + u ^ 2) - u ^ 2 := by linarith
      have h2 : 0 ≤ (α + u ^ 2) - s ^ 2 := by linarith
      have hX : 0 ≤ ((α + u ^ 2) - s ^ 2) * ((α + u ^ 2) - u ^ 2) / (α + u ^ 2) :=
        div_nonneg (mul_nonneg h2 h1) ht.le
      nlinarith [hX, hcp]
