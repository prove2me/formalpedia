-- Prove2me | solution 1 for ExplicitExpanders.Sizes.exists_pow_ratio_near_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T03:26:22.729594+00:00
-- url     : https://prove2.me/submissions/c6e1e57e-bf14-45ae-9618-3d9e070275d9

import Mathlib

namespace DB7EC1C5

lemma key (α δ : ℝ) (hδ : 0 < δ) :
    ∃ M : ℕ, 0 < M ∧ ∃ K : ℤ, 0 ≤ (M : ℝ) * α - K ∧ (M : ℝ) * α - K < δ := by
  set δ' := min δ 1 with hδ'
  have hδ'pos : 0 < δ' := lt_min hδ one_pos
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ'pos
  obtain ⟨j, k, hk0, hkn, hab⟩ :=
    Real.exists_int_int_abs_mul_sub_le α (Nat.succ_pos n)
  have hsmall : |(k : ℝ) * α - j| < δ' := by
    refine lt_of_le_of_lt hab (lt_of_le_of_lt ?_ hn)
    apply one_div_le_one_div_of_le (by positivity)
    push_cast; linarith
  have hδ'le : δ' ≤ δ := min_le_left _ _
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  have hkpos : 0 < k.toNat := by omega
  have hkc : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
    have : ((k.toNat : ℤ)) = k := Int.toNat_of_nonneg hk0.le
    exact_mod_cast this
  rcases le_or_gt 0 ((k : ℝ) * α - j) with hd | hd
  · refine ⟨k.toNat, hkpos, j, ?_, ?_⟩
    · rw [hkc]; exact hd
    · rw [hkc]; exact lt_of_le_of_lt (le_abs_self _) (lt_of_lt_of_le hsmall hδ'le)
  · set e := j - (k : ℝ) * α with he
    have hepos : 0 < e := by linarith
    have helt : e < δ' := by
      have := neg_abs_le ((k : ℝ) * α - j)
      linarith
    set m := ⌊1 / e⌋₊ with hm
    have h1e : 1 ≤ 1 / e := by
      rw [le_div_iff₀ hepos]; linarith
    have hm1 : 1 ≤ m := Nat.le_floor (by simpa using h1e)
    have hmle : (m : ℝ) ≤ 1 / e := Nat.floor_le (by positivity)
    have hmlt : 1 / e < (m : ℝ) + 1 := Nat.lt_floor_add_one _
    have hme1 : (m : ℝ) * e ≤ 1 := by rwa [le_div_iff₀ hepos] at hmle
    have hme2 : 1 < ((m : ℝ) + 1) * e := by rwa [div_lt_iff₀ hepos] at hmlt
    refine ⟨m * k.toNat, Nat.mul_pos hm1 hkpos, m * j - 1, ?_, ?_⟩
    · push_cast; rw [hkc]
      have : (m : ℝ) * k * α - ((m : ℝ) * j - 1) = 1 - m * e := by rw [he]; ring
      rw [this]; linarith
    · push_cast; rw [hkc]
      have : (m : ℝ) * k * α - ((m : ℝ) * j - 1) = 1 - m * e := by rw [he]; ring
      rw [this]; nlinarith

end DB7EC1C5

theorem solution {q₁ q₂ : ℕ} (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hne : q₁ ≠ q₂)
    {μ : ℝ} (hμ : 0 < μ) :
    ∃ k₁ k₂ : ℕ, 0 < k₁ ∧ 1 ≤ (q₁ : ℝ) ^ k₁ / (q₂ : ℝ) ^ k₂ ∧
      (q₁ : ℝ) ^ k₁ / (q₂ : ℝ) ^ k₂ ≤ 1 + μ := by
  have h1 : (1 : ℝ) < q₁ := by exact_mod_cast hq₁.one_lt
  have h2 : (1 : ℝ) < q₂ := by exact_mod_cast hq₂.one_lt
  set L1 := Real.log q₁ with hL1
  set L2 := Real.log q₂ with hL2
  have hL1p : 0 < L1 := Real.log_pos h1
  have hL2p : 0 < L2 := Real.log_pos h2
  have hlμ : 0 < Real.log (1 + μ) := Real.log_pos (by linarith)
  set α := L1 / L2 with hα
  have hαp : 0 < α := div_pos hL1p hL2p
  set δ := min (Real.log (1 + μ) / L2) α with hδ
  have hδp : 0 < δ := lt_min (div_pos hlμ hL2p) hαp
  obtain ⟨M, hM, K, hK0, hKδ⟩ := DB7EC1C5.key α δ hδp
  have hδα : δ ≤ α := min_le_right _ _
  have hδl : δ ≤ Real.log (1 + μ) / L2 := min_le_left _ _
  have hMα : α ≤ (M : ℝ) * α := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hKpos : (0 : ℝ) < K := by linarith
  have hKnn : 0 ≤ K := by exact_mod_cast hKpos.le
  have hKc : ((K.toNat : ℕ) : ℝ) = (K : ℝ) := by
    have : ((K.toNat : ℤ)) = K := Int.toNat_of_nonneg hKnn
    exact_mod_cast this
  refine ⟨M, K.toNat, hM, ?_, ?_⟩
  · -- ratio = exp (L2 * (M α - K))
    have hx : (q₁ : ℝ) ^ M / (q₂ : ℝ) ^ K.toNat = Real.exp (L2 * ((M : ℝ) * α - K)) := by
      have e1 : (q₁ : ℝ) ^ M = Real.exp (M * L1) := by
        rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
      have e2 : (q₂ : ℝ) ^ K.toNat = Real.exp (K * L2) := by
        rw [← hKc, Real.exp_nat_mul, Real.exp_log (by linarith)]
      rw [e1, e2, ← Real.exp_sub]
      congr 1
      rw [hα]; field_simp
    rw [hx]; exact Real.one_le_exp (by positivity)
  · have hx : (q₁ : ℝ) ^ M / (q₂ : ℝ) ^ K.toNat = Real.exp (L2 * ((M : ℝ) * α - K)) := by
      have e1 : (q₁ : ℝ) ^ M = Real.exp (M * L1) := by
        rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
      have e2 : (q₂ : ℝ) ^ K.toNat = Real.exp (K * L2) := by
        rw [← hKc, Real.exp_nat_mul, Real.exp_log (by linarith)]
      rw [e1, e2, ← Real.exp_sub]
      congr 1
      rw [hα]; field_simp
    rw [hx, ← Real.exp_log (show (0:ℝ) < 1 + μ by linarith)]
    apply Real.exp_le_exp.mpr
    have : L2 * ((M : ℝ) * α - K) ≤ L2 * (Real.log (1 + μ) / L2) := by
      apply mul_le_mul_of_nonneg_left _ hL2p.le; linarith
    rwa [mul_div_cancel₀ _ hL2p.ne'] at this
