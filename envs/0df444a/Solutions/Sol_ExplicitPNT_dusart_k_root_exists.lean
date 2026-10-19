-- Prove2me | solution 1 for ExplicitPNT.dusart_k_root_exists
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T09:08:19.020721+00:00
-- url     : https://prove2.me/submissions/f31eec87-a167-4333-adc7-2dfb168a0af4

import Mathlib
set_option autoImplicit false

set_option maxHeartbeats 2000000 in
theorem solution (X : ℝ) (hX : (836 / 100 : ℝ) ≤ X) :
    ∃ ν : ℝ,
      (97 / 100 : ℝ) < 1 - Real.log (X / (2 * Real.pi)) / (2 * X) ∧
      1 - Real.log (X / (2 * Real.pi)) / (2 * X) < ν ∧ ν < 1 ∧
      X / (2 * Real.pi) *
          Real.sqrt ((ν ^ 2 * (ν - Real.log (2 * Real.pi) / X)) ^ 3 /
            (ν ^ 2 / (2 * ν ^ 2 - 1) *
              (ν + (1 - 2 * Real.log (2 * Real.pi)) / (2 * X)))) *
          Real.exp (-(2 * X * (1 - ν))) * Real.exp (-(X * (1 - ν) ^ 2 / ν)) = 1 := by
  have hXpos : 0 < X := by linarith
  have hpi1 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hpi2 : Real.pi < 3.141593 := Real.pi_lt_d6
  have hpipos : 0 < Real.pi := by linarith
  set c : ℝ := Real.log (2 * Real.pi) with hc
  have hc0 : 0 < c := Real.log_pos (by linarith)
  have hc1 : c < 1.839 := by
    rw [hc, Real.log_lt_iff_lt_exp (by linarith)]
    have h := Real.sum_le_exp_of_nonneg (x := (1.839 : ℝ)) (by norm_num) 14
    refine lt_of_lt_of_le ?_ h
    norm_num [Finset.sum_range_succ, Nat.factorial]
    linarith
  set L : ℝ := Real.log (X / (2 * Real.pi)) with hL
  have hXpi : 1 < X / (2 * Real.pi) := by
    rw [lt_div_iff₀ (by linarith)]; linarith
  have hL0 : 0 < L := Real.log_pos hXpi
  have hL1 : L < 0.06 * X := by
    rw [hL, Real.log_lt_iff_lt_exp (by linarith)]
    have h1 := Real.add_one_le_exp (0.06 * X - 1)
    have h2 : Real.exp (0.06 * X) = Real.exp 1 * Real.exp (0.06 * X - 1) := by
      rw [← Real.exp_add]; ring_nf
    have h3 := Real.exp_one_gt_d9
    rw [div_lt_iff₀ (by linarith), h2]
    have h4 : 0 < Real.exp (0.06 * X - 1) := Real.exp_pos _
    have h6 : (2.7 : ℝ) * 3.14 < Real.exp 1 * Real.pi :=
      mul_lt_mul'' (by linarith : (2.7:ℝ) < Real.exp 1) hpi1 (by norm_num) (by norm_num)
    have h7 : 0.06 * X ≤ Real.exp (0.06 * X - 1) := by linarith
    have h8 : (Real.exp 1 * Real.pi) * (0.06 * X) ≤ (Real.exp 1 * Real.pi) * Real.exp (0.06 * X - 1) :=
      mul_le_mul_of_nonneg_left h7 (by positivity)
    nlinarith
  set ν0 : ℝ := 1 - L / (2 * X) with hν0
  have hLX : L / (2 * X) < 0.03 := by
    rw [div_lt_iff₀ (by linarith)]; linarith
  have hLX0 : 0 < L / (2 * X) := by positivity
  have hν0a : (97 / 100 : ℝ) < ν0 := by rw [hν0]; linarith
  have hν0b : ν0 < 1 := by rw [hν0]; linarith
  have hcX : c / X < 1 / 2 := by
    rw [div_lt_iff₀ hXpos]; linarith
  have hcX0 : 0 < c / X := by positivity
  have hX2 : 0 < 1 / (2 * X) := by positivity
  -- the function
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = fun ν =>
    X / (2 * Real.pi) *
          Real.sqrt ((ν ^ 2 * (ν - c / X)) ^ 3 /
            (ν ^ 2 / (2 * ν ^ 2 - 1) *
              (ν + (1 - 2 * c) / (2 * X)))) *
          Real.exp (-(2 * X * (1 - ν))) * Real.exp (-(X * (1 - ν) ^ 2 / ν)) := ⟨_, rfl⟩
  have hB : ∀ ν : ℝ, ν + (1 - 2 * c) / (2 * X) = (ν - c / X) + 1 / (2 * X) := by
    intro ν; field_simp; ring
  -- continuity
  have hcont : ContinuousOn F (Set.Icc ν0 1) := by
    rw [hF]
    have hν : ∀ ν ∈ Set.Icc ν0 1, 97 / 100 < ν := fun ν hν => by
      have := hν.1; linarith
    have hden1 : ∀ ν ∈ Set.Icc ν0 1, 2 * ν ^ 2 - 1 ≠ 0 := fun ν h => by
      have := hν ν h; nlinarith
    have hden2 : ∀ ν ∈ Set.Icc ν0 1, ν ^ 2 / (2 * ν ^ 2 - 1) *
              (ν + (1 - 2 * c) / (2 * X)) ≠ 0 := fun ν h => by
      have h1 := hν ν h
      have h2 : 0 < 2 * ν ^ 2 - 1 := by nlinarith
      have h3 : 0 < ν + (1 - 2 * c) / (2 * X) := by rw [hB]; linarith
      positivity
    have hden3 : ∀ ν ∈ Set.Icc ν0 1, ν ≠ 0 := fun ν h => by
      have := hν ν h; linarith
    have e1 : ContinuousOn (fun ν : ℝ => ν ^ 2 / (2 * ν ^ 2 - 1)) (Set.Icc ν0 1) :=
      ContinuousOn.div (by fun_prop) (by fun_prop) hden1
    have e2 : ContinuousOn (fun ν : ℝ => (ν ^ 2 * (ν - c / X)) ^ 3 /
            (ν ^ 2 / (2 * ν ^ 2 - 1) * (ν + (1 - 2 * c) / (2 * X)))) (Set.Icc ν0 1) :=
      ContinuousOn.div (by fun_prop) (e1.mul (by fun_prop)) hden2
    have e3 : ContinuousOn (fun ν : ℝ => X * (1 - ν) ^ 2 / ν) (Set.Icc ν0 1) :=
      ContinuousOn.div (by fun_prop) (by fun_prop) hden3
    have e4 := Real.continuous_sqrt.comp_continuousOn e2
    have e5 : ContinuousOn (fun ν : ℝ => Real.exp (-(2 * X * (1 - ν)))) (Set.Icc ν0 1) :=
      (Real.continuous_exp.comp (by fun_prop : Continuous fun ν : ℝ => -(2 * X * (1 - ν)))).continuousOn
    have e6 := Real.continuous_exp.comp_continuousOn e3.neg
    exact (((continuousOn_const.mul e4).mul e5).mul e6)
  -- value at ν0
  have hF0 : F ν0 < 1 := by
    have ha : 0 < ν0 - c / X := by linarith
    have ha1 : ν0 - c / X < 1 := by linarith
    have hb : ν0 - c / X < ν0 + (1 - 2 * c) / (2 * X) := by rw [hB]; linarith
    have hQ : (ν0 ^ 2 * (ν0 - c / X)) ^ 3 /
            (ν0 ^ 2 / (2 * ν0 ^ 2 - 1) * (ν0 + (1 - 2 * c) / (2 * X))) < 1 := by
      have h2 : 0 < 2 * ν0 ^ 2 - 1 := by nlinarith
      have hBpos : 0 < ν0 + (1 - 2 * c) / (2 * X) := by linarith
      have hden : 0 < ν0 ^ 2 / (2 * ν0 ^ 2 - 1) * (ν0 + (1 - 2 * c) / (2 * X)) := by positivity
      rw [div_lt_one hden, div_mul_eq_mul_div, lt_div_iff₀ h2]
      set a := ν0 - c / X
      set B := ν0 + (1 - 2 * c) / (2 * X)
      have hν2 : 0 < ν0 ^ 2 := by positivity
      have h4 : ν0 ^ 4 * (2 * ν0 ^ 2 - 1) ≤ 1 := by
        have hp : ν0 ^ 2 < 1 := by nlinarith
        have hp0 : 0 < ν0 ^ 2 := hν2
        have : ν0 ^ 4 = (ν0 ^ 2) ^ 2 := by ring
        rw [this]
        nlinarith [mul_pos hp0 hp0]
      have h5 : a ^ 3 < B := by
        have : a ^ 3 ≤ a := by nlinarith [pow_pos ha 2]
        linarith
      have h6 : 0 < a ^ 3 := by positivity
      have h7 : 0 < ν0 ^ 4 * (2 * ν0 ^ 2 - 1) := by positivity
      calc (ν0 ^ 2 * a) ^ 3 * (2 * ν0 ^ 2 - 1)
          = ν0 ^ 2 * ((ν0 ^ 4 * (2 * ν0 ^ 2 - 1)) * a ^ 3) := by ring
        _ < ν0 ^ 2 * B := by
          apply mul_lt_mul_of_pos_left _ hν2
          nlinarith
    have hsq : Real.sqrt ((ν0 ^ 2 * (ν0 - c / X)) ^ 3 /
            (ν0 ^ 2 / (2 * ν0 ^ 2 - 1) * (ν0 + (1 - 2 * c) / (2 * X)))) < 1 := by
      rw [Real.sqrt_lt' one_pos]; simpa using hQ
    have h1 : 2 * X * (1 - ν0) = L := by rw [hν0]; field_simp; ring
    have h2 : X / (2 * Real.pi) * Real.exp (-(2 * X * (1 - ν0))) = 1 := by
      rw [h1, Real.exp_neg, hL, Real.exp_log (by linarith)]
      field_simp
    have h3 : Real.exp (-(X * (1 - ν0) ^ 2 / ν0)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ X * (1 - ν0) ^ 2 / ν0 := by
        have : 0 < ν0 := by linarith
        positivity
      linarith
    have h4 : 0 ≤ Real.sqrt ((ν0 ^ 2 * (ν0 - c / X)) ^ 3 /
            (ν0 ^ 2 / (2 * ν0 ^ 2 - 1) * (ν0 + (1 - 2 * c) / (2 * X)))) := Real.sqrt_nonneg _
    have h5 : 0 < Real.exp (-(X * (1 - ν0) ^ 2 / ν0)) := Real.exp_pos _
    simp only [hF]
    set S := Real.sqrt ((ν0 ^ 2 * (ν0 - c / X)) ^ 3 /
            (ν0 ^ 2 / (2 * ν0 ^ 2 - 1) * (ν0 + (1 - 2 * c) / (2 * X))))
    calc X / (2 * Real.pi) * S * Real.exp (-(2 * X * (1 - ν0))) *
          Real.exp (-(X * (1 - ν0) ^ 2 / ν0))
        = S * (X / (2 * Real.pi) * Real.exp (-(2 * X * (1 - ν0)))) *
          Real.exp (-(X * (1 - ν0) ^ 2 / ν0)) := by ring
      _ = S * Real.exp (-(X * (1 - ν0) ^ 2 / ν0)) := by rw [h2]; ring
      _ ≤ S * 1 := mul_le_mul_of_nonneg_left h3 h4
      _ < 1 := by rw [mul_one]; exact hsq
  -- value at 1
  have hF1 : 1 < F 1 := by
    have e : F 1 = X / (2 * Real.pi) * Real.sqrt (((1:ℝ) ^ 2 * (1 - c / X)) ^ 3 /
            ((1:ℝ) ^ 2 / (2 * 1 ^ 2 - 1) * (1 + (1 - 2 * c) / (2 * X)))) := by
      rw [hF]; simp
    rw [e]
    have hu : (6.521 : ℝ) ≤ X - c := by linarith
    have hπ2 : Real.pi ^ 2 < 9.8697 := by nlinarith
    have hu2 : (42.52 : ℝ) ≤ (X - c) ^ 2 := by nlinarith
    have key : 2 * Real.pi ^ 2 * (2 * (X - c) + 1) < (X - c) ^ 3 := by
      have h1 : 42.52 * (X - c) ≤ (X - c) ^ 3 := by
        have : (X - c) ^ 3 = (X - c) * (X - c) ^ 2 := by ring
        rw [this]; nlinarith
      have h2 : Real.pi ^ 2 * (4 * (X - c)) ≤ 9.8697 * (4 * (X - c)) :=
        mul_le_mul_of_nonneg_right hπ2.le (by linarith)
      nlinarith
    have e1 : (1:ℝ) ^ 2 * (1 - c / X) = (X - c) / X := by field_simp
    have e2 : (1:ℝ) ^ 2 / (2 * 1 ^ 2 - 1) * (1 + (1 - 2 * c) / (2 * X)) = (2 * (X - c) + 1) / (2 * X) := by
      field_simp; ring
    rw [e1, e2]
    have hu0 : 0 < X - c := by linarith
    have hQ : (2 * Real.pi / X) ^ 2 < ((X - c) / X) ^ 3 / ((2 * (X - c) + 1) / (2 * X)) := by
      rw [lt_div_iff₀ (by positivity), div_pow, div_pow, div_mul_div_comm,
        div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos (pow_pos hXpos 3) (sub_pos.2 key)]
    have hS : 2 * Real.pi / X < Real.sqrt (((X - c) / X) ^ 3 / ((2 * (X - c) + 1) / (2 * X))) :=
      Real.lt_sqrt (by positivity) |>.2 hQ
    have h2pi : 0 < X / (2 * Real.pi) := by positivity
    calc (1:ℝ) = X / (2 * Real.pi) * (2 * Real.pi / X) := by field_simp
      _ < _ := mul_lt_mul_of_pos_left hS h2pi
  -- IVT
  have h1 : (1:ℝ) ∈ Set.Icc (F ν0) (F 1) := ⟨hF0.le, hF1.le⟩
  obtain ⟨ν, hν, hνF⟩ := intermediate_value_Icc hν0b.le hcont h1
  have hν1 : ν ≠ 1 := by
    rintro rfl; linarith
  have hνa : ν ≠ ν0 := by
    rintro rfl; linarith
  refine ⟨ν, hν0a, lt_of_le_of_ne hν.1 (Ne.symm hνa), lt_of_le_of_ne hν.2 hν1, ?_⟩
  rw [hF] at hνF
  exact hνF
