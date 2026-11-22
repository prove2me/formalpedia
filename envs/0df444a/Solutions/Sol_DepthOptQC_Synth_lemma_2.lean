-- Prove2me | solution 1 for DepthOptQC.Synth.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T07:50:10.019428+00:00
-- url     : https://prove2.me/submissions/094d3a9b-c203-4896-8f2b-2a2128268bf4

import Mathlib

theorem solution (θ ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (m : ℕ)
    (hm : ⌈Real.logb 2 (2 * Real.sqrt 2 / ε)⌉ ≤ (m : ℤ)) :
    ∃ n : Fin 4 → ℕ, ∑ j, n j = 2 ^ m ∧
      ‖(((n 0 : ℂ) - n 1) + Complex.I * ((n 2 : ℂ) - n 3)) / 2 ^ m
          - Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) / 2‖ ≤ ε := by
  -- Error budget.
  have hxpos : 0 < 2 * Real.sqrt 2 / ε := by positivity
  have hlog : Real.logb 2 (2 * Real.sqrt 2 / ε) ≤ (m : ℝ) := by
    have h := Int.ceil_le.mp hm
    rwa [Int.cast_natCast] at h
  have hbound : 2 * Real.sqrt 2 / ε ≤ (2 : ℝ) ^ m := by
    have h := (Real.logb_le_iff_le_rpow (b := 2) (x := 2 * Real.sqrt 2 / ε)
      (y := (m : ℝ)) (by norm_num) hxpos).mp hlog
    rwa [Real.rpow_natCast] at h
  have hbudget : 2 * Real.sqrt 2 ≤ ε * (2 : ℝ) ^ m := by
    have h := (div_le_iff₀ hε0).mp hbound
    linarith
  -- The admissible m are at least 2.
  have hPpos : 0 < (2 : ℝ) ^ m := pow_pos (by norm_num) m
  have hm2 : 2 ≤ m := by
    by_contra h
    push Not at h
    have hPle : (2 : ℝ) ^ m ≤ 2 := by
      interval_cases m <;> norm_num
    have hsqrt1 : 1 ≤ Real.sqrt 2 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by norm_num)
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  -- Data for the rounding: z = A + i B is the target.
  set A : ℝ := (2 : ℝ) ^ m / 2 * Real.cos (θ / 2) with hA
  set B : ℝ := (2 : ℝ) ^ m / 2 * Real.sin (θ / 2) with hB
  set a : ℤ := 2 * round (A / 2) with ha
  set b : ℤ := 2 * round (B / 2) with hb
  -- Rounding error.
  have hroundA : |A / 2 - (round (A / 2) : ℝ)| ≤ 1 / 2 := by
    rw [abs_sub_round_eq_min]
    rw [min_le_iff]
    rcases le_or_gt (Int.fract (A / 2)) (1 / 2) with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith [Int.fract_lt_one (A / 2)])
  have hroundB : |B / 2 - (round (B / 2) : ℝ)| ≤ 1 / 2 := by
    rw [abs_sub_round_eq_min]
    rw [min_le_iff]
    rcases le_or_gt (Int.fract (B / 2)) (1 / 2) with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith [Int.fract_lt_one (B / 2)])
  have ha_close : |(a : ℝ) - A| ≤ 1 := by
    have h1 : (a : ℝ) - A = 2 * ((round (A / 2) : ℝ) - A / 2) := by
      rw [ha]
      push_cast
      ring
    rw [h1, abs_mul]
    have h2 : |(round (A / 2) : ℝ) - A / 2| ≤ 1 / 2 := by
      rwa [abs_sub_comm]
    nlinarith [abs_nonneg ((round (A / 2) : ℝ) - A / 2)]
  have hb_close : |(b : ℝ) - B| ≤ 1 := by
    have h1 : (b : ℝ) - B = 2 * ((round (B / 2) : ℝ) - B / 2) := by
      rw [hb]
      push_cast
      ring
    rw [h1, abs_mul]
    have h2 : |(round (B / 2) : ℝ) - B / 2| ≤ 1 / 2 := by
      rwa [abs_sub_comm]
    nlinarith [abs_nonneg ((round (B / 2) : ℝ) - B / 2)]
  -- Size bound: |A| + |B| < 2^m - 1.
  have hAB : |A| + |B| < (2 : ℝ) ^ m - 1 := by
    have hcs : |Real.cos (θ / 2)| + |Real.sin (θ / 2)| ≤ Real.sqrt 2 := by
      have hsq : (|Real.cos (θ / 2)| + |Real.sin (θ / 2)|) ^ 2 ≤ 2 := by
        have h1 : Real.cos (θ / 2) ^ 2 + Real.sin (θ / 2) ^ 2 = 1 :=
          Real.cos_sq_add_sin_sq (θ / 2)
        have h2 : |Real.cos (θ / 2)| ^ 2 = Real.cos (θ / 2) ^ 2 := sq_abs _
        have h3 : |Real.sin (θ / 2)| ^ 2 = Real.sin (θ / 2) ^ 2 := sq_abs _
        nlinarith [sq_nonneg (|Real.cos (θ / 2)| - |Real.sin (θ / 2)|)]
      calc |Real.cos (θ / 2)| + |Real.sin (θ / 2)|
          = Real.sqrt ((|Real.cos (θ / 2)| + |Real.sin (θ / 2)|) ^ 2) := by
            rw [Real.sqrt_sq (by positivity)]
        _ ≤ Real.sqrt 2 := Real.sqrt_le_sqrt hsq
    have hcos : |Real.cos (θ / 2)| ≤ Real.sqrt 2 := by
      linarith [abs_nonneg (Real.sin (θ / 2))]
    have hsin : |Real.sin (θ / 2)| ≤ Real.sqrt 2 := by
      linarith [abs_nonneg (Real.cos (θ / 2))]
    have hsum : |A| + |B| = (2 : ℝ) ^ m / 2 * (|Real.cos (θ / 2)| + |Real.sin (θ / 2)|) := by
      rw [hA, hB, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ m / 2)]
      ring
    rw [hsum]
    have hP4 : 4 ≤ (2 : ℝ) ^ m := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := by
            apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm2
    nlinarith [Real.sqrt_two_lt_three_halves, hcs, hPpos]
  have hS_close_real : ((|a| + |b| : ℤ) : ℝ) < ((2 ^ m : ℤ) : ℝ) + 1 := by
    have h1 : (|a| : ℝ) ≤ |A| + 1 := by
      have h := abs_sub_abs_le_abs_sub (a : ℝ) A
      linarith [abs_nonneg (a : ℝ), abs_nonneg A]
    have h2 : (|b| : ℝ) ≤ |B| + 1 := by
      have h := abs_sub_abs_le_abs_sub (b : ℝ) B
      linarith [abs_nonneg (b : ℝ), abs_nonneg B]
    have hcast : ((|a| + |b| : ℤ) : ℝ) = (|a| : ℝ) + (|b| : ℝ) := by push_cast; ring
    have h2m : (((2 ^ m : ℤ)) : ℝ) = (2 : ℝ) ^ m := by push_cast; ring
    rw [hcast, h2m]
    linarith
  have hS_close : (|a| + |b| : ℤ) < (2 ^ m : ℤ) + 1 := by
    exact_mod_cast hS_close_real
  have hS_le : |a| + |b| ≤ (2 ^ m : ℤ) := by
    have h := hS_close
    omega
  -- Parity: a + b is even, and so is |a| + |b|.
  have hSdvd : (2 : ℤ) ∣ (|a| + |b|) := by
    obtain ⟨ka, hka⟩ : ∃ k : ℤ, a = 2 * k := ⟨round (A / 2), by rw [ha]⟩
    obtain ⟨kb, hkb⟩ : ∃ k : ℤ, b = 2 * k := ⟨round (B / 2), by rw [hb]⟩
    refine ⟨|ka| + |kb|, ?_⟩
    have e1 : |a| = 2 * |ka| := by
      rw [hka, abs_mul]
      norm_num
    have e2 : |b| = 2 * |kb| := by
      rw [hkb, abs_mul]
      norm_num
    rw [e1, e2]
    ring
  have h2mdvd : (2 : ℤ) ∣ (2 ^ m : ℤ) := by
    have hm1 : m = (m - 1) + 1 := by omega
    have h2m_eq : (2 : ℤ) ^ m = 2 * (2 : ℤ) ^ (m - 1) := by
      conv_lhs => rw [hm1]
      rw [pow_succ]
      ring
    exact ⟨(2 : ℤ) ^ (m - 1), h2m_eq⟩
  have hdiffdvd : (2 : ℤ) ∣ (2 ^ m : ℤ) - (|a| + |b|) := Int.dvd_sub h2mdvd hSdvd
  -- The padding r.
  set r : ℤ := ((2 ^ m : ℤ) - (|a| + |b|)) / 2 with hr
  have hr_nonneg : 0 ≤ r := by
    rw [hr]
    apply Int.ediv_nonneg
    · omega
    · norm_num
  have hr_eq : 2 * r = (2 ^ m : ℤ) - (|a| + |b|) := by
    rw [hr]
    exact Int.mul_ediv_cancel' hdiffdvd
  -- Nonnegative integer coordinates.
  have hn0 : (0 : ℤ) ≤ max a 0 + r := by
    have := le_max_right a 0
    linarith
  have hn1 : (0 : ℤ) ≤ max (-a) 0 + r := by
    have := le_max_right (-a) 0
    linarith
  have hn2 : (0 : ℤ) ≤ max b 0 := le_max_right b 0
  have hn3 : (0 : ℤ) ≤ max (-b) 0 := le_max_right (-b) 0
  -- The quadruple.
  let n : Fin 4 → ℕ := fun j =>
    if j = 0 then (max a 0 + r).toNat
    else if j = 1 then (max (-a) 0 + r).toNat
    else if j = 2 then (max b 0).toNat
    else (max (-b) 0).toNat
  have hn0v : n 0 = (max a 0 + r).toNat := by simp [n]
  have hn1v : n 1 = (max (-a) 0 + r).toNat := by simp [n]
  have hn2v : n 2 = (max b 0).toNat := by simp [n]
  have hn3v : n 3 = (max (-b) 0).toNat := by simp [n]
  have hdifa : ((n 0 : ℤ) - n 1) = a := by
    rw [hn0v, hn1v, Int.toNat_of_nonneg hn0, Int.toNat_of_nonneg hn1]
    have h1 : max a 0 + r - (max (-a) 0 + r) = max a 0 - max (-a) 0 := by ring
    rw [h1]
    rcases le_or_gt 0 a with h | h
    · rw [max_eq_left h, max_eq_right (by linarith : -a ≤ 0)]; ring
    · rw [max_eq_right (le_of_lt h), max_eq_left (by linarith : 0 ≤ -a)]; ring
  have hdifb : ((n 2 : ℤ) - n 3) = b := by
    rw [hn2v, hn3v, Int.toNat_of_nonneg hn2, Int.toNat_of_nonneg hn3]
    rcases le_or_gt 0 b with h | h
    · rw [max_eq_left h, max_eq_right (by linarith : -b ≤ 0)]; ring
    · rw [max_eq_right (le_of_lt h), max_eq_left (by linarith : 0 ≤ -b)]; ring
  have hsum : ∑ j, n j = 2 ^ m := by
    apply Nat.cast_injective (R := ℤ)
    rw [Fin.sum_univ_four]
    push_cast
    rw [hn0v, hn1v, hn2v, hn3v]
    rw [Int.toNat_of_nonneg hn0, Int.toNat_of_nonneg hn1, Int.toNat_of_nonneg hn2,
      Int.toNat_of_nonneg hn3]
    have h1 : max a 0 + max (-a) 0 = |a| := by
      rcases le_or_gt 0 a with h | h
      · rw [max_eq_left h, max_eq_right (by linarith : -a ≤ 0), abs_of_nonneg h]; ring
      · rw [max_eq_right (le_of_lt h), max_eq_left (by linarith : 0 ≤ -a), abs_of_neg h]; ring
    have h2 : max b 0 + max (-b) 0 = |b| := by
      rcases le_or_gt 0 b with h | h
      · rw [max_eq_left h, max_eq_right (by linarith : -b ≤ 0), abs_of_nonneg h]; ring
      · rw [max_eq_right (le_of_lt h), max_eq_left (by linarith : 0 ≤ -b), abs_of_neg h]; ring
    linarith [h1, h2, hr_eq]
  refine ⟨n, hsum, ?_⟩
  -- The complex norm bound.
  have hE : Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) =
      (Real.cos (θ / 2) : ℂ) + (Real.sin (θ / 2) : ℂ) * Complex.I :=
    Complex.exp_ofReal_mul_I (θ / 2)
  have hwa : ((n 0 : ℂ) - n 1) = (a : ℂ) := by
    have h : ((n 0 : ℤ) - (n 1 : ℤ)) = a := hdifa
    exact_mod_cast h
  have hwb : ((n 2 : ℂ) - n 3) = (b : ℂ) := by
    have h : ((n 2 : ℤ) - (n 3 : ℤ)) = b := hdifb
    exact_mod_cast h
  have hkey : (((n 0 : ℂ) - n 1) + Complex.I * ((n 2 : ℂ) - n 3)) / ((2 : ℂ) ^ m)
      - Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) / 2
      = ((a : ℂ) - (A : ℂ) + ((b : ℂ) - (B : ℂ)) * Complex.I) / ((2 : ℂ) ^ m) := by
    rw [hE, hwa, hwb]
    have h2m : ((2 : ℂ) ^ m) ≠ 0 := pow_ne_zero m (by norm_num)
    push_cast
    field_simp
    simp only [hA, hB]
    push_cast
    ring
  rw [hkey]
  have hden : ‖((2 : ℂ) ^ m)‖ = (2 : ℝ) ^ m := by
    rw [Complex.norm_pow]
    norm_num
  rw [Complex.norm_div, hden]
  have hnum : ‖(a : ℂ) - (A : ℂ) + ((b : ℂ) - (B : ℂ)) * Complex.I‖ ≤ 2 * Real.sqrt 2 := by
    have heq : (a : ℂ) - (A : ℂ) + ((b : ℂ) - (B : ℂ)) * Complex.I =
        ((a - A : ℝ) : ℂ) + ((b - B : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [heq, Complex.norm_def, Complex.normSq_add_mul_I]
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have h1 : ((a : ℝ) - A) ^ 2 ≤ 1 := by
        have h := ha_close
        have hs : ((a : ℝ) - A) ^ 2 = |(a : ℝ) - A| ^ 2 := (sq_abs _).symm
        rw [hs]
        nlinarith [abs_nonneg ((a : ℝ) - A)]
      have h2 : ((b : ℝ) - B) ^ 2 ≤ 1 := by
        have h := hb_close
        have hs : ((b : ℝ) - B) ^ 2 = |(b : ℝ) - B| ^ 2 := (sq_abs _).symm
        rw [hs]
        nlinarith [abs_nonneg ((b : ℝ) - B)]
      have : (2 * Real.sqrt 2) ^ 2 = 8 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num)]
        norm_num
      nlinarith
  calc ‖(a : ℂ) - (A : ℂ) + ((b : ℂ) - (B : ℂ)) * Complex.I‖ / (2 : ℝ) ^ m
      ≤ (2 * Real.sqrt 2) / (2 : ℝ) ^ m := by gcongr
    _ ≤ ε := by
        rw [div_le_iff₀ (pow_pos (by norm_num) m)]
        linarith
