-- Prove2me | solution 1 for CODATA2022.blackbody_exitance_eq_stefanBoltzmann
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:25:56.831925+00:00
-- url     : https://prove2.me/submissions/3c10de40-5b74-4cee-9a3d-7e0fd18f6db3

import Mathlib
import Definitions.Def_CODATA2022_si_defining_constants
import Definitions.Def_CODATA2022_radiation_constants

open MeasureTheory
open CODATA2022

/-- Convexity of `exp`: for `0 < a < b`, `exp (-a) ≤ (1 - a/b) + (a/b) exp (-b)`. -/
theorem W7b_CODATA2022_conv (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Real.exp (-a) ≤ (1 - a / b) + (a / b) * Real.exp (-b) := by
  have hb : 0 < b := ha.trans hab
  have hμ : 0 ≤ 1 - a / b := by rw [sub_nonneg, div_le_one hb]; exact hab.le
  have hla : 0 ≤ a / b := by positivity
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-b)) hμ hla (by ring)
  have e : (1 - a / b) • (0 : ℝ) + (a / b) • (-b) = -a := by
    simp only [smul_eq_mul]; field_simp; ring
  rw [e] at h
  simpa [smul_eq_mul, Real.exp_zero] using h

theorem W7b_CODATA2022_root_between (c x lo hi : ℝ) (hc : 0 < c) (hx : 0 < x)
    (hxeq : x = c * (1 - Real.exp (-x))) (hlo0 : 0 < lo) (hhi0 : 0 < hi)
    (hlo : Real.exp (-lo) < 1 - lo / c) (hhi : 1 - hi / c < Real.exp (-hi)) :
    lo < x ∧ x < hi := by
  have hex : Real.exp (-x) = 1 - x / c := by
    field_simp; linarith
  constructor
  · by_contra hcon
    push_neg at hcon
    rcases hcon.lt_or_eq with hlt | heq
    · have h1 := W7b_CODATA2022_conv x lo hx hlt
      have h2 : (x / lo) * Real.exp (-lo) < (x / lo) * (1 - lo / c) :=
        mul_lt_mul_of_pos_left hlo (by positivity)
      have h3 : (1 - x / lo) + (x / lo) * (1 - lo / c) = 1 - x / c := by
        field_simp; ring
      linarith
    · rw [heq] at hex; linarith
  · by_contra hcon
    push_neg at hcon
    rcases hcon.lt_or_eq with hlt | heq
    · have h1 := W7b_CODATA2022_conv hi x hhi0 hlt
      rw [hex] at h1
      have h3 : (1 - hi / x) + (hi / x) * (1 - x / c) = 1 - hi / c := by
        field_simp; ring
      linarith
    · rw [← heq] at hex; linarith

/-- `exp (-(k t)) = 1 / (exp t)^k`. -/
theorem W7b_CODATA2022_exp_neg_mul (t : ℝ) (k : ℕ) :
    Real.exp (-(k * t)) = 1 / (Real.exp t) ^ k := by
  rw [Real.exp_neg, ← Real.exp_nat_mul, one_div]

theorem W7b_CODATA2022_upper (t : ℝ) (ht : 0 ≤ t) (k n : ℕ) (hk : 0 < k) (B : ℝ)
    (hB : 1 / (∑ m ∈ Finset.range n, t ^ m / m.factorial) ^ k < B)
    (hS : 0 < ∑ m ∈ Finset.range n, t ^ m / m.factorial) :
    Real.exp (-(k * t)) < B := by
  rw [W7b_CODATA2022_exp_neg_mul]
  refine lt_of_le_of_lt ?_ hB
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_left₀ hS.le (Real.sum_le_exp_of_nonneg ht n) k

theorem W7b_CODATA2022_lower (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (k n : ℕ) (hn : 0 < n) (B : ℝ)
    (hB : B < 1 / ((∑ m ∈ Finset.range n, t ^ m / m.factorial) +
      t ^ n * (n + 1) / (n.factorial * n)) ^ k) :
    B < Real.exp (-(k * t)) := by
  rw [W7b_CODATA2022_exp_neg_mul]
  refine lt_of_lt_of_le hB ?_
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_left₀ (Real.exp_pos t).le (Real.exp_bound' ht ht1 hn) k

theorem W7b_CODATA2022_x3 (x : ℝ) (hx : 0 < x) (hxeq : x = 3 * (1 - Real.exp (-x))) :
    (28214393719 / 10000000000 : ℝ) < x ∧ x < 28214393722 / 10000000000 := by
  apply W7b_CODATA2022_root_between 3 x _ _ (by norm_num) hx hxeq (by norm_num) (by norm_num)
  · have e : (28214393719 / 10000000000 : ℝ) = ((4 : ℕ) : ℝ) * (28214393719 / 40000000000) := by
      norm_num
    rw [e]
    apply W7b_CODATA2022_upper _ (by norm_num) 4 14 (by norm_num)
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  · have e : (28214393722 / 10000000000 : ℝ) = ((4 : ℕ) : ℝ) * (28214393722 / 40000000000) := by
      norm_num
    rw [e]
    apply W7b_CODATA2022_lower _ (by norm_num) (by norm_num) 4 14 (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial]

theorem W7b_CODATA2022_x5 (x : ℝ) (hx : 0 < x) (hxeq : x = 5 * (1 - Real.exp (-x))) :
    (49651142315 / 10000000000 : ℝ) < x ∧ x < 49651142319 / 10000000000 := by
  apply W7b_CODATA2022_root_between 5 x _ _ (by norm_num) hx hxeq (by norm_num) (by norm_num)
  · have e : (49651142315 / 10000000000 : ℝ) = ((8 : ℕ) : ℝ) * (49651142315 / 80000000000) := by
      norm_num
    rw [e]
    apply W7b_CODATA2022_upper _ (by norm_num) 8 14 (by norm_num)
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  · have e : (49651142319 / 10000000000 : ℝ) = ((8 : ℕ) : ℝ) * (49651142319 / 80000000000) := by
      norm_num
    rw [e]
    apply W7b_CODATA2022_lower _ (by norm_num) (by norm_num) 8 14 (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial]

theorem W7b_CODATA2022_wienFrequencyConstant_bounds (x : ℝ) (hx : 0 < x)
    (hxeq : x = 3 * (1 - Real.exp (-x))) :
    5.878925757e10 < x * boltzmannConstant / planckConstant ∧
      x * boltzmannConstant / planckConstant < 5.878925758e10 := by
  obtain ⟨h1, h2⟩ := W7b_CODATA2022_x3 x hx hxeq
  unfold boltzmannConstant planckConstant
  constructor
  · rw [lt_div_iff₀ (by norm_num)]
    nlinarith
  · rw [div_lt_iff₀ (by norm_num)]
    nlinarith

theorem W7b_CODATA2022_wienDisplacementConstant_bounds (x : ℝ) (hx : 0 < x)
    (hxeq : x = 5 * (1 - Real.exp (-x))) :
    2.897771955e-3 < secondRadiationConstant / x ∧
      secondRadiationConstant / x < 2.897771956e-3 := by
  obtain ⟨h1, h2⟩ := W7b_CODATA2022_x5 x hx hxeq
  unfold secondRadiationConstant boltzmannConstant planckConstant speedOfLight
  constructor
  · rw [lt_div_iff₀ hx]
    nlinarith
  · rw [div_lt_iff₀ hx]
    nlinarith

theorem W7b_CODATA2022_geom (t : ℝ) (ht : 0 < t) :
    HasSum (fun i : ℕ => Real.exp (-((i : ℝ) + 1) * t)) (1 / (Real.exp t - 1)) := by
  have h1 : Real.exp (-t) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hg := (hasSum_geometric_of_lt_one (Real.exp_pos (-t)).le h1).mul_left (Real.exp (-t))
  have hne : Real.exp t - 1 ≠ 0 := by
    have : 1 < Real.exp t := Real.one_lt_exp_iff.mpr ht
    linarith
  have hfun : (fun i : ℕ => Real.exp (-((i : ℝ) + 1) * t)) =
      fun i : ℕ => Real.exp (-t) * Real.exp (-t) ^ i := by
    funext i
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; ring
  rw [hfun]
  have hval : 1 / (Real.exp t - 1) = Real.exp (-t) * (1 - Real.exp (-t))⁻¹ := by
    rw [Real.exp_neg]
    have hpos := Real.exp_pos t
    have h1' : 1 < Real.exp t := Real.one_lt_exp_iff.mpr ht
    have : 1 - (Real.exp t)⁻¹ ≠ 0 := by
      rw [sub_ne_zero]; intro h
      have := congrArg (·⁻¹) h; simp at this; linarith
    field_simp
  rw [hval]; exact hg

theorem W7b_CODATA2022_bose_einstein_integral_cube :
    (∫ x in Set.Ioi (0 : ℝ), x ^ 3 / (Real.exp x - 1)) = Real.pi ^ 4 / 15 := by
  have hs : (0 : ℝ) < (4 : ℂ).re := by norm_num
  have hF : ∀ t ∈ Set.Ioi (0 : ℝ), HasSum (fun i : ℕ => (fun _ => (1 : ℂ)) i *
      (Real.exp (-((fun i : ℕ => (i : ℝ) + 1) i) * t) : ℂ))
      ((fun t : ℝ => ((1 / (Real.exp t - 1) : ℝ) : ℂ)) t) := by
    intro t ht
    simp only [one_mul]
    exact Complex.hasSum_ofReal.mpr (W7b_CODATA2022_geom t ht)
  have hsum : Summable fun i : ℕ => ‖(fun _ => (1 : ℂ)) i‖ /
      ((fun i : ℕ => (i : ℝ) + 1) i) ^ (4 : ℂ).re := by
    simp only [norm_one]
    have h4 : (4 : ℂ).re = 4 := by norm_num
    rw [h4]
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1:ℝ) < 4))
    simpa [Nat.cast_add, Nat.cast_one] using this
  have hM := hasSum_mellin (a := fun _ => (1 : ℂ)) (p := fun i : ℕ => (i : ℝ) + 1)
    (F := fun t : ℝ => ((1 / (Real.exp t - 1) : ℝ) : ℂ)) (s := 4)
    (fun i => Or.inr (by positivity)) hs hF hsum
  have hmel : mellin (fun t : ℝ => ((1 / (Real.exp t - 1) : ℝ) : ℂ)) 4 =
      ((∫ x in Set.Ioi (0 : ℝ), x ^ 3 / (Real.exp x - 1) : ℝ) : ℂ) := by
    unfold mellin
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have h3 : (4 : ℂ) - 1 = ((3 : ℕ) : ℂ) := by norm_num
    simp only [smul_eq_mul]
    rw [h3, Complex.cpow_natCast]
    push_cast
    ring
  rw [hmel] at hM
  have hz : HasSum (fun i : ℕ => (((6 : ℝ) * (1 / ((i : ℝ) + 1) ^ 4) : ℝ) : ℂ))
      (((6 : ℝ) * (Real.pi ^ 4 / 90) : ℝ) : ℂ) := by
    apply Complex.hasSum_ofReal.mpr
    apply HasSum.mul_left
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_four
    simpa [Nat.cast_add, Nat.cast_one] using this
  have heq : (fun i : ℕ => Complex.Gamma 4 * (fun _ => (1 : ℂ)) i /
      (((fun i : ℕ => (i : ℝ) + 1) i : ℝ) : ℂ) ^ (4 : ℂ)) =
      (fun i : ℕ => (((6 : ℝ) * (1 / ((i : ℝ) + 1) ^ 4) : ℝ) : ℂ)) := by
    funext i
    have hG : Complex.Gamma 4 = 6 := by
      have := Complex.Gamma_nat_eq_factorial 3
      rw [show ((3 : ℕ) : ℂ) + 1 = 4 by norm_num] at this
      rw [this]; norm_num [Nat.factorial]
    have h4 : (4 : ℂ) = ((4 : ℕ) : ℂ) := by norm_num
    rw [hG, h4, Complex.cpow_natCast]
    push_cast
    ring
  rw [heq] at hM
  have := hM.unique hz
  have h' := Complex.ofReal_injective this
  rw [h']
  ring

theorem solution (T : ℝ) (hT : 0 < T) :
    (∫ nu in Set.Ioi (0 : ℝ), Real.pi * spectralRadianceFrequency T nu)
      = stefanBoltzmannConstant * T ^ 4 := by
  have hh : 0 < planckConstant := by unfold planckConstant; norm_num
  have hk : 0 < boltzmannConstant := by unfold boltzmannConstant; norm_num
  have hc : 0 < speedOfLight := by unfold speedOfLight; norm_num
  set b := planckConstant / (boltzmannConstant * T) with hb_def
  have hb : 0 < b := by positivity
  have hfun : (fun nu => Real.pi * spectralRadianceFrequency T nu) =
      fun nu => (Real.pi * 2 * planckConstant / (speedOfLight ^ 2 * b ^ 3)) *
        ((fun x : ℝ => x ^ 3 / (Real.exp x - 1)) (b * nu)) := by
    funext nu
    unfold spectralRadianceFrequency
    have : planckConstant * nu / (boltzmannConstant * T) = b * nu := by
      rw [hb_def]; ring
    rw [this]
    field_simp
  rw [hfun, integral_const_mul,
    integral_comp_mul_left_Ioi (fun x : ℝ => x ^ 3 / (Real.exp x - 1)) 0 hb, mul_zero,
    W7b_CODATA2022_bose_einstein_integral_cube]
  unfold stefanBoltzmannConstant reducedPlanckConstant
  rw [hb_def, smul_eq_mul]
  have hpi := Real.pi_pos
  field_simp
  ring
