-- Prove2me | solution 1 for BroughanRH.fareyL2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T01:43:50.302168+00:00
-- url     : https://prove2.me/submissions/73ff2e33-4926-44a1-aea0-4aec65285f3c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis
import Mathlib

open Finset Filter MeasureTheory Complex Real

namespace FareyAux

noncomputable def G (y : ℝ) : ℝ := Int.fract y - 1 / 2

lemma G_add_nat (y : ℝ) (j : ℕ) : G (y + j) = G y := by
  simp [G, Int.fract_add_natCast]

lemma measurable_G : Measurable G := (measurable_fract.sub measurable_const)

lemma abs_G_le (y : ℝ) : |G y| ≤ 1 := by
  unfold G
  have h0 := Int.fract_nonneg y
  have h1 := Int.fract_lt_one y
  rw [abs_le]; constructor <;> linarith

lemma intervalIntegrable_of_bdd {g : ℝ → ℂ} (hg : Measurable g) (M : ℝ) (hM : ∀ x, ‖g x‖ ≤ M)
    (a b : ℝ) : IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := M) ?_ hg.aestronglyMeasurable ?_
  · rw [Set.uIoc]; exact measure_Ioc_lt_top.ne
  · exact Filter.Eventually.of_forall hM

lemma fourier_eq (k : ℤ) (x : ℝ) :
    fourier (-k) (x : AddCircle ((1:ℝ) - 0)) = Complex.exp (2 * π * I * (-k : ℤ) * x) := by
  rw [fourier_coe_apply]; congr 1; push_cast; ring

/-- the `k`-th Fourier coefficient of `x ↦ G (m x)` on `[0,1]`. -/
lemma coef_G (m : ℕ) (hm : 1 ≤ m) (k : ℤ) :
    fourierCoeffOn zero_lt_one (fun x : ℝ => ((G (m * x) : ℝ) : ℂ)) k =
      if (m : ℤ) ∣ k then bernoulliFourierCoeff 1 (k / m) else 0 := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm0
  set φ : ℝ → ℂ := fun y => Complex.exp (2 * π * I * (-k : ℤ) * y / m) * (G y : ℂ) with hφ
  have hφm : Measurable φ := by
    apply Measurable.mul
    · exact (Complex.measurable_exp.comp (by fun_prop))
    · exact Complex.measurable_ofReal.comp measurable_G
  have hφb : ∀ y, ‖φ y‖ ≤ 1 := by
    intro y
    simp only [hφ, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have : ‖Complex.exp (2 * π * I * (-k : ℤ) * y / m)‖ = 1 := by
      rw [Complex.norm_exp]
      have : (2 * π * I * (-k : ℤ) * y / m).re = 0 := by
        simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
      rw [this, Real.exp_zero]
    rw [this, one_mul]; exact abs_G_le y
  have hint : ∀ a b : ℝ, IntervalIntegrable φ volume a b :=
    intervalIntegrable_of_bdd hφm 1 hφb
  -- step 1: rewrite as integral of φ (m x)
  have h1 : fourierCoeffOn zero_lt_one (fun x : ℝ => ((G (m * x) : ℝ) : ℂ)) k =
      (m : ℂ)⁻¹ * ∫ y in (0:ℝ)..m, φ y := by
    rw [fourierCoeffOn_eq_integral]
    have : (fun x : ℝ => fourier (-k) (x : AddCircle ((1:ℝ) - 0)) • ((G (m * x) : ℝ) : ℂ)) =
        fun x => φ (m * x) := by
      funext x
      rw [fourier_eq, smul_eq_mul, hφ]
      simp only
      congr 2
      push_cast
      field_simp
    rw [this, intervalIntegral.integral_comp_mul_left (fun y => φ y) hm0]
    simp only [sub_zero, div_one, one_smul, mul_zero, mul_one]
    rw [Complex.real_smul]; push_cast; ring
  -- step 2: split into unit intervals
  set ω : ℂ := Complex.exp (2 * π * I * (-k : ℤ) / m) with hω
  have h2 : ∫ y in (0:ℝ)..m, φ y = (∑ j ∈ range m, ω ^ j) * ∫ y in (0:ℝ)..1, φ y := by
    have := intervalIntegral.sum_integral_adjacent_intervals (f := φ) (μ := volume)
      (a := fun j : ℕ => (j : ℝ)) (n := m) (fun j _ => hint _ _)
    simp only [Nat.cast_zero] at this
    rw [← this, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    have e : ∫ y in (j:ℝ)..((j+1 : ℕ) : ℝ), φ y = ∫ y in (0:ℝ)..1, φ (y + j) := by
      rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm (1:ℝ)]; push_cast; rfl
    rw [e]
    have e2 : (fun y => φ (y + j)) = fun y => ω ^ j * φ y := by
      funext y
      simp only [hφ, hω, G_add_nat]
      rw [← Complex.exp_nat_mul, ← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast; ring
    rw [e2, intervalIntegral.integral_const_mul]
  -- step 3: the integral over [0,1] when m ∣ k
  have h3 : ∀ l : ℤ, k = m * l → ∫ y in (0:ℝ)..1, φ y = bernoulliFourierCoeff 1 l := by
    intro l hl
    rw [bernoulliFourierCoeff, fourierCoeffOn_eq_integral]
    simp only [sub_zero, div_one, one_smul]
    apply intervalIntegral.integral_congr_ae
    have hne : ∀ᵐ x : ℝ ∂volume, x ∉ ({1} : Set ℝ) :=
      measure_eq_zero_iff_ae_notMem.mp (measure_singleton 1)
    filter_upwards [hne] with x hx hxI
    rw [Set.uIoc_of_le zero_le_one] at hxI
    have hx1 : x < 1 := lt_of_le_of_ne hxI.2 (by simpa using hx)
    rw [fourier_eq, smul_eq_mul, hφ]
    simp only
    have hG : G x = bernoulliFun 1 x := by
      rw [bernoulliFun_one, G, Int.fract_eq_self.mpr ⟨hxI.1.le, hx1⟩]
    rw [hG]
    congr 2
    rw [hl]; push_cast; field_simp
  rw [h1, h2]
  split_ifs with hdvd
  · obtain ⟨l, hl⟩ := hdvd
    have hω1 : ω = 1 := by
      rw [hω, hl]
      have : 2 * π * I * ((-(m * l : ℤ) : ℤ) : ℂ) / m = ((-l : ℤ) : ℂ) * (2 * π * I) := by
        push_cast; field_simp
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [hω1, h3 l hl]
    have : (m : ℤ) * l / m = l := by
      rw [Int.mul_ediv_cancel_left]; exact_mod_cast (by omega : m ≠ 0)
    rw [show k / (m:ℤ) = l by rw [hl, this]]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    field_simp
  · have hω1 : ω ≠ 1 := by
      intro h
      rw [hω, Complex.exp_eq_one_iff] at h
      obtain ⟨n, hn⟩ := h
      apply hdvd
      refine ⟨-n, ?_⟩
      have h2pi : (2 * π * I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      rw [div_eq_iff hmC] at hn
      have h5 : (2 * π * I) * ((-k : ℤ) : ℂ) = (2 * π * I) * ((n * m : ℤ) : ℂ) := by
        push_cast at hn ⊢; linear_combination hn
      have h6 := mul_left_cancel₀ h2pi h5
      have h7 : -k = n * m := by exact_mod_cast h6
      linarith
    have hωm : ω ^ m = 1 := by
      rw [hω, ← Complex.exp_nat_mul]
      have : (m : ℂ) * (2 * π * I * ((-k : ℤ) : ℂ) / m) = ((-k : ℤ) : ℂ) * (2 * π * I) := by
        field_simp
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [geom_sum_eq hω1, hωm]
    simp

end FareyAux



namespace FareyAux

def FF (N : ℕ) : Finset ℚ := (Finset.Icc 1 N).biUnion fun q =>
  ((Finset.Icc 1 q).filter fun a => Nat.Coprime a q).image fun a : ℕ => (a : ℚ) / q

lemma den_eq (a q : ℕ) (hq : 0 < q) (h : Nat.Coprime a q) : ((a : ℚ) / q).den = q := by
  have := Rat.den_div_eq_of_coprime (a := (a : ℤ)) (b := (q : ℤ)) (by exact_mod_cast hq)
    (by simpa using h)
  push_cast at this
  exact_mod_cast this

lemma mem_FF {N : ℕ} {u : ℚ} :
    u ∈ FF N ↔ ∃ q ∈ Icc 1 N, ∃ a ∈ Icc 1 q, Nat.Coprime a q ∧ (a : ℚ) / q = u := by
  simp only [FF, mem_biUnion, mem_image, mem_filter]
  constructor
  · rintro ⟨q, hq, a, ⟨ha, hc⟩, rfl⟩; exact ⟨q, hq, a, ha, hc, rfl⟩
  · rintro ⟨q, hq, a, ha, hc, rfl⟩; exact ⟨q, hq, a, ⟨ha, hc⟩, rfl⟩

lemma sum_FF {N : ℕ} {β : Type*} [AddCommMonoid β] (g : ℚ → β) :
    ∑ u ∈ FF N, g u = ∑ q ∈ Icc 1 N, ∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
      g ((a : ℚ) / q) := by
  rw [FF, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro q hq
    have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
    rw [Finset.sum_image]
    intro a _ b _ hab
    have hq' : (q : ℚ) ≠ 0 := by positivity
    simp only at hab
    rw [div_left_inj' hq'] at hab
    exact_mod_cast hab
  · intro q hq q' hq' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro u hu hu'
    simp only [mem_image, mem_filter] at hu hu'
    obtain ⟨a, ⟨_, ha⟩, rfl⟩ := hu
    obtain ⟨b, ⟨_, hb⟩, hab⟩ := hu'
    have h1 := den_eq a q (Finset.mem_Icc.mp (Finset.mem_coe.mp hq)).1 ha
    have h2 := den_eq b q' (Finset.mem_Icc.mp (Finset.mem_coe.mp hq')).1 hb
    rw [hab] at h2
    exact (hne (h1.symm.trans h2)).elim

lemma FF_bounds {N : ℕ} {u : ℚ} (hu : u ∈ FF N) :
    1 / (N : ℝ) ≤ (u : ℝ) ∧ (u : ℝ) ≤ 1 := by
  obtain ⟨q, hq, a, ha, _, rfl⟩ := mem_FF.mp hu
  rw [Finset.mem_Icc] at hq ha
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.1
  push_cast
  constructor
  · rw [div_le_div_iff₀ (by exact_mod_cast (lt_of_lt_of_le hq.1 hq.2)) hq0]
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha.1
    have : (q : ℝ) ≤ N := by exact_mod_cast hq.2
    nlinarith
  · rw [div_le_one hq0]; exact_mod_cast ha.2

lemma one_mem_FF {N : ℕ} (hN : 1 ≤ N) : (1 : ℚ) ∈ FF N := by
  rw [mem_FF]; exact ⟨1, by simp [hN], 1, by simp, by simp, by simp⟩

lemma FF_spacing {N : ℕ} {u v : ℚ} (hu : u ∈ FF N) (hv : v ∈ FF N) (hne : u ≠ v) :
    1 / (N : ℝ) ^ 2 ≤ |(u : ℝ) - v| := by
  obtain ⟨q, hq, a, ha, _, rfl⟩ := mem_FF.mp hu
  obtain ⟨p, hp, b, hb, _, rfl⟩ := mem_FF.mp hv
  rw [Finset.mem_Icc] at hq hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.1
  have hz : ((a : ℤ) * p - b * q) ≠ 0 := by
    intro h
    apply hne
    have : (a : ℚ) * p = b * q := by exact_mod_cast (sub_eq_zero.mp h)
    have hq' : (q : ℚ) ≠ 0 := by have := hq.1; positivity
    have hp' : (p : ℚ) ≠ 0 := by have := hp.1; positivity
    rw [div_eq_div_iff hq' hp']; exact this
  have h1 : (1 : ℝ) ≤ |((a : ℤ) * p - b * q : ℤ)| := by
    exact_mod_cast Int.one_le_abs hz
  push_cast at h1 ⊢
  have e : (a : ℝ) / q - b / p = (a * p - b * q) / (q * p) := by field_simp
  rw [e, abs_div, abs_of_pos (by positivity : (0:ℝ) < q * p)]
  have hqN : (q : ℝ) ≤ N := by exact_mod_cast hq.2
  have hpN : (p : ℝ) ≤ N := by exact_mod_cast hp.2
  have hqp : (q : ℝ) * p ≤ N ^ 2 := by nlinarith
  calc 1 / (N : ℝ) ^ 2 ≤ 1 / (q * p) := one_div_le_one_div_of_le (by positivity) hqp
    _ ≤ _ := div_le_div_of_nonneg_right h1 (by positivity)

/-- counting function on `[0,1]` -/
lemma count_FF {N : ℕ} (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∑ u ∈ FF N, (if (u : ℝ) ≤ x then (1 : ℝ) else 0) =
      ∑ q ∈ Icc 1 N, (((Icc 1 ⌊(q : ℝ) * x⌋₊).filter fun a => Nat.Coprime a q).card : ℝ) := by
  rw [sum_FF]
  apply Finset.sum_congr rfl
  intro q hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.filter_filter]
  congr 2
  ext a
  simp only [mem_filter, mem_Icc]
  have hfl : ⌊(q : ℝ) * x⌋₊ ≤ q := by
    apply Nat.floor_le_of_le; nlinarith
  constructor
  · rintro ⟨⟨h1, _⟩, hc, hle⟩
    push_cast at hle
    rw [div_le_iff₀ hq0] at hle
    refine ⟨⟨h1, Nat.le_floor (by linarith)⟩, hc⟩
  · rintro ⟨⟨h1, h2⟩, hc⟩
    refine ⟨⟨h1, h2.trans hfl⟩, hc, ?_⟩
    push_cast
    rw [div_le_iff₀ hq0]
    have := (Nat.le_floor_iff (by positivity)).mp h2
    linarith

lemma sum_divisors_moebius (q : ℕ) :
    ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℤ) = if q = 1 then 1 else 0 := by
  have := congrArg (fun f : ArithmeticFunction ℤ => f q) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at this
  exact this

/-- coprime count via Möbius -/
lemma coprime_count (q K : ℕ) (hq : 0 < q) :
    (((Icc 1 K).filter fun a => Nat.Coprime a q).card : ℤ) =
      ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℤ) * (K / d : ℕ) := by
  rw [Finset.card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have h1 : ∀ a ∈ Icc 1 K, (if Nat.Coprime a q then (1 : ℤ) else 0) =
      ∑ d ∈ q.divisors.filter (fun d => d ∣ a), (ArithmeticFunction.moebius d : ℤ) := by
    intro a ha
    have hg : q.divisors.filter (fun d => d ∣ a) = (Nat.gcd a q).divisors := by
      ext d
      simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      have : Nat.gcd a q ≠ 0 := Nat.gcd_ne_zero_right hq.ne'
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨⟨h2, h1⟩, this⟩
      · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨⟨h2, hq.ne'⟩, h1⟩
    rw [hg, sum_divisors_moebius]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm' (t' := q.divisors)
    (s' := fun d => (Icc 1 K).filter (fun a => d ∣ a))]
  · apply Finset.sum_congr rfl
    intro d _
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    congr 1
    have : Icc 1 K = Ioc 0 K := rfl
    rw [this, Nat.Ioc_filter_dvd_card_eq_div]
  · intro a d
    simp only [mem_filter]
    tauto

/-- rearrangement of the Dirichlet hyperbola sum -/
lemma rearrange (N : ℕ) (h : ℕ → ℝ) :
    ∑ q ∈ Icc 1 N, ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * h (q / d) =
      ∑ m ∈ Icc 1 N, (∑ d ∈ Icc 1 (N / m), (ArithmeticFunction.moebius d : ℝ)) * h m := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun p _ => (⟨p.1 / p.2, p.2⟩ : (_ : ℕ) × ℕ)) (fun p _ => ⟨p.1 * p.2, p.2⟩)
    ?hi ?hj ?li ?ri ?hh
  case hi =>
    intro p hp
    rw [mem_sigma, mem_Icc, Nat.mem_divisors] at hp
    rw [mem_sigma, mem_Icc, mem_Icc]
    obtain ⟨⟨hq1, hqN⟩, hdq, -⟩ := hp
    obtain ⟨k, hk⟩ := hdq
    have hd : 0 < p.2 := Nat.pos_of_ne_zero (by intro h; rw [h] at hk; omega)
    have hk0 : 0 < k := Nat.pos_of_ne_zero (by intro h; rw [h] at hk; omega)
    show (1 ≤ p.1 / p.2 ∧ p.1 / p.2 ≤ N) ∧ 1 ≤ p.2 ∧ p.2 ≤ N / (p.1 / p.2)
    rw [hk, Nat.mul_div_cancel_left _ hd]
    refine ⟨⟨hk0, ?_⟩, hd, ?_⟩
    · nlinarith
    · rw [Nat.le_div_iff_mul_le hk0]; nlinarith
  case hj =>
    intro p hp
    rw [mem_sigma, mem_Icc, mem_Icc] at hp
    rw [mem_sigma, mem_Icc, Nat.mem_divisors]
    obtain ⟨⟨hm1, _⟩, hd1, hdN⟩ := hp
    have := (Nat.le_div_iff_mul_le hm1).mp hdN
    show (1 ≤ p.1 * p.2 ∧ p.1 * p.2 ≤ N) ∧ p.2 ∣ p.1 * p.2 ∧ p.1 * p.2 ≠ 0
    refine ⟨⟨by nlinarith, by nlinarith⟩, Dvd.intro_left _ rfl, by positivity⟩
  case li =>
    intro p hp
    rw [mem_sigma, Nat.mem_divisors] at hp
    show (⟨p.1 / p.2 * p.2, p.2⟩ : (_ : ℕ) × ℕ) = p
    rw [Nat.div_mul_cancel hp.2.1]
  case ri =>
    intro p hp
    rw [mem_sigma, mem_Icc, mem_Icc] at hp
    show (⟨p.1 * p.2 / p.2, p.2⟩ : (_ : ℕ) × ℕ) = p
    rw [Nat.mul_div_cancel _ (by omega : 0 < p.2)]
  case hh =>
    intro p hp
    rfl

/-- `c N m = M(N/m)` -/
noncomputable def cc (N m : ℕ) : ℝ := ∑ d ∈ Icc 1 (N / m), (ArithmeticFunction.moebius d : ℝ)

lemma count_formula {N : ℕ} (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∑ u ∈ FF N, (if (u : ℝ) ≤ x then (1 : ℝ) else 0) =
      ∑ m ∈ Icc 1 N, cc N m * (⌊(m : ℝ) * x⌋₊ : ℝ) := by
  rw [count_FF x hx0 hx1]
  unfold cc
  rw [← rearrange N (fun m => (⌊(m : ℝ) * x⌋₊ : ℝ))]
  apply Finset.sum_congr rfl
  intro q hq
  have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
  have := congrArg (fun z : ℤ => (z : ℝ)) (coprime_count q ⌊(q : ℝ) * x⌋₊ hq0)
  simp only [Int.cast_natCast, Int.cast_sum, Int.cast_mul] at this
  rw [this]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  rw [← Nat.floor_div_natCast]
  congr 2
  rw [Nat.cast_div hdq (by exact_mod_cast hd0.ne')]
  ring

lemma card_formula {N : ℕ} :
    ((FF N).card : ℝ) = ∑ m ∈ Icc 1 N, cc N m * m := by
  have := count_formula (N := N) 1 zero_le_one le_rfl
  have h1 : ∑ u ∈ FF N, (if (u : ℝ) ≤ 1 then (1 : ℝ) else 0) = (FF N).card := by
    rw [Finset.card_eq_sum_ones]; push_cast
    apply Finset.sum_congr rfl; intro u hu; simp [(FF_bounds hu).2]
  rw [← h1, this]
  apply Finset.sum_congr rfl; intro m _; simp

lemma sum_cc {N : ℕ} (hN : 1 ≤ N) : ∑ m ∈ Icc 1 N, cc N m = 1 := by
  have := rearrange N (fun _ => 1)
  unfold cc
  simp only [mul_one] at this
  rw [← this]
  have h2 : ∀ q ∈ Icc 1 N, ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) =
      if q = 1 then 1 else 0 := by
    intro q _
    have := sum_divisors_moebius q
    have h' : ((∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℤ) : ℤ) : ℝ) =
      ((if q = 1 then 1 else 0 : ℤ) : ℝ) := by rw [this]
    push_cast at h'
    rw [h']
  rw [Finset.sum_congr rfl h2, Finset.sum_ite_eq']
  simp [hN]

/-- `|F_N| ≤ N^2` -/
lemma card_FF_le (N : ℕ) : ((FF N).card : ℝ) ≤ (N : ℝ) ^ 2 := by
  have h1 : (FF N).card ≤ ∑ q ∈ Finset.Icc 1 N, (((Finset.Icc 1 q).filter fun a => Nat.Coprime a q).image fun a : ℕ => (a : ℚ) / q).card :=
    Finset.card_biUnion_le
  have h3 : ∀ q ∈ Finset.Icc 1 N, (((Finset.Icc 1 q).filter fun a => Nat.Coprime a q).image fun a : ℕ => (a : ℚ) / q).card ≤ N := by
    intro q hq
    refine (Finset.card_image_le).trans ((Finset.card_filter_le _ _).trans ?_)
    simp only [Nat.card_Icc, add_tsub_cancel_right]
    exact (Finset.mem_Icc.mp hq).2
  have h4 := (h1.trans (Finset.sum_le_sum h3))
  simp only [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, smul_eq_mul] at h4
  have : ((FF N).card : ℝ) ≤ ((N * N : ℕ) : ℝ) := by exact_mod_cast h4
  simpa [sq] using this

lemma inv_sq_sum (N : ℕ) (hN : 2 ≤ N) :
    ∑ d ∈ Icc 2 N, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 3 / 4 - 1 / N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / n - 1 / (n + 1 : ℕ) := by
      push_cast
      rw [div_sub_div _ _ hn0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    push_cast at this ⊢
    linarith

/-- `|F_N| ≥ N^2/8` -/
lemma card_FF_ge (N : ℕ) (hN : 1 ≤ N) : (N : ℝ) ^ 2 / 8 ≤ ((FF N).card : ℝ) := by
  set S := Icc 1 N ×ˢ Icc 1 N with hS
  set P := S.filter (fun p => Nat.Coprime p.1 p.2) with hP
  set Q := S.filter (fun p => ¬ Nat.Coprime p.1 p.2) with hQ
  have hPQ : (P.card : ℝ) + Q.card = (N : ℝ) ^ 2 := by
    have := Finset.card_filter_add_card_filter_not (s := S) (fun p => Nat.Coprime p.1 p.2)
    rw [hS, Finset.card_product] at this
    simp only [Nat.card_Icc, add_tsub_cancel_right] at this
    rw [hP, hQ, hS]; rw [sq]; exact_mod_cast this
  -- bound Q
  have hQsub : Q ⊆ (Icc 2 N).biUnion fun d =>
      (Icc 1 N).filter (fun a => d ∣ a) ×ˢ (Icc 1 N).filter (fun a => d ∣ a) := by
    intro p hp
    simp only [hQ, hS, mem_filter, mem_product, mem_Icc] at hp
    simp only [mem_biUnion, mem_product, mem_filter, mem_Icc]
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, hc⟩ := hp
    refine ⟨Nat.gcd p.1 p.2, ⟨?_, ?_⟩, ⟨⟨h1, h2⟩, Nat.gcd_dvd_left _ _⟩, ⟨h3, h4⟩, Nat.gcd_dvd_right _ _⟩
    · have : Nat.gcd p.1 p.2 ≠ 1 := hc
      have : Nat.gcd p.1 p.2 ≠ 0 := Nat.gcd_ne_zero_left (by omega)
      omega
    · exact (Nat.gcd_le_left _ (by omega)).trans h2
  have hQle : (Q.card : ℝ) ≤ ∑ d ∈ Icc 2 N, ((N / d : ℕ) : ℝ) ^ 2 := by
    have := (Finset.card_le_card hQsub).trans Finset.card_biUnion_le
    have e : ∀ d ∈ Icc 2 N, ((Icc 1 N).filter (fun a => d ∣ a) ×ˢ
        (Icc 1 N).filter (fun a => d ∣ a)).card = (N / d) * (N / d) := by
      intro d _
      rw [Finset.card_product]
      have : Icc 1 N = Ioc 0 N := rfl
      rw [this, Nat.Ioc_filter_dvd_card_eq_div]
    rw [Finset.sum_congr rfl e] at this
    have : (Q.card : ℝ) ≤ ((∑ d ∈ Icc 2 N, (N / d) * (N / d) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this
    simpa [sq] using this
  have hQle2 : (Q.card : ℝ) ≤ 3 / 4 * (N : ℝ) ^ 2 := by
    refine hQle.trans ?_
    rcases (show N = 1 ∨ 2 ≤ N by omega) with h | h
    · subst h; simp; norm_num
    have h1 : ∀ d ∈ Icc 2 N, ((N / d : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 * (1 / (d : ℝ) ^ 2) := by
      intro d hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (by simp at hd; omega : 0 < d)
      have : ((N / d : ℕ) : ℝ) ≤ N / d := Nat.cast_div_le
      have h0 : (0 : ℝ) ≤ ((N / d : ℕ) : ℝ) := by positivity
      calc ((N / d : ℕ) : ℝ) ^ 2 ≤ ((N : ℝ) / d) ^ 2 := pow_le_pow_left₀ h0 this 2
        _ = _ := by field_simp
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.mul_sum]
    have := inv_sq_sum N h
    have : (0 : ℝ) ≤ 1 / N := by positivity
    nlinarith [sq_nonneg (N : ℝ)]
  -- P ≤ 2 |F_N|
  set P1 := P.filter (fun p => p.1 ≤ p.2) with hP1
  have hP1card : (P1.card : ℝ) = (FF N).card := by
    have e1 : (FF N).card = ∑ q ∈ Icc 1 N, ((Icc 1 q).filter fun a => Nat.Coprime a q).card := by
      rw [Finset.card_eq_sum_ones, sum_FF]; simp
    rw [e1]
    have e2 : P1.card = ((Icc 1 N).sigma fun q => (Icc 1 q).filter fun a => Nat.Coprime a q).card := by
      refine Finset.card_nbij' (fun p => (⟨p.2, p.1⟩ : (_ : ℕ) × ℕ)) (fun s => (s.2, s.1)) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_coe, hP1, hP, hS, mem_filter, mem_product, mem_Icc] at hp
        simp only [Finset.mem_coe, mem_sigma, mem_filter, mem_Icc]
        exact ⟨hp.1.1.2, ⟨hp.1.1.1.1, hp.2⟩, hp.1.2⟩
      · intro s hs
        simp only [Finset.mem_coe, mem_sigma, mem_filter, mem_Icc] at hs
        simp only [Finset.mem_coe, hP1, hP, hS, mem_filter, mem_product, mem_Icc]
        exact ⟨⟨⟨⟨hs.2.1.1, hs.2.1.2.trans hs.1.2⟩, hs.1⟩, hs.2.2⟩, hs.2.1.2⟩
      · intro p _; rfl
      · intro s _; rfl
    rw [e2, Finset.card_sigma]
  have hPle : (P.card : ℝ) ≤ 2 * P1.card := by
    have hsub : P ⊆ P1 ∪ P1.image (fun p => (p.2, p.1)) := by
      intro p hp
      rcases le_total p.1 p.2 with h | h
      · exact Finset.mem_union_left _ (by rw [hP1, mem_filter]; exact ⟨hp, h⟩)
      · apply Finset.mem_union_right
        rw [mem_image]
        refine ⟨(p.2, p.1), ?_, rfl⟩
        simp only [hP1, hP, hS, mem_filter, mem_product] at hp ⊢
        exact ⟨⟨⟨hp.1.2, hp.1.1⟩, Nat.Coprime.symm hp.2⟩, h⟩
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have h2 := (Finset.card_image_le (s := P1) (f := fun p : ℕ × ℕ => (p.2, p.1)))
    have : (P.card : ℝ) ≤ P1.card + P1.card := by exact_mod_cast this.trans (by omega)
    linarith
  nlinarith

end FareyAux



namespace FareyAux

/-- multiples of `L` -/
noncomputable def gL (L : ℕ) (k : ℤ) : ℝ := if (L : ℤ) ∣ k then 1 / (k : ℝ) ^ 2 else 0

lemma gL_nonneg (L : ℕ) (k : ℤ) : 0 ≤ gL L k := by
  unfold gL; split_ifs <;> positivity

lemma summable_inv_sq_int : Summable (fun k : ℤ => 1 / (k : ℝ) ^ 2) :=
  summable_one_div_int_pow.mpr (by norm_num)

lemma tsum_inv_sq_int_le : ∑' k : ℤ, 1 / (k : ℝ) ^ 2 ≤ 4 := by
  have hz := hasSum_zeta_two
  have h1' : HasSum (fun n : ℕ => 1 / ((n : ℤ) : ℝ) ^ 2) (π ^ 2 / 6) := by
    simp only [Int.cast_natCast]; exact hz
  have hz2 : HasSum (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) (π ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hz
    simpa using this
  have h2' : HasSum (fun n : ℕ => 1 / ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 2) (π ^ 2 / 6) := by
    refine hz2.congr_fun ?_
    intro n; push_cast; ring
  have e := tsum_of_nat_of_neg_add_one (f := fun k : ℤ => 1 / (k : ℝ) ^ 2) h1'.summable h2'.summable
  rw [e, h1'.tsum_eq, h2'.tsum_eq]
  have hpi : π < 63 / 20 := by have := Real.pi_lt_d2; norm_num at this ⊢; linarith
  have h3 : π * π < (63 / 20) * (63 / 20) := mul_self_lt_mul_self Real.pi_pos.le hpi
  rw [sq]; linarith

lemma summable_gL (L : ℕ) : Summable (gL L) := by
  refine Summable.of_nonneg_of_le (gL_nonneg L) (fun k => ?_) summable_inv_sq_int
  unfold gL; split_ifs
  · exact le_rfl
  · positivity

lemma tsum_gL_le (L : ℕ) (hL : 1 ≤ L) : ∑' k, gL L k ≤ 4 / (L : ℝ) ^ 2 := by
  have hL0 : (L : ℝ) ≠ 0 := by positivity
  have hinj : Function.Injective (fun t : ℤ => (L : ℤ) * t) := by
    intro a b h; simp only at h
    exact Int.eq_of_mul_eq_mul_left (by exact_mod_cast (by omega : L ≠ 0)) h
  have hsupp : Function.support (gL L) ⊆ Set.range (fun t : ℤ => (L : ℤ) * t) := by
    intro k hk
    simp only [Function.mem_support, gL] at hk
    split_ifs at hk with h
    · obtain ⟨t, rfl⟩ := h; exact ⟨t, rfl⟩
    · exact absurd rfl hk
  rw [← hinj.tsum_eq hsupp]
  have e : (fun t : ℤ => gL L ((L : ℤ) * t)) = fun t : ℤ => (1 / (L : ℝ) ^ 2) * (1 / (t : ℝ) ^ 2) := by
    funext t
    simp only [gL, dvd_mul_right, if_true]
    push_cast; field_simp
  rw [e, tsum_mul_left]
  have := tsum_inv_sq_int_le
  rw [div_eq_mul_one_div 4]
  rw [mul_comm 4]
  exact mul_le_mul_of_nonneg_left this (by positivity)

noncomputable def bb (m : ℕ) (k : ℤ) : ℝ := if (m : ℤ) ∣ k then (m : ℝ) / |(k : ℝ)| else 0

lemma bb_nonneg (m : ℕ) (k : ℤ) : 0 ≤ bb m k := by unfold bb; split_ifs <;> positivity

lemma norm_coef_G_le (m : ℕ) (hm : 1 ≤ m) (k : ℤ) :
    ‖fourierCoeffOn zero_lt_one (fun x : ℝ => ((G (m * x) : ℝ) : ℂ)) k‖ ≤ bb m k := by
  rw [coef_G m hm k, bb]
  split_ifs with h
  · obtain ⟨l, rfl⟩ := h
    have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    rw [Int.mul_ediv_cancel_left _ hm0, bernoulliFourierCoeff_eq one_ne_zero]
    simp only [Nat.factorial_one, Nat.cast_one, pow_one]
    rcases eq_or_ne l 0 with rfl | hl
    · simp
    have hl' : (1 : ℝ) ≤ |(l : ℝ)| := by exact_mod_cast Int.one_le_abs hl
    rw [norm_div, norm_neg, norm_one]
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one, Complex.norm_intCast]
    push_cast
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < m)]
    rw [abs_of_pos Real.pi_pos]
    have hpi := Real.pi_gt_three
    have hm' : (0 : ℝ) < m := by positivity
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 < (m:ℝ) * |(l:ℝ)| := by positivity
    nlinarith
  · simp

lemma bb_mul_le (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (k : ℤ) :
    bb m k * bb n k ≤ (m : ℝ) * n * gL (Nat.lcm m n) k := by
  unfold bb gL
  by_cases hmk : (m : ℤ) ∣ k
  · by_cases hnk : (n : ℤ) ∣ k
    · have : ((Nat.lcm m n : ℕ) : ℤ) ∣ k := by
        rw [Int.natCast_dvd] at hmk hnk ⊢
        exact Nat.lcm_dvd hmk hnk
      rw [if_pos hmk, if_pos hnk, if_pos this]
      rw [div_mul_div_comm, ← sq, sq_abs]; ring_nf; exact le_rfl
    · rw [if_neg hnk, mul_zero]
      split_ifs <;> positivity
  · rw [if_neg hmk, zero_mul]
    split_ifs <;> positivity

lemma norm_exp_re_zero (z : ℂ) (hz : z.re = 0) : ‖Complex.exp z‖ = 1 := by
  rw [Complex.norm_exp, hz, Real.exp_zero]

lemma coef_sum (N : ℕ) (c : ℕ → ℝ) (k : ℤ) :
    fourierCoeffOn zero_lt_one
        (fun x : ℝ => (((∑ m ∈ Icc 1 N, c m * G (m * x)) : ℝ) : ℂ)) k =
      ∑ m ∈ Icc 1 N, (c m : ℂ) *
        fourierCoeffOn zero_lt_one (fun x : ℝ => ((G (m * x) : ℝ) : ℂ)) k := by
  simp_rw [fourierCoeffOn_eq_integral, fourier_eq]
  simp only [sub_zero, div_one, one_smul, smul_eq_mul]
  push_cast
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro m _
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext x; ring
  · intro m _
    apply intervalIntegrable_of_bdd (M := |c m|)
    · exact (Complex.measurable_exp.comp (by fun_prop)).mul (measurable_const.mul
          (Complex.measurable_ofReal.comp (measurable_G.comp (by fun_prop))))
    · intro x
      rw [norm_mul, norm_mul, norm_exp_re_zero _ (by simp [Complex.mul_re, Complex.mul_im]),
        one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      have := abs_G_le (m * x)
      calc |c m| * |G (↑m * x)| ≤ |c m| * 1 := mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ = |c m| := mul_one _

lemma parseval_bound (N : ℕ) (c : ℕ → ℝ) :
    ∫ x in (0:ℝ)..1, (∑ m ∈ Icc 1 N, c m * G (m * x)) ^ 2 ≤
      4 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |c m| * |c n| * ((Nat.gcd m n : ℝ) ^ 2 / (m * n)) := by
  set f : ℝ → ℝ := fun x => ∑ m ∈ Icc 1 N, c m * G (m * x) with hf
  have hfm : Measurable f := by
    apply Finset.measurable_sum; intro m _
    exact measurable_const.mul (measurable_G.comp (by fun_prop))
  have hfb : ∀ x, |f x| ≤ ∑ m ∈ Icc 1 N, |c m| := by
    intro x
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [abs_mul]
    calc |c m| * |G (↑m * x)| ≤ |c m| * 1 := mul_le_mul_of_nonneg_left (abs_G_le _) (abs_nonneg _)
      _ = |c m| := mul_one _
  have : IsFiniteMeasure (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    ⟨by simp⟩
  have hL2 : MemLp (fun x => ((f x : ℝ) : ℂ)) 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    refine MemLp.of_bound (Complex.measurable_ofReal.comp hfm).aestronglyMeasurable
      (∑ m ∈ Icc 1 N, |c m|) (Filter.Eventually.of_forall fun x => ?_)
    simp only [Function.comp, Complex.norm_real, Real.norm_eq_abs]
    exact hfb x
  have hP := hasSum_sq_fourierCoeffOn zero_lt_one hL2
  have hint : ((1:ℝ) - 0)⁻¹ • ∫ x in (0:ℝ)..1, ‖((f x : ℝ) : ℂ)‖ ^ 2 =
      ∫ x in (0:ℝ)..1, (f x) ^ 2 := by
    simp [Complex.norm_real, sq_abs]
  rw [hint] at hP
  rw [← hP.tsum_eq]
  -- termwise bound
  set a : ℕ → ℝ := fun m => |c m|
  have hterm : ∀ k : ℤ, ‖fourierCoeffOn zero_lt_one (fun x => ((f x : ℝ) : ℂ)) k‖ ^ 2 ≤
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, a m * a n * ((m : ℝ) * n * gL (Nat.lcm m n) k) := by
    intro k
    rw [hf, coef_sum]
    have h1 : ‖∑ m ∈ Icc 1 N, (c m : ℂ) *
        fourierCoeffOn zero_lt_one (fun x : ℝ => ((G (m * x) : ℝ) : ℂ)) k‖ ≤
        ∑ m ∈ Icc 1 N, a m * bb m k := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_coef_G_le m (Finset.mem_Icc.mp hm).1 k) (abs_nonneg _)
    have h2 : (∑ m ∈ Icc 1 N, a m * bb m k) ^ 2 =
        ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, a m * a n * (bb m k * bb n k) := by
      rw [sq, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro m _; apply Finset.sum_congr rfl; intro n _; ring
    calc _ ≤ (∑ m ∈ Icc 1 N, a m * bb m k) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = _ := h2
      _ ≤ _ := by
        apply Finset.sum_le_sum; intro m hm; apply Finset.sum_le_sum; intro n hn
        apply mul_le_mul_of_nonneg_left
          (bb_mul_le m n (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hn).1 k)
        positivity
  have hsum : Summable (fun k : ℤ =>
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, a m * a n * ((m : ℝ) * n * gL (Nat.lcm m n) k)) := by
    apply summable_sum; intro m _; apply summable_sum; intro n _
    exact ((summable_gL _).mul_left _).mul_left _
  refine (hP.summable.tsum_le_tsum hterm hsum).trans ?_
  rw [Summable.tsum_finsetSum (fun m _ => summable_sum fun n _ =>
    ((summable_gL _).mul_left _).mul_left _)]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro m hm
  rw [Summable.tsum_finsetSum (fun n _ => ((summable_gL _).mul_left _).mul_left _)]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro n hn
  have hm1 := (Finset.mem_Icc.mp hm).1
  have hn1 := (Finset.mem_Icc.mp hn).1
  rw [tsum_mul_left, tsum_mul_left]
  have hL : 1 ≤ Nat.lcm m n := Nat.one_le_iff_ne_zero.mpr (Nat.lcm_ne_zero (by omega) (by omega))
  have ht := tsum_gL_le _ hL
  have hgl : ((Nat.gcd m n : ℕ) : ℝ) * (Nat.lcm m n : ℕ) = m * n := by
    exact_mod_cast Nat.gcd_mul_lcm m n
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hL0 : (0 : ℝ) < (Nat.lcm m n : ℕ) := by exact_mod_cast hL
  have e : (m : ℝ) * n * (4 / ((Nat.lcm m n : ℕ) : ℝ) ^ 2) = 4 * ((Nat.gcd m n : ℝ) ^ 2 / (m * n)) := by
    rw [← hgl]; field_simp
  have hpos : 0 ≤ a m * a n := by positivity
  calc a m * a n * ((m : ℝ) * n * ∑' k, gL (Nat.lcm m n) k)
      ≤ a m * a n * ((m : ℝ) * n * (4 / ((Nat.lcm m n : ℕ) : ℝ) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hpos
        exact mul_le_mul_of_nonneg_left ht (by positivity)
    _ = 4 * (|c m| * |c n| * ((Nat.gcd m n : ℝ) ^ 2 / (m * n))) := by rw [e]; ring

end FareyAux



namespace FareyAux

lemma mertens_bound (θ : ℝ) (hθ : 1 / 2 < θ)
    (hM : ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO atTop
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε))) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      |∑ k ∈ Icc 0 ⌊t⌋₊, (ArithmeticFunction.moebius k : ℝ)| ≤ C * t ^ θ := by
  obtain ⟨C, hC⟩ := (hM (θ - 1/2) (by linarith)).bound
  rw [eventually_atTop] at hC
  obtain ⟨N0, hN0⟩ := hC
  refine ⟨max C 0 + N0 + 1, by positivity, fun t ht => ?_⟩
  set N := ⌊t⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.one_le_floor_iff _ |>.mpr ht
  have hNt : (N : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hsum : ∑ k ∈ Icc 0 N, (ArithmeticFunction.moebius k : ℝ) =
      ∑ k ∈ Icc 1 N, (ArithmeticFunction.moebius k : ℝ) := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, ← Finset.Icc_add_one_left_eq_Ioc]
    simp
  have hpowN : (N : ℝ) ^ θ ≤ t ^ θ := Real.rpow_le_rpow hNpos.le hNt (by linarith)
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ θ := Real.one_le_rpow (by exact_mod_cast hN1) (by linarith)
  rw [hsum]
  rcases le_or_gt N0 N with h | h
  · have hb := hN0 N h
    have e : ‖∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ)‖ =
        |∑ k ∈ Icc 1 N, (ArithmeticFunction.moebius k : ℝ)| := by
      have : (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ)) =
          ((∑ k ∈ Icc 1 N, (ArithmeticFunction.moebius k : ℝ) : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.norm_real, Real.norm_eq_abs]
    have eθ : (1:ℝ)/2 + (θ - 1/2) = θ := by ring
    rw [e, eθ, Real.norm_of_nonneg (by positivity)] at hb
    calc _ ≤ C * (N : ℝ) ^ θ := hb
      _ ≤ max C 0 * (N : ℝ) ^ θ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ (max C 0 + N0 + 1) * t ^ θ := by
        apply mul_le_mul (by linarith) hpowN (by positivity) (by positivity)
  · have hb : |∑ k ∈ Icc 1 N, (ArithmeticFunction.moebius k : ℝ)| ≤ N := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k ∈ Icc 1 N, |(ArithmeticFunction.moebius k : ℝ)| ≤ ∑ k ∈ Icc 1 N, (1 : ℝ) := by
            apply Finset.sum_le_sum; intro k _
            have := ArithmeticFunction.abs_moebius_le_one (n := k)
            exact_mod_cast this
        _ = N := by simp
    have : (N : ℝ) ≤ N0 := by exact_mod_cast h.le
    calc _ ≤ (N0 : ℝ) := hb.trans this
      _ ≤ (max C 0 + N0 + 1) * 1 := by nlinarith [le_max_right C 0]
      _ ≤ (max C 0 + N0 + 1) * t ^ θ := by
        apply mul_le_mul_of_nonneg_left (h1.trans hpowN) (by positivity)



lemma cc_bound (θ : ℝ) (hθ : 1 / 2 < θ)
    (hM : ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO atTop
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε))) :
    ∃ C : ℝ, 0 < C ∧ ∀ N m : ℕ, 1 ≤ m → m ≤ N →
      |∑ d ∈ Icc 1 (N / m), (ArithmeticFunction.moebius d : ℝ)| ≤ C * ((N : ℝ) / m) ^ θ := by
  obtain ⟨C, hC, h⟩ := mertens_bound θ hθ hM
  refine ⟨C, hC, fun N m hm hmN => ?_⟩
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have ht : (1 : ℝ) ≤ (N : ℝ) / m := by
    rw [le_div_iff₀ hm0]; simp only [one_mul]; exact_mod_cast hmN
  have := h ((N : ℝ) / m) ht
  rw [Nat.floor_div_eq_div] at this
  have hsum : ∑ k ∈ Icc 0 (N / m), (ArithmeticFunction.moebius k : ℝ) =
      ∑ k ∈ Icc 1 (N / m), (ArithmeticFunction.moebius k : ℝ) := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, ← Finset.Icc_add_one_left_eq_Ioc]
    simp
  rwa [hsum] at this

lemma gcd_sum_bound (θ : ℝ) (hθ : 1 / 2 < θ) : ∃ Z : ℝ, 0 ≤ Z ∧ ∀ N : ℕ,
    ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (Nat.gcd m n : ℝ) ^ 2 / ((m : ℝ) * n) ^ (1 + θ) ≤ Z := by
  have hs1 : Summable (fun g : ℕ => (((g : ℝ) ^ θ) ^ 2)⁻¹) := by
    have := Real.summable_nat_rpow_inv.mpr (by linarith : 1 < 2 * θ)
    refine this.congr fun g => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; ring_nf
  have hs2 : Summable (fun a : ℕ => ((a : ℝ) ^ (1 + θ))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  set Z1 := ∑' g : ℕ, (((g : ℝ) ^ θ) ^ 2)⁻¹
  set Z2 := ∑' a : ℕ, ((a : ℝ) ^ (1 + θ))⁻¹
  have hZ1 : 0 ≤ Z1 := tsum_nonneg fun _ => by positivity
  have hZ2 : 0 ≤ Z2 := tsum_nonneg fun _ => by positivity
  refine ⟨Z1 * (Z2 * Z2), by positivity, fun N => ?_⟩
  set H : ℕ × ℕ × ℕ → ℝ := fun t =>
    (((t.1 : ℝ) ^ θ) ^ 2)⁻¹ * (((t.2.1 : ℝ) ^ (1 + θ))⁻¹ * ((t.2.2 : ℝ) ^ (1 + θ))⁻¹) with hH
  set φ : ℕ × ℕ → ℕ × ℕ × ℕ := fun p => (Nat.gcd p.1 p.2, p.1 / Nat.gcd p.1 p.2, p.2 / Nat.gcd p.1 p.2)
  have hval : ∀ p ∈ Icc 1 N ×ˢ Icc 1 N,
      (Nat.gcd p.1 p.2 : ℝ) ^ 2 / ((p.1 : ℝ) * p.2) ^ (1 + θ) = H (φ p) := by
    intro p hp
    simp only [mem_product, mem_Icc] at hp
    simp only [hH, φ]
    have hg0 : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left _ (by omega)
    obtain ⟨a, ha⟩ := Nat.gcd_dvd_left p.1 p.2
    obtain ⟨b, hb⟩ := Nat.gcd_dvd_right p.1 p.2
    have ha' : p.1 / Nat.gcd p.1 p.2 = a :=
      Nat.div_eq_of_eq_mul_left hg0 (by rw [mul_comm]; exact ha)
    have hb' : p.2 / Nat.gcd p.1 p.2 = b :=
      Nat.div_eq_of_eq_mul_left hg0 (by rw [mul_comm]; exact hb)
    rw [ha', hb']
    have e1 : ((p.1 : ℝ) * p.2) = ((Nat.gcd p.1 p.2 : ℝ) * Nat.gcd p.1 p.2) * ((a : ℝ) * b) := by
      have h1 : ((p.1 : ℕ) : ℝ) = (Nat.gcd p.1 p.2 : ℝ) * a := by exact_mod_cast ha
      have h2 : ((p.2 : ℕ) : ℝ) = (Nat.gcd p.1 p.2 : ℝ) * b := by exact_mod_cast hb
      rw [h1, h2]; ring
    rw [e1]
    have ha0 : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have hb0 : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; omega)
    generalize Nat.gcd p.1 p.2 = g at hg0 ⊢
    have hgR : (0 : ℝ) < g := by exact_mod_cast hg0
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity)]
    have e2 : (g : ℝ) ^ (1 + θ) = g * g ^ θ := by
      rw [Real.rpow_add hgR, Real.rpow_one]
    rw [e2]
    have : (0 : ℝ) < (g : ℝ) ^ θ := Real.rpow_pos_of_pos hgR θ
    have : (0 : ℝ) < (a : ℝ) ^ (1 + θ) := Real.rpow_pos_of_pos (by exact_mod_cast ha0) _
    have : (0 : ℝ) < (b : ℝ) ^ (1 + θ) := Real.rpow_pos_of_pos (by exact_mod_cast hb0) _
    field_simp
  have hinj : Set.InjOn φ (Icc 1 N ×ˢ Icc 1 N : Finset (ℕ × ℕ)) := by
    intro p hp p' hp' h
    simp only [φ, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    simp only [coe_product, coe_Icc, Set.mem_prod, Set.mem_Icc] at hp hp'
    have e1 : p.1 = Nat.gcd p.1 p.2 * (p.1 / Nat.gcd p.1 p.2) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
    have e2 : p.2 = Nat.gcd p.1 p.2 * (p.2 / Nat.gcd p.1 p.2) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
    have e1' : p'.1 = Nat.gcd p'.1 p'.2 * (p'.1 / Nat.gcd p'.1 p'.2) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
    have e2' : p'.2 = Nat.gcd p'.1 p'.2 * (p'.2 / Nat.gcd p'.1 p'.2) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
    ext
    · calc p.1 = _ := e1
        _ = _ := by rw [h2, h1]
        _ = p'.1 := e1'.symm
    · calc p.2 = _ := e2
        _ = _ := by rw [h3, h1]
        _ = p'.2 := e2'.symm
  have hsub : (Icc 1 N ×ˢ Icc 1 N).image φ ⊆ Icc 1 N ×ˢ (Icc 1 N ×ˢ Icc 1 N) := by
    intro t ht
    simp only [mem_image, mem_product, mem_Icc] at ht ⊢
    obtain ⟨p, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩ := ht
    simp only [φ]
    have hg0 : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left _ (by omega)
    refine ⟨⟨hg0, (Nat.gcd_le_left _ (by omega)).trans h2⟩, ⟨?_, (Nat.div_le_self _ _).trans h2⟩,
      ⟨?_, (Nat.div_le_self _ _).trans h4⟩⟩
    · exact Nat.div_pos (Nat.gcd_le_left _ (by omega)) hg0
    · exact Nat.div_pos (Nat.gcd_le_right _ (by omega)) hg0
  have hH0 : ∀ t, 0 ≤ H t := fun t => by simp only [hH]; positivity
  rw [← Finset.sum_product' (f := fun m n => (Nat.gcd m n : ℝ) ^ 2 / ((m : ℝ) * n) ^ (1 + θ))]
  rw [Finset.sum_congr rfl hval, ← Finset.sum_image hinj]
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => hH0 t)).trans ?_
  rw [Finset.sum_product, ]
  simp only [hH]
  simp_rw [← Finset.mul_sum, Finset.sum_product, ← Finset.mul_sum, ← Finset.sum_mul]
  have b1 : ∑ g ∈ Icc 1 N, (((g : ℝ) ^ θ) ^ 2)⁻¹ ≤ Z1 :=
    hs1.sum_le_tsum _ (fun _ _ => by positivity)
  have b2 : ∑ a ∈ Icc 1 N, ((a : ℝ) ^ (1 + θ))⁻¹ ≤ Z2 :=
    hs2.sum_le_tsum _ (fun _ _ => by positivity)
  have p1 : 0 ≤ ∑ g ∈ Icc 1 N, (((g : ℝ) ^ θ) ^ 2)⁻¹ := Finset.sum_nonneg fun _ _ => by positivity
  have p2 : 0 ≤ ∑ a ∈ Icc 1 N, ((a : ℝ) ^ (1 + θ))⁻¹ := Finset.sum_nonneg fun _ _ => by positivity
  calc _ = (∑ g ∈ Icc 1 N, (((g : ℝ) ^ θ) ^ 2)⁻¹) *
        ((∑ a ∈ Icc 1 N, ((a : ℝ) ^ (1 + θ))⁻¹) * (∑ a ∈ Icc 1 N, ((a : ℝ) ^ (1 + θ))⁻¹)) := by
        rw [Finset.sum_mul]
    _ ≤ _ := by gcongr

end FareyAux


namespace FareyAux

open Finset Filter MeasureTheory

lemma floor_eq_sub_fract (y : ℝ) (hy : 0 ≤ y) : (⌊y⌋₊ : ℝ) = y - Int.fract y := by
  rw [natCast_floor_eq_intCast_floor hy, ← Int.self_sub_floor]; ring

noncomputable def AA (N : ℕ) (x : ℝ) : ℝ := ∑ u ∈ FF N, if (u : ℝ) ≤ x then (1 : ℝ) else 0

noncomputable def ff (N : ℕ) (x : ℝ) : ℝ := ∑ m ∈ Icc 1 N, cc N m * G (m * x)

noncomputable def EE (N : ℕ) (x : ℝ) : ℝ := -ff N x - 1 / 2

lemma AA_mono (N : ℕ) {x y : ℝ} (h : x ≤ y) : AA N x ≤ AA N y := by
  unfold AA
  apply Finset.sum_le_sum; intro u _
  split_ifs with h1 h2 <;> first | linarith | (exfalso; linarith)

lemma AA_one (N : ℕ) : AA N 1 = (FF N).card := by
  unfold AA
  rw [Finset.card_eq_sum_ones]; push_cast
  apply Finset.sum_congr rfl; intro u hu; simp [(FF_bounds hu).2]

lemma E_eq {N : ℕ} (hN : 1 ≤ N) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    AA N x - ((FF N).card : ℝ) * x = EE N x := by
  unfold AA EE ff
  rw [count_formula x hx0 hx1, card_formula]
  have h1 : ∑ m ∈ Icc 1 N, cc N m * (⌊(m : ℝ) * x⌋₊ : ℝ) =
      ∑ m ∈ Icc 1 N, cc N m * ((m : ℝ) * x) - ∑ m ∈ Icc 1 N, cc N m * Int.fract ((m : ℝ) * x) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro m _
    rw [floor_eq_sub_fract _ (by positivity)]; ring
  have h2 : ∑ m ∈ Icc 1 N, cc N m * G ((m : ℝ) * x) =
      ∑ m ∈ Icc 1 N, cc N m * Int.fract ((m : ℝ) * x) - (1 / 2) * ∑ m ∈ Icc 1 N, cc N m := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro m _
    unfold G; ring
  rw [sum_cc hN] at h2
  have h3 : (∑ m ∈ Icc 1 N, cc N m * (m : ℝ)) * x = ∑ m ∈ Icc 1 N, cc N m * ((m : ℝ) * x) := by
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro m _; ring
  rw [h1, h2, h3]; ring

lemma measurable_ff (N : ℕ) : Measurable (ff N) := by
  unfold ff
  apply Finset.measurable_sum; intro m _
  exact measurable_const.mul (measurable_G.comp (by fun_prop))

lemma abs_EE_le (N : ℕ) (x : ℝ) : |EE N x| ≤ ∑ m ∈ Icc 1 N, |cc N m| + 1 := by
  unfold EE ff
  have : |∑ m ∈ Icc 1 N, cc N m * G (m * x)| ≤ ∑ m ∈ Icc 1 N, |cc N m| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [abs_mul]
    calc |cc N m| * |G (↑m * x)| ≤ |cc N m| * 1 :=
          mul_le_mul_of_nonneg_left (abs_G_le _) (abs_nonneg _)
      _ = |cc N m| := mul_one _
  have h2 := abs_sub (-∑ m ∈ Icc 1 N, cc N m * G (m * x)) (1 / 2)
  rw [abs_neg] at h2
  have : |(1 : ℝ) / 2| ≤ 1 := by norm_num [abs_of_pos]
  linarith

lemma integrableOn_EE_sq (N : ℕ) (s : Set ℝ) (hs : volume s ≠ ⊤) :
    IntegrableOn (fun x => EE N x ^ 2) s := by
  refine Measure.integrableOn_of_bounded (M := (∑ m ∈ Icc 1 N, |cc N m| + 1) ^ 2) hs ?_ ?_
  · exact (((measurable_ff N).neg.sub measurable_const).pow_const 2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_EE_le N x) 2

lemma comparison {N : ℕ} (hN : 1 ≤ N) :
    ∑ r ∈ FF N, (AA N (r : ℝ) - ((FF N).card : ℝ) * r) ^ 2 ≤
      2 * (FF N).card + 4 * (N : ℝ) ^ 2 * ∫ x in (0:ℝ)..1, EE N x ^ 2 := by
  set Φ : ℝ := ((FF N).card : ℝ) with hΦ
  set δ : ℝ := 1 / (N : ℝ) ^ 2 with hδ
  set e : ℚ → ℝ := fun r => AA N (r : ℝ) - Φ * r with he
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hδ0 : 0 < δ := by positivity
  have hΦδ : Φ * δ ≤ 1 := by
    rw [hδ, mul_one_div, div_le_one (by positivity)]; exact card_FF_le N
  have hNδ : (N : ℝ) ^ 2 * δ = 1 := by rw [hδ]; field_simp
  have hδN : δ ≤ 1 / (N : ℝ) := by
    rw [hδ]; apply one_div_le_one_div_of_le (by positivity); nlinarith
  set I := ∫ x in Set.Icc (0:ℝ) 1, EE N x ^ 2 with hI
  have hIeq : I = ∫ x in (0:ℝ)..1, EE N x ^ 2 := by
    rw [hI, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le zero_le_one]
  have hIcc : IntegrableOn (fun x => EE N x ^ 2) (Set.Icc 0 1) :=
    integrableOn_EE_sq N _ (by simp)
  -- pointwise split
  have hpt : ∀ r ∈ FF N, e r ^ 2 ≤ 2 + 2 * (if 1 ≤ e r then (e r - 1) ^ 2 else 0) +
      2 * (if e r ≤ -1 then (e r + 1) ^ 2 else 0) := by
    intro r _
    split_ifs with h1 h2 h2
    · linarith
    · nlinarith [sq_nonneg (e r - 2)]
    · nlinarith [sq_nonneg (e r + 2)]
    · have : e r ^ 2 ≤ 1 := by nlinarith
      linarith
  have hsplit : ∑ r ∈ FF N, e r ^ 2 ≤ 2 * Φ +
      2 * ∑ r ∈ (FF N).filter (fun r => 1 ≤ e r), (e r - 1) ^ 2 +
      2 * ∑ r ∈ (FF N).filter (fun r => e r ≤ -1), (e r + 1) ^ 2 := by
    refine (Finset.sum_le_sum hpt).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hΦ]
    ring
  -- e at 1 vanishes
  have he1 : e 1 = 0 := by
    simp only [he, Rat.cast_one, mul_one]; rw [AA_one]; ring
  -- right intervals
  have hright : ∀ r ∈ (FF N).filter (fun r => 1 ≤ e r),
      δ * (e r - 1) ^ 2 ≤ ∫ x in Set.Ioc (r : ℝ) (r + δ), EE N x ^ 2 := by
    intro r hr
    rw [mem_filter] at hr
    have hb := FF_bounds hr.1
    have hne : r ≠ 1 := by rintro rfl; rw [he1] at hr; linarith [hr.2]
    have hsp := FF_spacing hr.1 (one_mem_FF hN) hne
    rw [← hδ, Rat.cast_one, abs_sub_comm, abs_of_nonneg (by linarith)] at hsp
    have hr0 : 0 ≤ (r : ℝ) := le_trans (by positivity) hb.1
    rw [← intervalIntegral.integral_of_le (by linarith)]
    have : ∫ x in (r : ℝ)..(r + δ), (e r - 1) ^ 2 = δ * (e r - 1) ^ 2 := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    rw [← this]
    apply intervalIntegral.integral_mono_on (by linarith) (by simp)
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
      exact integrableOn_EE_sq N _ (by simp)
    · intro x hx
      have hx0 : 0 ≤ x := le_trans hr0 hx.1
      have hx1 : x ≤ 1 := by linarith [hx.2]
      rw [← E_eq hN x hx0 hx1]
      have hA := AA_mono N hx.1
      have : Φ * x ≤ Φ * r + 1 := by
        have : Φ * x ≤ Φ * (r + δ) := mul_le_mul_of_nonneg_left hx.2 (by positivity)
        nlinarith
      have hge : e r - 1 ≤ AA N x - Φ * x := by simp only [he]; linarith
      have : 0 ≤ e r - 1 := by linarith [hr.2]
      nlinarith
  have hleft : ∀ r ∈ (FF N).filter (fun r => e r ≤ -1),
      δ * (e r + 1) ^ 2 ≤ ∫ x in Set.Ioc ((r : ℝ) - δ) r, EE N x ^ 2 := by
    intro r hr
    rw [mem_filter] at hr
    have hb := FF_bounds hr.1
    have hrδ : 0 ≤ (r : ℝ) - δ := by linarith [hb.1]
    rw [← intervalIntegral.integral_of_le (by linarith)]
    have : ∫ x in ((r : ℝ) - δ)..r, (e r + 1) ^ 2 = δ * (e r + 1) ^ 2 := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    rw [← this]
    apply intervalIntegral.integral_mono_on (by linarith) (by simp)
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
      exact integrableOn_EE_sq N _ (by simp)
    · intro x hx
      have hx0 : 0 ≤ x := le_trans hrδ hx.1
      have hx1 : x ≤ 1 := le_trans hx.2 hb.2
      rw [← E_eq hN x hx0 hx1]
      have hA := AA_mono N hx.2
      have : Φ * r ≤ Φ * x + 1 := by
        have : Φ * (r - δ) ≤ Φ * x := mul_le_mul_of_nonneg_left hx.1 (by positivity)
        nlinarith
      have hle : AA N x - Φ * x ≤ e r + 1 := by simp only [he]; linarith
      have : e r + 1 ≤ 0 := by linarith [hr.2]
      nlinarith
  -- disjoint unions
  have hdisj : ∀ (R : Finset ℚ), R ⊆ FF N → ∀ t : ℝ,
      ∑ r ∈ R, ∫ x in Set.Ioc ((r : ℝ) + t) (r + t + δ), EE N x ^ 2 ≤
        ∫ x in ⋃ r ∈ R, Set.Ioc ((r : ℝ) + t) (r + t + δ), EE N x ^ 2 := by
    intro R hR t
    rw [integral_biUnion_finset]
    · intro r _; exact measurableSet_Ioc
    · intro r hr r' hr' hne
      simp only [Function.onFun]
      rw [Set.Ioc_disjoint_Ioc]
      have hsp := FF_spacing (hR hr) (hR hr') hne
      rw [← hδ] at hsp
      rcases le_total (r : ℝ) r' with h | h
      · rw [abs_sub_comm, abs_of_nonneg (by linarith)] at hsp
        calc min ((r : ℝ) + t + δ) (r' + t + δ) ≤ r + t + δ := min_le_left _ _
          _ ≤ r' + t := by linarith
          _ ≤ max ((r : ℝ) + t) (r' + t) := le_max_right _ _
      · rw [abs_of_nonneg (by linarith)] at hsp
        calc min ((r : ℝ) + t + δ) (r' + t + δ) ≤ r' + t + δ := min_le_right _ _
          _ ≤ r + t := by linarith
          _ ≤ max ((r : ℝ) + t) (r' + t) := le_max_left _ _
    · intro r _; exact integrableOn_EE_sq N _ (by simp)
  have hsub : ∀ (R : Finset ℚ) (t : ℝ),
      (⋃ r ∈ R, Set.Ioc ((r : ℝ) + t) (r + t + δ)) ⊆ Set.Icc 0 1 →
      ∫ x in ⋃ r ∈ R, Set.Ioc ((r : ℝ) + t) (r + t + δ), EE N x ^ 2 ≤ I := by
    intro R t h
    exact setIntegral_mono_set hIcc (Filter.Eventually.of_forall fun x => sq_nonneg _)
      h.eventuallyLE
  -- right sum
  set Rp := (FF N).filter (fun r => 1 ≤ e r)
  set Rm := (FF N).filter (fun r => e r ≤ -1)
  have hRp : ∑ r ∈ Rp, (e r - 1) ^ 2 ≤ (N : ℝ) ^ 2 * I := by
    have h1 : ∑ r ∈ Rp, (e r - 1) ^ 2 ≤
        (N : ℝ) ^ 2 * ∑ r ∈ Rp, ∫ x in Set.Ioc ((r : ℝ) + 0) (r + 0 + δ), EE N x ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro r hr
      have := hright r hr
      simp only [add_zero]
      calc (e r - 1) ^ 2 = (N : ℝ) ^ 2 * (δ * (e r - 1) ^ 2) := by rw [← mul_assoc, hNδ, one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
    refine h1.trans (mul_le_mul_of_nonneg_left ((hdisj Rp (filter_subset _ _) 0).trans
      (hsub Rp 0 ?_)) (by positivity))
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_Ioc, add_zero] at hx
    obtain ⟨r, hr, hx1, hx2⟩ := hx
    rw [mem_filter] at hr
    have hb := FF_bounds hr.1
    have hne : r ≠ 1 := by rintro rfl; rw [he1] at hr; linarith [hr.2]
    have hsp := FF_spacing hr.1 (one_mem_FF hN) hne
    rw [← hδ, Rat.cast_one, abs_sub_comm, abs_of_nonneg (by linarith)] at hsp
    exact ⟨by linarith [le_trans (by positivity : (0:ℝ) ≤ 1 / N) hb.1], by linarith⟩
  have hRm : ∑ r ∈ Rm, (e r + 1) ^ 2 ≤ (N : ℝ) ^ 2 * I := by
    have h1 : ∑ r ∈ Rm, (e r + 1) ^ 2 ≤
        (N : ℝ) ^ 2 * ∑ r ∈ Rm, ∫ x in Set.Ioc ((r : ℝ) + -δ) (r + -δ + δ), EE N x ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro r hr
      have := hleft r hr
      have e1 : (r : ℝ) + -δ + δ = r := by ring
      rw [e1, ← sub_eq_add_neg]
      calc (e r + 1) ^ 2 = (N : ℝ) ^ 2 * (δ * (e r + 1) ^ 2) := by rw [← mul_assoc, hNδ, one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
    refine h1.trans (mul_le_mul_of_nonneg_left ((hdisj Rm (filter_subset _ _) (-δ)).trans
      (hsub Rm (-δ) ?_)) (by positivity))
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_Ioc] at hx
    obtain ⟨r, hr, hx1, hx2⟩ := hx
    rw [mem_filter] at hr
    have hb := FF_bounds hr.1
    exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have hfin : ∑ r ∈ FF N, e r ^ 2 ≤ 2 * Φ + 4 * (N : ℝ) ^ 2 * I := by
    have := hsplit; nlinarith
  rw [← hIeq]
  exact hfin

end FareyAux

namespace FareyAux

open Finset Filter MeasureTheory

lemma intervalIntegrable_ff_sq (N : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x => ff N x ^ 2) volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := (∑ m ∈ Icc 1 N, |cc N m|) ^ 2) ?_ ?_ ?_
  · rw [Set.uIoc]; exact measure_Ioc_lt_top.ne
  · exact ((measurable_ff N).pow_const 2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_pow]
    apply pow_le_pow_left₀ (abs_nonneg _)
    unfold ff
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [abs_mul]
    calc |cc N m| * |G (↑m * x)| ≤ |cc N m| * 1 :=
          mul_le_mul_of_nonneg_left (abs_G_le _) (abs_nonneg _)
      _ = |cc N m| := mul_one _

lemma int_EE_le (N : ℕ) :
    ∫ x in (0:ℝ)..1, EE N x ^ 2 ≤ 2 * (∫ x in (0:ℝ)..1, ff N x ^ 2) + 1 / 2 := by
  have h1 : IntervalIntegrable (fun x => EE N x ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
    exact integrableOn_EE_sq N _ (by simp)
  have h2 : IntervalIntegrable (fun x => 2 * ff N x ^ 2 + 1 / 2) volume 0 1 :=
    ((intervalIntegrable_ff_sq N 0 1).const_mul 2).add intervalIntegrable_const
  calc ∫ x in (0:ℝ)..1, EE N x ^ 2 ≤ ∫ x in (0:ℝ)..1, (2 * ff N x ^ 2 + 1 / 2) := by
        apply intervalIntegral.integral_mono_on zero_le_one h1 h2
        intro x _
        unfold EE
        nlinarith [sq_nonneg (ff N x - 1 / 2)]
    _ = _ := by
        rw [intervalIntegral.integral_add ((intervalIntegrable_ff_sq N 0 1).const_mul 2)
          intervalIntegrable_const, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const]
        simp

theorem fareyL2_of_moebius
    (hM : ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO atTop
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε))) :
    ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => ∑ r ∈ FF N, ((r : ℝ) - (((FF N).filter (fun u => u ≤ r)).card : ℝ) /
        (FF N).card) ^ 2) (fun N : ℕ => (N : ℝ) ^ (-1 + ε)) := by
  intro ε hε
  set θ : ℝ := 1 / 2 + ε / 2 with hθ
  have hθ1 : 1 / 2 < θ := by linarith
  obtain ⟨C, hC, hcc⟩ := cc_bound θ hθ1 hM
  obtain ⟨Z, hZ, hgcd⟩ := gcd_sum_bound θ hθ1
  set K : ℝ := 64 * (4 + 32 * C ^ 2 * Z) with hK
  refine Asymptotics.IsBigO.of_bound K ?_
  rw [Filter.eventually_atTop]
  refine ⟨1, fun N hN => ?_⟩
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set Φ : ℝ := ((FF N).card : ℝ) with hΦ
  have hΦlo := card_FF_ge N hN
  have hΦhi := card_FF_le N
  have hΦ0 : 0 < Φ := by have : 0 < (N : ℝ) ^ 2 / 8 := by positivity
                         linarith
  -- rewrite the sum
  have hterm : ∀ r ∈ FF N, ((r : ℝ) - (((FF N).filter (fun u => u ≤ r)).card : ℝ) / Φ) ^ 2 =
      (AA N (r : ℝ) - Φ * r) ^ 2 / Φ ^ 2 := by
    intro r _
    have : (((FF N).filter (fun u => u ≤ r)).card : ℝ) = AA N (r : ℝ) := by
      rw [Finset.card_filter]; push_cast
      unfold AA
      apply Finset.sum_congr rfl; intro u _
      simp only [Rat.cast_le]
    rw [this]; field_simp; ring
  have hS : ∑ r ∈ FF N, ((r : ℝ) - (((FF N).filter (fun u => u ≤ r)).card : ℝ) / Φ) ^ 2 =
      (∑ r ∈ FF N, (AA N (r : ℝ) - Φ * r) ^ 2) / Φ ^ 2 := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_div]
  -- bound the integral
  set T : ℝ := (N : ℝ) ^ θ with hT
  have hT1 : 1 ≤ T := Real.one_le_rpow hNR (by linarith)
  have hpar := parseval_bound N (cc N)
  have hpair : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N,
      |cc N m| * |cc N n| * ((Nat.gcd m n : ℝ) ^ 2 / (m * n)) ≤
        C ^ 2 * T ^ 2 * ((Nat.gcd m n : ℝ) ^ 2 / ((m : ℝ) * n) ^ (1 + θ)) := by
    intro m hm n hn
    rw [mem_Icc] at hm hn
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    have b1 := hcc N m hm.1 hm.2
    have b2 := hcc N n hn.1 hn.2
    have hg : 0 ≤ (Nat.gcd m n : ℝ) ^ 2 / (m * n) := by positivity
    calc |cc N m| * |cc N n| * ((Nat.gcd m n : ℝ) ^ 2 / (m * n))
        ≤ (C * ((N : ℝ) / m) ^ θ) * (C * ((N : ℝ) / n) ^ θ) * ((Nat.gcd m n : ℝ) ^ 2 / (m * n)) := by
          apply mul_le_mul_of_nonneg_right _ hg
          exact mul_le_mul b1 b2 (abs_nonneg _) (by positivity)
      _ = _ := by
          rw [Real.div_rpow hN0.le hm0.le, Real.div_rpow hN0.le hn0.le,
            Real.mul_rpow hm0.le hn0.le, Real.rpow_add hm0 1 θ, Real.rpow_add hn0 1 θ,
            Real.rpow_one, Real.rpow_one, ← hT]
          have : (0 : ℝ) < (m : ℝ) ^ θ := Real.rpow_pos_of_pos hm0 θ
          have : (0 : ℝ) < (n : ℝ) ^ θ := Real.rpow_pos_of_pos hn0 θ
          field_simp
  have hsum2 : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      |cc N m| * |cc N n| * ((Nat.gcd m n : ℝ) ^ 2 / (m * n)) ≤ C ^ 2 * T ^ 2 * Z := by
    calc _ ≤ ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
          C ^ 2 * T ^ 2 * ((Nat.gcd m n : ℝ) ^ 2 / ((m : ℝ) * n) ^ (1 + θ)) :=
          Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => hpair m hm n hn
      _ = C ^ 2 * T ^ 2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
          ((Nat.gcd m n : ℝ) ^ 2 / ((m : ℝ) * n) ^ (1 + θ)) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _; rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hgcd N) (by positivity)
  have hff : ∫ x in (0:ℝ)..1, ff N x ^ 2 ≤ 4 * (C ^ 2 * T ^ 2 * Z) := by
    have : ∫ x in (0:ℝ)..1, ff N x ^ 2 =
        ∫ x in (0:ℝ)..1, (∑ m ∈ Icc 1 N, cc N m * G (m * x)) ^ 2 := rfl
    rw [this]; linarith
  have hEE := int_EE_le N
  have hcomp := comparison hN
  rw [← hΦ] at hcomp
  -- assemble
  have hnum : ∑ r ∈ FF N, (AA N (r : ℝ) - Φ * r) ^ 2 ≤ (N : ℝ) ^ 2 * T ^ 2 * (4 + 32 * C ^ 2 * Z) := by
    have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have hT2 : (1 : ℝ) ≤ T ^ 2 := by nlinarith
    have hCZ : 0 ≤ C ^ 2 * Z := by positivity
    calc _ ≤ 2 * Φ + 4 * (N : ℝ) ^ 2 * ∫ x in (0:ℝ)..1, EE N x ^ 2 := hcomp
      _ ≤ 2 * (N : ℝ) ^ 2 + 4 * (N : ℝ) ^ 2 * (2 * (4 * (C ^ 2 * T ^ 2 * Z)) + 1 / 2) := by
          have : ∫ x in (0:ℝ)..1, EE N x ^ 2 ≤ 2 * (4 * (C ^ 2 * T ^ 2 * Z)) + 1 / 2 := by
            linarith
          have h4 : 0 ≤ 4 * (N : ℝ) ^ 2 := by positivity
          nlinarith
      _ = (N : ℝ) ^ 2 * (4 + 32 * (C ^ 2 * Z) * T ^ 2) := by ring
      _ ≤ (N : ℝ) ^ 2 * (T ^ 2 * 4 + 32 * (C ^ 2 * Z) * T ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
      _ = _ := by ring
  have hpow : (N : ℝ) ^ (-1 + ε) = T ^ 2 / (N : ℝ) ^ 2 := by
    rw [hT, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le,
      ← Real.rpow_sub hN0]
    congr 1; rw [hθ]; push_cast; ring
  have hS0 : 0 ≤ ∑ r ∈ FF N, ((r : ℝ) - (((FF N).filter (fun u => u ≤ r)).card : ℝ) / Φ) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [Real.norm_of_nonneg hS0, Real.norm_of_nonneg (by positivity), hS, hpow]
  have hΦ2 : (N : ℝ) ^ 4 / 64 ≤ Φ ^ 2 := by
    have : 0 ≤ (N : ℝ) ^ 2 / 8 := by positivity
    calc (N : ℝ) ^ 4 / 64 = ((N : ℝ) ^ 2 / 8) ^ 2 := by ring
      _ ≤ Φ ^ 2 := pow_le_pow_left₀ this hΦlo 2
  rw [div_le_iff₀ (by positivity)]
  have hnum0 : 0 ≤ ∑ r ∈ FF N, (AA N (r : ℝ) - Φ * r) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hK0 : 0 ≤ 4 + 32 * C ^ 2 * Z := by positivity
  calc ∑ r ∈ FF N, (AA N (r : ℝ) - Φ * r) ^ 2 ≤ (N : ℝ) ^ 2 * T ^ 2 * (4 + 32 * C ^ 2 * Z) := hnum
    _ = K * (T ^ 2 / (N : ℝ) ^ 2) * ((N : ℝ) ^ 4 / 64) := by
        rw [hK]; field_simp
    _ ≤ K * (T ^ 2 / (N : ℝ) ^ 2) * Φ ^ 2 := by
        apply mul_le_mul_of_nonneg_left hΦ2; positivity

end FareyAux

theorem solution :
    let F (N : ℕ) : Finset ℚ := (Finset.Icc 1 N).biUnion fun q =>
      ((Finset.Icc 1 q).filter fun a => Nat.Coprime a q).image fun a : ℕ => (a : ℚ) / q
    let D (N : ℕ) (r : ℚ) : ℝ := (r : ℝ) - (((F N).filter (fun u => u ≤ r)).card : ℝ) / (F N).card
    ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO Filter.atTop (fun N : ℕ => ∑ r ∈ F N, (D N r)^2) (fun N : ℕ => (N : ℝ)^(-1 + ε)) := by
  intro F D
  exact FareyAux.fareyL2_of_moebius
    (moebius_summatory_rpow_bound_of_riemannHypothesis riemann_hypothesis)
