-- Prove2me | solution 1 for BroughanRH.amoroso
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T01:54:59.186645+00:00
-- url     : https://prove2.me/submissions/7380d651-d9b8-436a-9e9e-025ea2e1bf1d
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

open Finset Filter MeasureTheory Complex Real

lemma parseval_gen (N : ℕ) (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) (V : ℝ → ℂ)
    (hV : MemLp V 2 (volume.restrict (Set.Ioc (0:ℝ) 1)))
    (hcoef : ∀ k : ℤ, ‖fourierCoeffOn zero_lt_one V k‖ ≤ ∑ m ∈ Icc 1 N, a m * bb m k) :
    ∫ x in (0:ℝ)..1, ‖V x‖ ^ 2 ≤
      4 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, a m * a n * ((Nat.gcd m n : ℝ) ^ 2 / (m * n)) := by
  have hP := hasSum_sq_fourierCoeffOn zero_lt_one hV
  have hint : ((1:ℝ) - 0)⁻¹ • ∫ x in (0:ℝ)..1, ‖V x‖ ^ 2 = ∫ x in (0:ℝ)..1, ‖V x‖ ^ 2 := by
    simp
  rw [hint] at hP
  rw [← hP.tsum_eq]
  have hterm : ∀ k : ℤ, ‖fourierCoeffOn zero_lt_one V k‖ ^ 2 ≤
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, a m * a n * ((m : ℝ) * n * gL (Nat.lcm m n) k) := by
    intro k
    have h2 : (∑ m ∈ Icc 1 N, a m * bb m k) ^ 2 =
        ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, a m * a n * (bb m k * bb n k) := by
      rw [sq, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro m _; apply Finset.sum_congr rfl; intro n _; ring
    calc _ ≤ (∑ m ∈ Icc 1 N, a m * bb m k) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hcoef k) 2
      _ = _ := h2
      _ ≤ _ := by
        apply Finset.sum_le_sum; intro m hm; apply Finset.sum_le_sum; intro n hn
        apply mul_le_mul_of_nonneg_left
          (bb_mul_le m n (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hn).1 k)
        exact mul_nonneg (ha m) (ha n)
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
  have e : (m : ℝ) * n * (4 / ((Nat.lcm m n : ℕ) : ℝ) ^ 2) =
      4 * ((Nat.gcd m n : ℝ) ^ 2 / (m * n)) := by
    rw [← hgl]; field_simp
  have hpos : 0 ≤ a m * a n := mul_nonneg (ha m) (ha n)
  calc a m * a n * ((m : ℝ) * n * ∑' k, gL (Nat.lcm m n) k)
      ≤ a m * a n * ((m : ℝ) * n * (4 / ((Nat.lcm m n : ℕ) : ℝ) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hpos
        exact mul_le_mul_of_nonneg_left ht (by positivity)
    _ = 4 * (a m * a n * ((Nat.gcd m n : ℝ) ^ 2 / (m * n))) := by rw [e]; ring

/-! ### cyclotomic products -/

lemma log_norm_cyc_sum (z : ℂ) (hz : ‖z‖ < 1) (n : ℕ) (hn : 0 < n) :
    ∑ i ∈ n.divisors, Real.log ‖(Polynomial.cyclotomic i ℂ).eval z‖ = Real.log ‖1 - z ^ n‖ ∧
      ∀ i ∈ n.divisors, (Polynomial.cyclotomic i ℂ).eval z ≠ 0 := by
  have h := congrArg (Polynomial.eval z) (Polynomial.prod_cyclotomic_eq_X_pow_sub_one hn ℂ)
  rw [Polynomial.eval_prod] at h
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] at h
  have hne : z ^ n - 1 ≠ 0 := by
    intro h0
    have : ‖z ^ n‖ = 1 := by rw [sub_eq_zero.mp h0, norm_one]
    rw [norm_pow] at this
    have : ‖z‖ ^ n < 1 := pow_lt_one₀ (norm_nonneg _) hz (by omega)
    linarith
  have hall : ∀ i ∈ n.divisors, (Polynomial.cyclotomic i ℂ).eval z ≠ 0 := by
    rw [← h] at hne
    exact Finset.prod_ne_zero_iff.mp hne
  refine ⟨?_, hall⟩
  rw [norm_sub_rev, ← h, norm_prod, Real.log_prod]
  intro i hi; exact norm_ne_zero_iff.mpr (hall i hi)

lemma log_norm_F (N : ℕ) (z : ℂ) (hz : ‖z‖ < 1) :
    Real.log ‖(∏ j ∈ Icc 1 N, Polynomial.cyclotomic j ℂ).eval z‖ =
      ∑ m ∈ Icc 1 N, cc N m * Real.log ‖1 - z ^ m‖ := by
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq
    (f := fun i => Real.log ‖(Polynomial.cyclotomic i ℂ).eval z‖)
    (g := fun n => Real.log ‖1 - z ^ n‖)).mp (fun n hn => (log_norm_cyc_sum z hz n hn).1)
  rw [Polynomial.eval_prod, norm_prod, Real.log_prod]
  · unfold cc
    rw [← rearrange N (fun m => Real.log ‖1 - z ^ m‖)]
    apply Finset.sum_congr rfl
    intro j hj
    have hj0 : 0 < j := (Finset.mem_Icc.mp hj).1
    rw [← hinv j hj0, Nat.sum_divisorsAntidiagonal (fun a b => (ArithmeticFunction.moebius a) •
      Real.log ‖1 - z ^ b‖)]
    apply Finset.sum_congr rfl; intro d _
    rw [zsmul_eq_mul]
  · intro j hj
    have hj0 : 0 < j := (Finset.mem_Icc.mp hj).1
    exact norm_ne_zero_iff.mpr ((log_norm_cyc_sum z hz j hj0).2 j (Nat.mem_divisors_self j hj0.ne'))

/-! ### the regularised logarithms -/

noncomputable def zz (ρ x : ℝ) : ℂ := (ρ : ℂ) * Complex.exp (2 * π * I * x)

lemma continuous_zz (ρ : ℝ) : Continuous (zz ρ) := by unfold zz; fun_prop

lemma norm_zz (ρ x : ℝ) (hρ : 0 ≤ ρ) : ‖zz ρ x‖ = ρ := by
  unfold zz
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ,
    norm_exp_re_zero _ (by simp [Complex.mul_re, Complex.mul_im]), mul_one]

lemma zz_pow (ρ x : ℝ) (m : ℕ) :
    zz ρ x ^ m = (ρ : ℂ) ^ m * Complex.exp (2 * π * I * (m : ℂ) * x) := by
  unfold zz; rw [mul_pow, ← Complex.exp_nat_mul]; congr 2; ring

noncomputable def uu (ρ : ℝ) (d : ℕ) (x : ℝ) : ℂ := -Complex.log (1 - zz ρ x ^ d)

lemma uu_hasSum (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (d : ℕ) (hd : 1 ≤ d) (x : ℝ) :
    HasSum (fun k : ℕ => (ρ : ℂ) ^ (d * k) * Complex.exp (2 * π * I * ((d * k : ℕ) : ℂ) * x) / k)
      (uu ρ d x) := by
  have hz : ‖zz ρ x ^ d‖ < 1 := by
    rw [norm_pow, norm_zz _ _ hρ0]; exact pow_lt_one₀ hρ0 hρ1 (by omega)
  have := Complex.hasSum_taylorSeries_neg_log hz
  unfold uu
  refine this.congr_fun ?_
  intro k
  rw [← pow_mul, zz_pow]

lemma norm_term_le (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (d : ℕ) (hd : 1 ≤ d) (x : ℝ) (k : ℕ) :
    ‖(ρ : ℂ) ^ (d * k) * Complex.exp (2 * π * I * ((d * k : ℕ) : ℂ) * x) / k‖ ≤ ρ ^ k := by
  rw [norm_div, norm_mul, norm_exp_re_zero _ (by simp [Complex.mul_re, Complex.mul_im]), mul_one,
    norm_pow, Complex.norm_real, Real.norm_of_nonneg hρ0, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : ρ ^ (d * k) ≤ ρ ^ k := pow_le_pow_of_le_one hρ0 hρ1.le (Nat.le_mul_of_pos_left _ (by omega))
  calc ρ ^ (d * k) / k ≤ ρ ^ (d * k) / 1 := div_le_div_of_nonneg_left (by positivity) one_pos hk1
    _ ≤ ρ ^ k := by rw [div_one]; exact h1

lemma norm_uu_le (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (d : ℕ) (hd : 1 ≤ d) (x : ℝ) :
    ‖uu ρ d x‖ ≤ (1 - ρ)⁻¹ := by
  have hs := uu_hasSum ρ hρ0 hρ1 d hd x
  have hg := hasSum_geometric_of_lt_one hρ0 hρ1
  have hsn : Summable (fun k : ℕ => ‖(ρ : ℂ) ^ (d * k) *
      Complex.exp (2 * π * I * ((d * k : ℕ) : ℂ) * x) / k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_le ρ hρ0 hρ1 d hd x) hg.summable
  rw [← hs.tsum_eq]
  refine (norm_tsum_le_tsum_norm hsn).trans ?_
  rw [← hg.tsum_eq]
  exact hsn.tsum_le_tsum (norm_term_le ρ hρ0 hρ1 d hd x) hg.summable

lemma measurable_uu (ρ : ℝ) (d : ℕ) : Measurable (uu ρ d) := by
  unfold uu
  exact (Complex.measurable_log.comp (measurable_const.sub
    ((continuous_zz ρ).measurable.pow_const d))).neg

lemma integral_exp_int (m : ℤ) :
    ∫ x in (0:ℝ)..1, Complex.exp (2 * π * I * m * x) = if m = 0 then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · have hc : (2 * π * I * m : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero, h]
    rw [integral_exp_mul_complex hc]
    have : Complex.exp (2 * π * I * m * ((1:ℝ) : ℂ)) = 1 := by
      rw [Complex.ofReal_one, mul_one, show (2 * π * I * m : ℂ) = m * (2 * π * I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I m
    rw [this]; simp

lemma coef_uu (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (d : ℕ) (hd : 1 ≤ d) (n : ℤ) :
    ‖fourierCoeffOn zero_lt_one (uu ρ d) n‖ ≤ bb d n := by
  rw [fourierCoeffOn_eq_integral]
  simp_rw [fourier_eq]
  simp only [sub_zero, div_one, one_smul, smul_eq_mul]
  set Fk : ℕ → ℝ → ℂ := fun k x => (ρ : ℂ) ^ (d * k) / k *
    Complex.exp (2 * π * I * ((((d * k : ℕ) : ℤ) - n : ℤ) : ℂ) * x) with hFk
  have hpt : ∀ x : ℝ, Complex.exp (2 * π * I * ((-n : ℤ) : ℂ) * x) * uu ρ d x = ∑' k, Fk k x := by
    intro x
    rw [← (uu_hasSum ρ hρ0.le hρ1 d hd x).tsum_eq, ← tsum_mul_left]
    congr 1; funext k
    simp only [hFk]
    rw [show ∀ (A P B : ℂ) (K : ℂ), Complex.exp A * (P * Complex.exp B / K) =
        P / K * (Complex.exp (B + A)) from fun A P B K => by rw [Complex.exp_add]; ring]
    congr 2
    push_cast; ring
  simp_rw [hpt]
  have hcont : ∀ k, Continuous (Fk k) := fun k => by simp only [hFk]; fun_prop
  have hnorm : ∀ k x, ‖Fk k x‖ = ρ ^ (d * k) / k := by
    intro k x
    simp only [hFk]
    rw [norm_mul, norm_exp_re_zero _ (by simp [Complex.mul_re, Complex.mul_im]), mul_one,
      norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hρ0.le, Complex.norm_natCast]
  rw [intervalIntegral.integral_of_le zero_le_one]
  rw [← integral_tsum_of_summable_integral_norm (fun k => (hcont k).integrableOn_Ioc)]
  swap
  · simp_rw [hnorm]
    have hvol : (volume.restrict (Set.Ioc (0:ℝ) 1)).real Set.univ = 1 := by simp [Measure.real]
    simp only [integral_const, smul_eq_mul, hvol, one_mul]
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun k => ?_)
      (summable_geometric_of_lt_one hρ0.le hρ1)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    calc ρ ^ (d * k) / k ≤ ρ ^ (d * k) / 1 := div_le_div_of_nonneg_left (by positivity) one_pos hk1
      _ ≤ ρ ^ k := by
          rw [div_one]
          exact pow_le_pow_of_le_one hρ0.le hρ1.le (Nat.le_mul_of_pos_left _ (by omega))
  have hint : ∀ k, ∫ x in Set.Ioc (0:ℝ) 1, Fk k x =
      (ρ : ℂ) ^ (d * k) / k * (if (((d * k : ℕ) : ℤ) - n : ℤ) = 0 then 1 else 0) := by
    intro k
    rw [← intervalIntegral.integral_of_le zero_le_one]
    simp only [hFk]
    rw [intervalIntegral.integral_const_mul, integral_exp_int]
  simp_rw [hint]
  by_cases hex : ∃ k0 : ℕ, ((d * k0 : ℕ) : ℤ) = n
  · obtain ⟨k0, hk0⟩ := hex
    rw [tsum_eq_single k0]
    · rw [if_pos (by rw [hk0]; ring), mul_one]
      unfold bb
      rw [if_pos (by rw [← hk0]; push_cast; exact Dvd.intro _ rfl)]
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hρ0.le, Complex.norm_natCast]
      rw [← hk0]
      rcases Nat.eq_zero_or_pos k0 with rfl | hk
      · simp
      have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
      have hk' : (0 : ℝ) < k0 := by exact_mod_cast hk
      push_cast
      rw [abs_of_pos (by positivity), div_le_div_iff₀ hk' (by positivity)]
      have : ρ ^ (d * k0) ≤ 1 := pow_le_one₀ hρ0.le hρ1.le
      have := mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ d * k0)
      linarith
    · intro k hk
      rw [if_neg, mul_zero]
      intro h
      apply hk
      have : ((d * k : ℕ) : ℤ) = ((d * k0 : ℕ) : ℤ) := by rw [hk0]; linarith
      have : d * k = d * k0 := by exact_mod_cast this
      exact Nat.eq_of_mul_eq_mul_left (by omega) this
  · push_neg at hex
    have : ∀ k : ℕ, (ρ : ℂ) ^ (d * k) / k *
        (if (((d * k : ℕ) : ℤ) - n : ℤ) = 0 then 1 else 0) = 0 := by
      intro k
      rw [if_neg, mul_zero]
      intro h; exact hex k (by linarith)
    simp_rw [this, tsum_zero, norm_zero]
    exact bb_nonneg _ _

end FareyAux

namespace FareyAux

open Finset Filter MeasureTheory Complex Real

noncomputable def FP (N : ℕ) : Polynomial ℂ := ∏ j ∈ Icc 1 N, Polynomial.cyclotomic j ℂ

noncomputable def UU (N : ℕ) (ρ : ℝ) (x : ℝ) : ℂ := ∑ d ∈ Icc 1 N, (cc N d : ℂ) * uu ρ d x

lemma L_eq (N : ℕ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (x : ℝ) :
    Real.log ‖(FP N).eval (zz ρ x)‖ = -(UU N ρ x).re := by
  rw [FP, log_norm_F N _ (by rw [norm_zz _ _ hρ0]; exact hρ1)]
  unfold UU uu
  rw [Complex.re_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro d _
  rw [Complex.re_ofReal_mul, Complex.neg_re, Complex.log_re]; ring

lemma measurable_UU (N : ℕ) (ρ : ℝ) : Measurable (UU N ρ) := by
  unfold UU
  apply Finset.measurable_sum; intro d _
  exact measurable_const.mul (measurable_uu ρ d)

lemma norm_UU_le (N : ℕ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (x : ℝ) :
    ‖UU N ρ x‖ ≤ ∑ d ∈ Icc 1 N, |cc N d| * (1 - ρ)⁻¹ := by
  unfold UU
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_uu_le ρ hρ0 hρ1 d (Finset.mem_Icc.mp hd).1 x) (abs_nonneg _)

lemma coef_UU (N : ℕ) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (k : ℤ) :
    ‖fourierCoeffOn zero_lt_one (UU N ρ) k‖ ≤ ∑ m ∈ Icc 1 N, |cc N m| * bb m k := by
  have heq : fourierCoeffOn zero_lt_one (UU N ρ) k =
      ∑ d ∈ Icc 1 N, (cc N d : ℂ) * fourierCoeffOn zero_lt_one (uu ρ d) k := by
    simp_rw [fourierCoeffOn_eq_integral, fourier_eq]
    simp only [sub_zero, div_one, one_smul, smul_eq_mul]
    unfold UU
    simp_rw [Finset.mul_sum]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro m _
      rw [← intervalIntegral.integral_const_mul]
      congr 1; funext x; ring
    · intro m hm
      apply intervalIntegrable_of_bdd (M := |cc N m| * (1 - ρ)⁻¹)
      · exact (Complex.measurable_exp.comp (by fun_prop)).mul (measurable_const.mul
          (measurable_uu ρ m))
      · intro x
        rw [norm_mul, norm_mul, norm_exp_re_zero _ (by simp [Complex.mul_re, Complex.mul_im]),
          one_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (norm_uu_le ρ hρ0.le hρ1 m (Finset.mem_Icc.mp hm).1 x) (abs_nonneg _)
  rw [heq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (coef_uu ρ hρ0 hρ1 d (Finset.mem_Icc.mp hd).1 k) (abs_nonneg _)

lemma J_bound (N : ℕ) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (T : ℝ) (hT : 0 < T) (B : ℝ)
    (hB : 4 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      |cc N m| * |cc N n| * ((Nat.gcd m n : ℝ) ^ 2 / (m * n)) ≤ B) :
    ∫ x in (0:ℝ)..1, Real.posLog ‖(FP N).eval (zz ρ x)‖ ≤ B / (2 * T) + T / 2 := by
  set M := ∑ d ∈ Icc 1 N, |cc N d| * (1 - ρ)⁻¹
  have hM : MemLp (UU N ρ) 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    have : IsFiniteMeasure (volume.restrict (Set.Ioc (0:ℝ) 1)) := ⟨by simp⟩
    exact MemLp.of_bound (measurable_UU N ρ).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun x => norm_UU_le N ρ hρ0.le hρ1 x)
  have hpar := parseval_gen N (fun m => |cc N m|) (fun m => abs_nonneg _) (UU N ρ) hM
    (coef_UU N ρ hρ0 hρ1)
  have hsq : IntervalIntegrable (fun x => ‖UU N ρ x‖ ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff]
    refine Measure.integrableOn_of_bounded (M := M ^ 2) ?_ ?_ ?_
    · rw [Set.uIoc]; exact measure_Ioc_lt_top.ne
    · exact ((measurable_UU N ρ).norm.pow_const 2).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_pow, abs_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_UU_le N ρ hρ0.le hρ1 x) 2
  have hcont : Continuous (fun x => Real.posLog ‖(FP N).eval (zz ρ x)‖) :=
    Real.continuous_posLog.comp (continuous_norm.comp ((FP N).continuous.comp (continuous_zz ρ)))
  have hg : IntervalIntegrable (fun x => ‖UU N ρ x‖ ^ 2 / (2 * T) + T / 2) volume 0 1 :=
    (hsq.div_const _).add intervalIntegrable_const
  calc ∫ x in (0:ℝ)..1, Real.posLog ‖(FP N).eval (zz ρ x)‖
      ≤ ∫ x in (0:ℝ)..1, (‖UU N ρ x‖ ^ 2 / (2 * T) + T / 2) := by
        apply intervalIntegral.integral_mono_on zero_le_one (hcont.intervalIntegrable 0 1) hg
        intro x _
        have h1 : Real.posLog ‖(FP N).eval (zz ρ x)‖ ≤ ‖UU N ρ x‖ := by
          show max 0 (Real.log ‖(FP N).eval (zz ρ x)‖) ≤ _
          rw [L_eq N ρ hρ0.le hρ1 x]
          apply max_le (norm_nonneg _)
          exact (neg_le_abs _).trans (Complex.abs_re_le_norm _)
        have h2 : ‖UU N ρ x‖ ≤ ‖UU N ρ x‖ ^ 2 / (2 * T) + T / 2 := by
          rw [div_add_div _ _ (by positivity) (by positivity), le_div_iff₀ (by positivity)]
          nlinarith [sq_nonneg (‖UU N ρ x‖ - T)]
        linarith
    _ = (∫ x in (0:ℝ)..1, ‖UU N ρ x‖ ^ 2) / (2 * T) + T / 2 := by
        rw [intervalIntegral.integral_add (hsq.div_const _) intervalIntegrable_const,
          intervalIntegral.integral_div, intervalIntegral.integral_const]
        simp
    _ ≤ B / (2 * T) + T / 2 := by
        gcongr
        linarith

theorem amoroso_of_moebius
    (hM : ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO atTop
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε))) :
    ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => (∫ t in (-Real.pi)..Real.pi, max 0
        (Real.log ‖(FP N).eval (Complex.exp ((t : ℂ) * Complex.I))‖)) / (2 * Real.pi))
      (fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε)) := by
  intro ε hε
  set θ : ℝ := 1 / 2 + ε with hθ
  have hθ1 : 1 / 2 < θ := by linarith
  obtain ⟨C, hC, hcc⟩ := cc_bound θ hθ1 hM
  obtain ⟨Z, hZ, hgcd⟩ := gcd_sum_bound θ hθ1
  set K : ℝ := 2 * C ^ 2 * Z + 1 / 2 with hK
  refine Asymptotics.IsBigO.of_bound K ?_
  rw [Filter.eventually_atTop]
  refine ⟨1, fun N hN => ?_⟩
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set T : ℝ := (N : ℝ) ^ θ with hT
  have hT0 : 0 < T := Real.rpow_pos_of_pos hN0 θ
  -- the Möbius sum bound
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
  have hsum2 : 4 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      |cc N m| * |cc N n| * ((Nat.gcd m n : ℝ) ^ 2 / (m * n)) ≤ 4 * (C ^ 2 * T ^ 2 * Z) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc _ ≤ ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
          C ^ 2 * T ^ 2 * ((Nat.gcd m n : ℝ) ^ 2 / ((m : ℝ) * n) ^ (1 + θ)) :=
          Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => hpair m hm n hn
      _ = C ^ 2 * T ^ 2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
          ((Nat.gcd m n : ℝ) ^ 2 / ((m : ℝ) * n) ^ (1 + θ)) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _; rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hgcd N) (by positivity)
  set B := 4 * (C ^ 2 * T ^ 2 * Z)
  have hBT : B / (2 * T) + T / 2 = K * T := by
    rw [hK]; field_simp; ring
  -- the integral over the circle of radius ρ, and the limit ρ → 1
  set J : ℝ → ℝ := fun ρ => ∫ x in (0:ℝ)..1, Real.posLog ‖(FP N).eval (zz ρ x)‖ with hJ
  have hJc : Continuous J := by
    have : Continuous (fun p : ℝ × ℝ => Real.posLog ‖(FP N).eval (zz p.1 p.2)‖) := by
      have hz : Continuous (fun p : ℝ × ℝ => zz p.1 p.2) := by unfold zz; fun_prop
      exact Real.continuous_posLog.comp (continuous_norm.comp ((FP N).continuous.comp hz))
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun ρ x => Real.posLog ‖(FP N).eval (zz ρ x)‖) this 0 1
  have hJ1 : J 1 ≤ K * T := by
    have ht : Tendsto J (nhdsWithin 1 (Set.Iio 1)) (nhds (J 1)) :=
      hJc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0:ℝ) < 1)] with ρ hρ
    rw [← hBT]
    exact J_bound N ρ hρ.1 hρ.2 T hT0 B hsum2
  -- change of variables
  have hper : Function.Periodic
      (fun t : ℝ => max 0 (Real.log ‖(FP N).eval (Complex.exp ((t : ℂ) * Complex.I))‖))
      (2 * Real.pi) := by
    intro t
    have : Complex.exp (((t + 2 * Real.pi : ℝ) : ℂ) * I) = Complex.exp ((t:ℂ) * I) := by
      rw [show ((t + 2 * Real.pi : ℝ) : ℂ) * I = (t:ℂ) * I + 2 * π * I by push_cast; ring,
        Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    beta_reduce
    rw [this]
  have hcv : (∫ t in (-Real.pi)..Real.pi, max 0
      (Real.log ‖(FP N).eval (Complex.exp ((t : ℂ) * Complex.I))‖)) = 2 * Real.pi * J 1 := by
    have e1 := hper.intervalIntegral_add_eq (-Real.pi) 0
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add] at e1
    rw [e1]
    have e2 := intervalIntegral.integral_comp_mul_left
      (fun t : ℝ => max 0 (Real.log ‖(FP N).eval (Complex.exp ((t : ℂ) * Complex.I))‖))
      (c := 2 * Real.pi) (a := 0) (b := 1) (by positivity)
    rw [mul_zero, mul_one] at e2
    have e3 : (∫ x in (0:ℝ)..1, max 0 (Real.log ‖(FP N).eval
        (Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I))‖)) = J 1 := by
      simp only [hJ]
      apply intervalIntegral.integral_congr
      intro x _
      have : Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) = zz 1 x := by
        simp only [zz, Complex.ofReal_one, one_mul]; congr 1; push_cast; ring
      beta_reduce
      rw [this]; rfl
    rw [e3] at e2
    rw [e2, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  rw [hcv]
  have hJ0 : 0 ≤ J 1 := intervalIntegral.integral_nonneg zero_le_one
    (fun x _ => Real.posLog_nonneg)
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [mul_div_cancel_left₀ _ hpi.ne', Real.norm_of_nonneg hJ0,
    Real.norm_of_nonneg (by positivity)]
  exact hJ1

end FareyAux

theorem solution :
    let F (N : ℕ) := ∏ j ∈ Finset.Icc 1 N, Polynomial.cyclotomic j ℂ
    let h (N : ℕ) : ℝ := (∫ t in (-Real.pi)..Real.pi, max 0
      (Real.log ‖(F N).eval (Complex.exp ((t : ℂ) * Complex.I))‖)) / (2 * Real.pi)
    ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO Filter.atTop h (fun N : ℕ => (N : ℝ)^(1/2+ε)) := by
  intro F h
  exact FareyAux.amoroso_of_moebius
    (moebius_summatory_rpow_bound_of_riemannHypothesis riemann_hypothesis)
