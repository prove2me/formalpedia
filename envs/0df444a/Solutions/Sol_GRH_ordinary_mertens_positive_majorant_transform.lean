-- Prove2me | solution 1 for GRH.ordinary_mertens_positive_majorant_transform
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T20:55:45.03148+00:00
-- url     : https://prove2.me/submissions/04b2d560-4db9-4612-b41e-91f10826a9ee

import Definitions.Def_GRH_OneSidedMoebius
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp

open Complex MeasureTheory Filter Set Finset GRH.OneSidedMoebius

private theorem mertens_abs (n : ℕ) : |mertens n| ≤ n := by
  calc
    _ ≤ ∑ k ∈ Icc 1 n, |(ArithmeticFunction.moebius k : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Icc 1 n, (1:ℝ) := sum_le_sum fun k _ => by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=k)
    _ = _ := by simp

private theorem mertens_coe (n : ℕ) :
    (mertens n : ℂ) = ∑ k ∈ Icc 1 n, (ArithmeticFunction.moebius k : ℂ) := by
  unfold mertens
  push_cast
  rfl

private theorem measurableM : Measurable (fun x : ℝ => mertens ⌊x⌋₊) :=
  (measurable_of_countable mertens).comp Nat.measurable_floor

private theorem boundM {x : ℝ} (hx : 0 ≤ x) : |mertens ⌊x⌋₊| ≤ x :=
  (mertens_abs _).trans (Nat.floor_le hx)

private theorem integrableM {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (mertens ⌊x⌋₊ : ℂ) * (x : ℂ)^(-s-1)) (Set.Ioi 1) := by
  have hI : IntegrableOn (fun x : ℝ => x^(-s.re)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  refine hI.mono' (((Complex.measurable_ofReal.comp measurableM).mul
    (Complex.measurable_ofReal.pow_const _)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  have e : (-s-1).re = -s.re + (-1) := by simp [sub_eq_add_neg]
  rw [e, Real.rpow_add hx0, Real.rpow_neg_one]
  calc
    _ ≤ x * (x^(-s.re)*x⁻¹) := mul_le_mul_of_nonneg_right (boundM hx0.le) (by positivity)
    _ = _ := by field_simp

private theorem mertens_transform {s : ℂ} (hs : 1 < s.re) :
    transform (fun x => mertens ⌊x⌋₊) s = (s * riemannZeta s)⁻¹ := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.moebius n : ℂ)
  have hO : Asymptotics.IsBigO atTop (fun n => ∑ k ∈ Icc 1 n, f k)
      (fun n : ℕ => (n:ℝ)^(1:ℝ)) := by
    apply Asymptotics.isBigO_of_le
    intro n
    simp only [f,← mertens_coe, Complex.norm_real, Real.norm_eq_abs, Real.rpow_one,
      abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) n)]
    exact mertens_abs n
  have he := LSeries_eq_mul_integral f zero_le_one hs
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs) hO
  have hm : LSeries f s = s * transform (fun x => mertens ⌊x⌋₊) s := by
    simpa only [transform, mertens_coe, neg_add_rev, sub_eq_add_neg, add_comm (-1:ℂ) (-s), f] using he
  have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at h
  change riemannZeta s * LSeries f s = 1 at h
  rw [hm] at h
  apply eq_inv_of_mul_eq_one_left
  linear_combination h

theorem solution (D θ : ℝ) (hD : 0 ≤ D) (hθ : θ < 1) :
    Measurable (majorant D θ) ∧
    (∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => majorant D θ x * x^(-σ-1)) (Set.Ioi 1)) ∧
    ∀ s : ℂ, 1 < s.re → transform (majorant D θ) s =
      (D : ℂ)/(s-θ) - (s*riemannZeta s)⁻¹ := by
  have hA : Measurable (majorant D θ) :=
    (measurable_const.mul (measurable_id.pow_const θ)).sub measurableM
  refine ⟨hA,?_,?_⟩
  · intro σ hσ
    have hi : IntegrableOn (fun x : ℝ => (D+1)*x^(-σ)) (Set.Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
    refine hi.mono' ((hA.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 < x := hx
    have hx0 := zero_lt_one.trans hx1
    have hp : x^θ ≤ x := by simpa using Real.rpow_le_rpow_of_exponent_le hx1.le hθ.le
    have hmaj : |majorant D θ x| ≤ (D+1)*x := by
      apply (abs_sub _ _).trans
      rw [abs_of_nonneg (mul_nonneg hD (Real.rpow_nonneg hx0.le _))]
      nlinarith only [boundM hx0.le, mul_le_mul_of_nonneg_left hp hD]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    rw [show -σ-1 = -σ+(-1) by ring, Real.rpow_add hx0, Real.rpow_neg_one]
    calc
      _ ≤ ((D+1)*x)*(x^(-σ)*x⁻¹) := mul_le_mul_of_nonneg_right hmaj (by positivity)
      _ = _ := by field_simp
  · intro s hs
    have hp : IntegrableOn (fun x : ℝ => (D:ℂ)*(x:ℂ)^((θ:ℂ)-s-1)) (Set.Ioi 1) :=
      (integrableOn_Ioi_cpow_of_lt (by simp;linarith) zero_lt_one).const_mul _
    have hpoint : ∀ x ∈ Set.Ioi (1:ℝ), (majorant D θ x : ℂ)*(x:ℂ)^(-s-1) =
        (D:ℂ)*(x:ℂ)^((θ:ℂ)-s-1) - (mertens ⌊x⌋₊:ℂ)*(x:ℂ)^(-s-1) := by
      intro x hx
      have hx0 : 0 < x := zero_lt_one.trans hx
      have hxc : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0.ne'
      rw [majorant, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_cpow hx0.le, show (θ:ℂ)-s-1 = θ+(-s-1) by ring, cpow_add _ _ hxc]
      ring
    unfold transform
    rw [setIntegral_congr_fun measurableSet_Ioi hpoint, integral_sub hp (integrableM hs),
      integral_const_mul, integral_Ioi_cpow_of_lt (by simp;linarith) zero_lt_one]
    change _ - transform (fun x => mertens ⌊x⌋₊) s = _
    rw [mertens_transform hs]
    simp only [ofReal_one,one_cpow]
    rw [show (θ:ℂ)-s-1+1 = -(s-θ) by ring]
    simp [div_eq_mul_inv]
    rw [show (θ:ℂ)-s = -(s-θ) by ring, inv_neg]
    ring
