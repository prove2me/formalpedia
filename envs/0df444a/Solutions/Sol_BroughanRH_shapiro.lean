-- Prove2me | solution 1 for BroughanRH.shapiro
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T04:26:41.318505+00:00
-- url     : https://prove2.me/submissions/109ecb07-6283-4c00-bad8-164c4f16d749
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NicolasBRH_prime_ramp_bound_of_RH
import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_LandauCriterion_sum_multiplicity_div_normSq_zeros_le
import Mathlib

set_option autoImplicit false
open Finset ArithmeticFunction MeasureTheory Filter Topology

namespace NicS

noncomputable def Mfun (x : ℝ) : ℝ :=
  ((∑ n ∈ range (⌊x⌋₊+1), vonMangoldt n * max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)) / x

noncomputable def βc : ℝ := 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)

noncomputable def gfun (t : ℝ) : ℝ := (Chebyshev.psi t - t) / t^2

noncomputable def Sfun (t : ℝ) : ℝ := ∑ k ∈ Ioc 0 ⌊t⌋₊, (vonMangoldt k : ℝ) / k

lemma range_sum_eq (t : ℝ) (ht : 1 ≤ t) :
    (∑ n ∈ range (⌊t⌋₊+1), vonMangoldt n * max (t/(n:ℝ)-1) 0) =
      t * Sfun t - Chebyshev.psi t := by
  have hr : range (⌊t⌋₊+1) = Icc 0 ⌊t⌋₊ := by ext; simp
  rw [hr, ← add_sum_Ioc_eq_sum_Icc (Nat.zero_le _), Chebyshev.psi_eq_sum_Icc,
    ← add_sum_Ioc_eq_sum_Icc (Nat.zero_le _)]
  simp only [ArithmeticFunction.map_zero, zero_mul, zero_add, Sfun, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Ioc] at hk
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk.1
  have hkt : (k:ℝ) ≤ t := le_trans (by exact_mod_cast hk.2) (Nat.floor_le (by linarith))
  have hk0 : (0:ℝ) < k := by linarith
  rw [max_eq_left]
  · field_simp
  · rw [sub_nonneg, le_div_iff₀ hk0]; linarith

lemma Mfun_eq (t : ℝ) (ht : 1 ≤ t) :
    Mfun t = Sfun t - Chebyshev.psi t / t - Real.log t + 1 + Real.eulerMascheroniConstant := by
  rw [Mfun, range_sum_eq t ht]
  have : t ≠ 0 := by positivity
  field_simp
  ring

lemma psi_intervalIntegrable (a b : ℝ) : IntervalIntegrable Chebyshev.psi volume a b :=
  Chebyshev.psi_mono.intervalIntegrable

lemma gfun_intervalIntegrable (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable gfun volume a b := by
  have h0 : ∀ t ∈ Set.uIcc a b, t ≠ 0 := by
    intro t ht
    have : 0 < t := by
      rcases Set.mem_uIcc.mp ht with h | h <;> linarith [h.1]
    exact this.ne'
  have h1 : ContinuousOn (fun t : ℝ => 1 / t^2) (Set.uIcc a b) := by
    apply ContinuousOn.div continuousOn_const (continuousOn_pow 2)
    intro t ht; exact pow_ne_zero 2 (h0 t ht)
  have h2 : ContinuousOn (fun t : ℝ => t / t^2) (Set.uIcc a b) := by
    apply ContinuousOn.div continuousOn_id (continuousOn_pow 2)
    intro t ht; exact pow_ne_zero 2 (h0 t ht)
  have := ((psi_intervalIntegrable a b).mul_continuousOn h1).sub (h2.intervalIntegrable)
  refine this.congr ?_
  intro t _
  simp only [gfun]
  ring

/-- `M` is a primitive of `(ψ(t)-t)/t²`. -/
theorem integral_gfun (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, gfun t = Mfun b - Mfun a := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  -- Abel summation with f = t⁻¹
  have hA := sum_mul_eq_sub_sub_integral_mul (fun k => (vonMangoldt k : ℝ)) ha0.le hab
    (f := fun t : ℝ => t⁻¹)
    (fun t ht => differentiableAt_inv (by linarith [ht.1]))
    (by
      have : Set.EqOn (deriv fun t : ℝ => t⁻¹) (fun t => -(t^2)⁻¹) (Set.Icc a b) := by
        intro t _; exact deriv_inv
      refine (IntegrableOn.congr_fun ?_ this.symm measurableSet_Icc)
      apply ContinuousOn.integrableOn_Icc
      apply ContinuousOn.neg
      apply ContinuousOn.inv₀ (continuousOn_pow 2)
      intro t ht; exact pow_ne_zero 2 (by linarith [ht.1]))
  simp only [← Chebyshev.psi_eq_sum_Icc] at hA
  have hderiv : ∀ t ∈ Set.Ioc a b, deriv (fun t : ℝ => t⁻¹) t * Chebyshev.psi t =
      -(Chebyshev.psi t / t^2) := by
    intro t _; rw [deriv_inv]; ring
  rw [setIntegral_congr_fun measurableSet_Ioc hderiv, integral_neg,
    ← intervalIntegral.integral_of_le hab] at hA
  have hS : Sfun b = Sfun a + ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (vonMangoldt k : ℝ) / k := by
    rw [Sfun, Sfun, Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.floor_le_floor hab)]
  have hS' : ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (vonMangoldt k : ℝ) / k =
      ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, ((k:ℝ))⁻¹ * (vonMangoldt k : ℝ) := by
    apply Finset.sum_congr rfl; intro k _; ring
  have hpsi_int : IntervalIntegrable (fun t => Chebyshev.psi t / t^2) volume a b := by
    have h1 : ContinuousOn (fun t : ℝ => 1 / t^2) (Set.uIcc a b) := by
      apply ContinuousOn.div continuousOn_const (continuousOn_pow 2)
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact pow_ne_zero 2 (by linarith [ht.1])
    refine ((psi_intervalIntegrable a b).mul_continuousOn h1).congr ?_
    intro t _; simp only; ring
  have hinv_int : IntervalIntegrable (fun t : ℝ => t / t^2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_id (continuousOn_pow 2)
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact pow_ne_zero 2 (by linarith [ht.1])
  have hsplit : ∫ t in a..b, gfun t = (∫ t in a..b, Chebyshev.psi t / t^2) -
      ∫ t in a..b, t / t^2 := by
    rw [← intervalIntegral.integral_sub hpsi_int hinv_int]
    congr 1; funext t; simp only [gfun]; ring
  have hlog : ∫ t in a..b, t / t^2 = Real.log b - Real.log a := by
    have : ∫ t in a..b, t / t^2 = ∫ t in a..b, t⁻¹ := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      have : t ≠ 0 := by linarith [ht.1]
      simp only; field_simp
    rw [this, integral_inv (by
      rw [Set.uIcc_of_le hab]; intro h; linarith [h.1]),
      Real.log_div hb0.ne' ha0.ne']
  rw [hsplit, hlog, Mfun_eq b (by linarith), Mfun_eq a ha, hS, hS', hA]
  have e1 : b⁻¹ * Chebyshev.psi b = Chebyshev.psi b / b := by ring
  have e2 : a⁻¹ * Chebyshev.psi a = Chebyshev.psi a / a := by ring
  rw [e1, e2]
  ring





lemma psi_rcont (t : ℝ) (ht : 0 ≤ t) : ContinuousWithinAt Chebyshev.psi (Set.Ioi t) t := by
  have hlt : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  apply (continuousWithinAt_const (b := Chebyshev.psi t)).congr_of_eventuallyEq
  · filter_upwards [Ioo_mem_nhdsGT hlt] with u hu
    rw [Chebyshev.psi_eq_psi_coe_floor u, Chebyshev.psi_eq_psi_coe_floor t]
    congr 2
    rw [Nat.floor_eq_iff (by linarith [hu.1])]
    exact ⟨le_trans (Nat.floor_le ht) hu.1.le, hu.2⟩
  · rfl

lemma gfun_rcont (t : ℝ) (ht : 0 < t) : ContinuousWithinAt gfun (Set.Ioi t) t := by
  unfold gfun
  apply ContinuousWithinAt.div ((psi_rcont t ht.le).sub continuousWithinAt_id)
    (continuousWithinAt_id.pow 2) (pow_ne_zero 2 ht.ne')

lemma gfun_measurable : Measurable gfun := by
  unfold gfun
  have := Chebyshev.psi_mono.measurable
  fun_prop

lemma gamma_lt : Real.eulerMascheroniConstant < 0.5929 := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 32
  simp only [Real.eulerMascheroniSeq', show (32:ℕ) ≠ 0 by norm_num, if_false] at h
  have hH : ((harmonic 32 : ℚ) : ℝ) < 4.0586 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hl : Real.log (32:ℕ) = 5 * Real.log 2 := by
    rw [show ((32:ℕ):ℝ) = 2^5 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_gt_d9
  rw [hl] at h
  linarith

lemma log_four_pi_gt : 5/2 < Real.log (4 * Real.pi) := by
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  have h5 : Real.exp 5 < 149 := by
    rw [show (5:ℝ) = (5:ℕ) by norm_num, ← Real.exp_one_pow]
    have := Real.exp_one_lt_d9
    have h0 := (Real.exp_pos 1).le
    calc Real.exp 1 ^ 5 ≤ (2.7182818286:ℝ)^5 := pow_le_pow_left₀ h0 this.le 5
      _ < 149 := by norm_num
  have hsq : Real.exp (5/2) ^ 2 = Real.exp 5 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hpi := Real.pi_gt_d2
  have hpos := Real.exp_pos (5/2)
  nlinarith

lemma beta_lt : βc < 1/10 := by
  have := gamma_lt; have := log_four_pi_gt
  unfold βc; linarith



lemma M_bd (hRH : RiemannHypothesis) (t : ℝ) (ht : 2 ≤ t) :
    |Mfun t| ≤ βc * t ^ (-(1/2:ℝ)) + Real.log (2*Real.pi) / t :=
  NicolasBRH.prime_ramp_bound_of_RH hRH t ht

lemma log_two_pi_lt : Real.log (2*Real.pi) < 2 := by
  rw [Real.log_lt_iff_lt_exp (by positivity)]
  have h1 := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have := Real.pi_lt_d2
  nlinarith

lemma log_two_pi_pos : 0 < Real.log (2*Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])

/-- Integration by parts: `∫_2^n (ψ - t) = n² M(n) - 4 M(2) - ∫_2^n 2t M(t)`. -/
lemma ibp_psi (n : ℝ) (hn : 2 ≤ n) :
    ∫ t in (2:ℝ)..n, (Chebyshev.psi t - t) =
      n^2 * Mfun n - 4 * Mfun 2 - ∫ t in (2:ℝ)..n, 2 * t * Mfun t := by
  have h2 : (0:ℝ) < 2 := by norm_num
  let u : ℝ → ℝ := fun t => ∫ s in (2:ℝ)..t, gfun s
  have hgi : IntervalIntegrable gfun volume 2 n := gfun_intervalIntegrable 2 n h2 (by linarith)
  have hIcc : IntegrableOn gfun (Set.uIcc 2 n) volume := by
    rw [Set.uIcc_of_le hn]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hn).mp hgi
  have hu_cont : ContinuousOn u (Set.uIcc 2 n) :=
    intervalIntegral.continuousOn_primitive_interval hIcc
  have hu_eq : ∀ t ∈ Set.uIcc (2:ℝ) n, u t = Mfun t - Mfun 2 := by
    intro t ht; rw [Set.uIcc_of_le hn] at ht
    exact integral_gfun 2 t (by norm_num) ht.1
  have hv_cont : ContinuousOn (fun t : ℝ => t^2) (Set.uIcc 2 n) := (continuous_pow 2).continuousOn
  have hu_der : ∀ t ∈ Set.Ioo (min (2:ℝ) n) (max 2 n),
      HasDerivWithinAt u (gfun t) (Set.Ioi t) t := by
    intro t ht
    rw [min_eq_left hn, max_eq_right hn] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have h := intervalIntegral.integral_hasDerivWithinAt_right
      (gfun_intervalIntegrable 2 t h2 ht0)
      (s := Set.Ici t) (t := Set.Ioi t)
      (gfun_measurable.stronglyMeasurable.stronglyMeasurableAtFilter) (gfun_rcont t ht0)
    exact h.mono Set.Ioi_subset_Ici_self
  have hv_der : ∀ t ∈ Set.Ioo (min (2:ℝ) n) (max 2 n),
      HasDerivWithinAt (fun t : ℝ => t^2) (2 * t) (Set.Ioi t) t := by
    intro t _
    have := (hasDerivAt_pow 2 t).hasDerivWithinAt (s := Set.Ioi t)
    simpa using this
  have hvd_int : IntervalIntegrable (fun t : ℝ => 2 * t) volume 2 n :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right
    hu_cont hv_cont hu_der hv_der hgi hvd_int
  have hu2 : u 2 = 0 := intervalIntegral.integral_same
  have hun : u n = Mfun n - Mfun 2 := hu_eq n Set.right_mem_uIcc
  rw [hu2, hun] at hparts
  have hgv : IntervalIntegrable (fun t => gfun t * t^2) volume 2 n :=
    hgi.mul_continuousOn hv_cont
  have huv : IntervalIntegrable (fun t => u t * (2 * t)) volume 2 n :=
    (hu_cont.mul (continuous_const.mul continuous_id).continuousOn).intervalIntegrable
  rw [intervalIntegral.integral_add hgv huv] at hparts
  have e1 : ∫ t in (2:ℝ)..n, gfun t * t^2 = ∫ t in (2:ℝ)..n, (Chebyshev.psi t - t) := by
    apply intervalIntegral.integral_congr
    intro t ht; rw [Set.uIcc_of_le hn] at ht
    have : t ≠ 0 := by linarith [ht.1]
    simp only [gfun]; field_simp
  have e2 : ∫ t in (2:ℝ)..n, u t * (2 * t) =
      ∫ t in (2:ℝ)..n, (2 * t * Mfun t - Mfun 2 * (2 * t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp only; rw [hu_eq t ht]; ring
  have hMi : IntervalIntegrable (fun t => 2 * t * Mfun t) volume 2 n := by
    have : IntervalIntegrable (fun t => u t * (2 * t) + Mfun 2 * (2 * t)) volume 2 n :=
      huv.add (hvd_int.const_mul _)
    refine this.congr ?_
    intro t ht
    rw [Set.uIoc_of_le hn] at ht
    simp only; rw [hu_eq t (Set.Ioc_subset_Icc_self (by rwa [Set.uIcc_of_le hn] at *) |> fun h => by
      rw [Set.uIcc_of_le hn]; exact Set.Ioc_subset_Icc_self ht)]; ring
  rw [e1, e2, intervalIntegral.integral_sub hMi (hvd_int.const_mul _),
    intervalIntegral.integral_const_mul] at hparts
  have e3 : ∫ t in (2:ℝ)..n, 2 * t = n^2 - 4 := by
    rw [intervalIntegral.integral_const_mul, integral_id]; ring
  rw [e3] at hparts
  linarith

lemma abs_int_bound (hRH : RiemannHypothesis) (n : ℝ) (hn : 2 ≤ n) :
    |∫ t in (2:ℝ)..n, (Chebyshev.psi t - t)| ≤
      3 * βc * n * Real.sqrt n + 3 * Real.log (2*Real.pi) * n + 4 * βc + 2 * Real.log (2*Real.pi) := by
  have hβ := beta_lt
  have hβ0 : 0 ≤ βc := by
    have := LandauCriterion.sum_multiplicity_div_normSq_zeros_le hRH ∅ (by simp)
    simpa [βc] using this
  have hc := log_two_pi_pos
  have hn0 : 0 < n := by linarith
  have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  have hsn0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have rpow_eq : ∀ t : ℝ, 0 < t → t ^ (-(1/2:ℝ)) = 1 / Real.sqrt t := by
    intro t ht
    rw [Real.rpow_neg ht.le, Real.sqrt_eq_rpow]
    exact (one_div _).symm
  rw [ibp_psi n hn]
  -- bound each piece
  have hMn := M_bd hRH n hn
  have hM2 := M_bd hRH 2 le_rfl
  rw [rpow_eq n hn0] at hMn
  rw [rpow_eq 2 (by norm_num)] at hM2
  have hs2 : 1 ≤ Real.sqrt 2 := by rw [Real.one_le_sqrt]; norm_num
  have hM2' : |Mfun 2| ≤ βc + Real.log (2*Real.pi) / 2 := by
    have : βc * (1 / Real.sqrt 2) ≤ βc := by
      rw [mul_one_div]; exact div_le_self hβ0 hs2
    linarith
  have hpt : ∀ t ∈ Set.uIcc (2:ℝ) n, |2 * t * Mfun t| ≤ 2 * βc * Real.sqrt n + 2 * Real.log (2*Real.pi) := by
    intro t ht
    rw [Set.uIcc_of_le hn] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hM := M_bd hRH t ht.1
    rw [rpow_eq t ht0] at hM
    have hst : Real.sqrt t ≤ Real.sqrt n := Real.sqrt_le_sqrt ht.2
    have hst0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have hstt : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
    rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < 2 * t)]
    calc 2 * t * |Mfun t| ≤ 2 * t * (βc * (1 / Real.sqrt t) + Real.log (2 * Real.pi) / t) :=
          mul_le_mul_of_nonneg_left hM (by linarith)
      _ = 2 * βc * Real.sqrt t + 2 * Real.log (2*Real.pi) := by
          rw [show 2 * t * (βc * (1 / Real.sqrt t) + Real.log (2 * Real.pi) / t) =
            2 * (Real.sqrt t * Real.sqrt t) * (βc * (1 / Real.sqrt t)) + 2 * Real.log (2 * Real.pi) * (t / t) by
              rw [hstt]; ring]
          rw [div_self (ne_of_gt ht0)]
          field_simp
      _ ≤ 2 * βc * Real.sqrt n + 2 * Real.log (2*Real.pi) := by nlinarith
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := (2:ℝ)) (b := n)
    (f := fun t => 2 * t * Mfun t) (C := 2 * βc * Real.sqrt n + 2 * Real.log (2*Real.pi))
    (fun t ht => by
      rw [Real.norm_eq_abs]
      exact hpt t (Set.uIoc_subset_uIcc ht))
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ n - 2)] at hint
  have hnM : |n^2 * Mfun n| ≤ βc * n * Real.sqrt n + Real.log (2*Real.pi) * n := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc n^2 * |Mfun n| ≤ n^2 * (βc * (1 / Real.sqrt n) + Real.log (2 * Real.pi) / n) :=
          mul_le_mul_of_nonneg_left hMn (by positivity)
      _ = βc * n * Real.sqrt n + Real.log (2*Real.pi) * n := by
          rw [show n^2 * (βc * (1 / Real.sqrt n) + Real.log (2 * Real.pi) / n) =
            n * (Real.sqrt n * Real.sqrt n) * (βc * (1 / Real.sqrt n)) + Real.log (2 * Real.pi) * n * (n / n) by
              rw [hsn]; ring]
          rw [div_self (ne_of_gt hn0)]
          field_simp
  have h4 : |4 * Mfun 2| ≤ 4 * βc + 2 * Real.log (2*Real.pi) := by
    rw [abs_mul]; norm_num; linarith
  have hsnn : 0 ≤ βc * Real.sqrt n := by positivity
  calc |n^2 * Mfun n - 4 * Mfun 2 - ∫ t in (2:ℝ)..n, 2 * t * Mfun t|
      ≤ |n^2 * Mfun n| + |4 * Mfun 2| + |∫ t in (2:ℝ)..n, 2 * t * Mfun t| := by
        have := abs_sub (n^2 * Mfun n - 4 * Mfun 2) (∫ t in (2:ℝ)..n, 2 * t * Mfun t)
        have := abs_sub (n^2 * Mfun n) (4 * Mfun 2)
        linarith
    _ ≤ (βc * n * Real.sqrt n + Real.log (2*Real.pi) * n) + (4 * βc + 2 * Real.log (2*Real.pi)) +
          (2 * βc * Real.sqrt n + 2 * Real.log (2*Real.pi)) * (n - 2) := by
        gcongr
    _ ≤ 3 * βc * n * Real.sqrt n + 3 * Real.log (2*Real.pi) * n + 4 * βc +
          2 * Real.log (2*Real.pi) := by nlinarith

end NicS

namespace NicS

lemma int_psi_step (j : ℕ) : ∫ t in (j:ℝ)..((j:ℝ)+1), Chebyshev.psi t = Chebyshev.psi j := by
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (a := (j:ℝ)) (b := (j:ℝ)+1)
    (f := fun t => Chebyshev.psi j * t) (f' := Chebyshev.psi) (by linarith)
    ((continuous_const.mul continuous_id).continuousOn)
    (by
      intro x hx
      have hfl : ⌊x⌋₊ = j := by
        rw [Nat.floor_eq_iff (by linarith [hx.1, (Nat.cast_nonneg j : (0:ℝ) ≤ j)])]
        exact ⟨hx.1.le, hx.2⟩
      have hpx : Chebyshev.psi x = Chebyshev.psi j := by
        rw [Chebyshev.psi_eq_psi_coe_floor x, hfl]
      rw [hpx]
      have := ((hasDerivAt_id x).const_mul (Chebyshev.psi j)).hasDerivWithinAt (s := Set.Ioi x)
      simpa using this)
    (psi_intervalIntegrable _ _)
  rw [h]; ring

lemma sum_psi_eq_int (n : ℕ) (hn : 2 ≤ n) :
    ∑ j ∈ Finset.Ico 1 n, Chebyshev.psi j = ∫ t in (2:ℝ)..n, Chebyshev.psi t := by
  induction n, hn using Nat.le_induction with
  | base => simp [Chebyshev.psi_one]
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top (by omega), ih]
    push_cast
    rw [← intervalIntegral.integral_add_adjacent_intervals (a := (2:ℝ)) (b := (n:ℝ)) (c := (n:ℝ)+1)
      (psi_intervalIntegrable _ _) (psi_intervalIntegrable _ _), int_psi_step n]

lemma log_delta (n : ℕ) :
    Real.log ((∏ j ∈ Finset.Ico 1 n, (Finset.Icc 1 j).lcm id : ℕ) : ℝ) =
      ∑ j ∈ Finset.Ico 1 n, Chebyshev.psi j := by
  rw [Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro j _
    rw [Chebyshev.psi_eq_log_lcmUpto]; rfl
  · intro j _
    have := Nat.lcmUpto_pos j
    simp only [Nat.lcmUpto] at this
    exact_mod_cast this.ne'

theorem shapiro_of_RH (hRH : RiemannHypothesis) :
    let δ (n : ℕ) : ℕ := ∏ j ∈ Finset.Ico 1 n, (Finset.Icc 1 j).lcm id
    ∀ n : ℕ, 1 ≤ n → ((harmonic (δ n) : ℝ) - (n : ℝ)^2/2)^2 < 36*(n : ℝ)^3 := by
  intro δ n hn
  rcases (show n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with h | h | h | h
  · subst h
    have : δ 1 = 1 := by decide
    rw [this]; norm_num [harmonic]
  · subst h
    have : δ 2 = 1 := by decide
    rw [this]; norm_num [harmonic]
  · subst h
    have : δ 3 = 2 := by decide
    rw [this]; norm_num [harmonic, Finset.sum_range_succ]
  -- main case
  set N : ℝ := (n:ℝ) with hN
  have hN4 : (4:ℝ) ≤ N := by rw [hN]; exact_mod_cast h
  have hN0 : 0 < N := by linarith
  have hδpos : 0 < δ n := by
    apply Finset.prod_pos
    intro j _
    have := Nat.lcmUpto_pos j
    simpa [Nat.lcmUpto] using this
  have hlogδ : Real.log (δ n) = (∫ t in (2:ℝ)..N, (Chebyshev.psi t - t)) + (N^2 - 4)/2 := by
    have h1 := log_delta n
    rw [sum_psi_eq_int n (by omega)] at h1
    simp only [δ]
    rw [h1, intervalIntegral.integral_sub (psi_intervalIntegrable _ _)
      (intervalIntegral.intervalIntegrable_id (a := 2) (b := N)), integral_id]
    ring
  have hH1 : Real.log (δ n) ≤ (harmonic (δ n) : ℝ) := by
    have := log_add_one_le_harmonic (δ n)
    have h2 : Real.log (δ n) ≤ Real.log ((δ n : ℕ) + 1 : ℕ) := by
      apply Real.log_le_log (by exact_mod_cast hδpos); push_cast; linarith
    linarith
  have hH2 : (harmonic (δ n) : ℝ) ≤ 1 + Real.log (δ n) := harmonic_le_one_add_log _
  have hI := abs_int_bound hRH N (by linarith)
  have hβ := beta_lt
  have hc := log_two_pi_lt
  have hc0 := log_two_pi_pos
  have hβ0 : 0 ≤ βc := by
    have := LandauCriterion.sum_multiplicity_div_normSq_zeros_le hRH ∅ (by simp)
    simpa [βc] using this
  have hs : 2 ≤ Real.sqrt N := by
    rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hN4
  have hss : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  set I := ∫ t in (2:ℝ)..N, (Chebyshev.psi t - t)
  have hX : |(harmonic (δ n) : ℝ) - N^2/2| ≤ 2 + |I| := by
    have e : (harmonic (δ n) : ℝ) - N^2/2 = ((harmonic (δ n) : ℝ) - Real.log (δ n)) + I - 2 := by
      rw [hlogδ]; ring
    rw [e, abs_le]
    constructor <;> cases abs_le.mp (le_refl |I|) <;> nlinarith [abs_nonneg I, le_abs_self I, neg_abs_le I]
  have hb1 : |I| ≤ 0.3 * N * Real.sqrt N + 6 * N + 4.4 := by
    have h3 : 3 * βc * N * Real.sqrt N ≤ 0.3 * N * Real.sqrt N := by
      have : 0 ≤ N * Real.sqrt N := by positivity
      nlinarith
    nlinarith
  have hfin : |(harmonic (δ n) : ℝ) - N^2/2| < 6 * N * Real.sqrt N := by
    have : 8 ≤ N * Real.sqrt N := by nlinarith
    nlinarith
  have hpos : 0 ≤ 6 * N * Real.sqrt N := by positivity
  have hsq : (6 * N * Real.sqrt N)^2 = 36 * N^3 := by
    have : (6 * N * Real.sqrt N)^2 = 36 * N^2 * (Real.sqrt N * Real.sqrt N) := by ring
    rw [this, hss]; ring
  rw [← hsq]
  have := sq_lt_sq' (by linarith [neg_abs_le ((harmonic (δ n) : ℝ) - N^2/2)]) (lt_of_le_of_lt (le_abs_self _) hfin)
  exact this

end NicS

theorem solution :
    let δ (n : ℕ) : ℕ := ∏ j ∈ Finset.Ico 1 n, (Finset.Icc 1 j).lcm id
    ∀ n : ℕ, 1 ≤ n → ((harmonic (δ n) : ℝ) - (n : ℝ)^2/2)^2 < 36*(n : ℝ)^3 :=
  NicS.shapiro_of_RH riemann_hypothesis
