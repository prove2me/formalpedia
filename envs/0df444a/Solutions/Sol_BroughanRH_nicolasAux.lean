-- Prove2me | solution 1 for BroughanRH.nicolasAux
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T20:07:56.222813+00:00
-- url     : https://prove2.me/submissions/f37c0810-7d20-4091-bcea-990f24b34b07
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ArtinPrimitiveRoots_mertens_product
import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_LandauCriterion_sum_multiplicity_div_normSq_zeros_le
import Theorems.Thm_MasulloRH_prime_ramp_integrated_explicit_formula
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_lower
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_low
import Mathlib

set_option autoImplicit false
open Finset ArithmeticFunction MeasureTheory Filter Topology



namespace NicCore

noncomputable def Mfun (x : ℝ) : ℝ :=
  ((∑ n ∈ range (⌊x⌋₊+1), vonMangoldt n * max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)) / x

noncomputable def βc : ℝ := 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)

noncomputable def Kt (x : ℝ) (ρ : MasulloRH.ZetaZerosInTraceStrip (1/2)) : ℂ :=
  (analyticOrderNatAt riemannZeta ρ.val : ℂ) * (x:ℂ)^(ρ.val-1)/(ρ.val*(ρ.val-1))

lemma re_half (hRH : RiemannHypothesis) (ρ : MasulloRH.ZetaZerosInTraceStrip (1/2)) :
    ρ.val.re = 1/2 := by
  obtain ⟨hz, h0, h1, -⟩ := ρ.property
  apply hRH ρ.val hz
  · rintro ⟨n, hn⟩
    have : ρ.val.re = -2 * ((n:ℝ) + 1) := by rw [hn]; simp
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · intro h; rw [h] at h1; simp at h1

lemma norm_Kt (hRH : RiemannHypothesis) (x : ℝ) (hx : 0 < x)
    (ρ : MasulloRH.ZetaZerosInTraceStrip (1/2)) :
    ‖Kt x ρ‖ = x ^ (-(1/2:ℝ)) * ((analyticOrderNatAt riemannZeta ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by
  have hre := re_half hRH ρ
  have hne : ρ.val ≠ 0 := by
    intro h; rw [h] at hre; simp at hre
  have hn1 : ‖ρ.val - 1‖ = ‖ρ.val‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply, hre]
    ring
  rw [Kt, norm_div, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, hn1]
  have : (ρ.val - 1).re = -(1/2) := by simp [hre]; norm_num
  rw [this]
  simp only [Complex.norm_natCast]
  have hp : 0 < ‖ρ.val‖ := norm_pos_iff.mpr hne
  field_simp

lemma summable_Kt (x : ℝ) (hx : 1 ≤ x) : Summable (fun ρ => ‖Kt x ρ‖) := by
  have h := @MasulloRH.prime_ramp_integrated_explicit_formula
  dsimp only at h
  exact h.1 x hx

lemma tsum_norm_Kt_le (hRH : RiemannHypothesis) (x : ℝ) (hx : 1 ≤ x) :
    ∑' ρ, ‖Kt x ρ‖ ≤ βc * x ^ (-(1/2:ℝ)) := by
  have hx0 : 0 < x := by linarith
  apply (summable_Kt x hx).tsum_le_of_sum_le
  intro s
  simp_rw [norm_Kt hRH x hx0]
  rw [← Finset.mul_sum, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hL := LandauCriterion.sum_multiplicity_div_normSq_zeros_le hRH
    (s.map ⟨Subtype.val, Subtype.val_injective⟩) (by
      intro ρ hρ
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hρ
      obtain ⟨r, -, rfl⟩ := hρ
      exact ⟨r.property.1, r.property.2.1⟩)
  rw [Finset.sum_map] at hL
  simpa [βc] using hL

lemma c_nonneg (t : ℝ) (ht : 2 ≤ t) :
    0 ≤ Real.log (2*Real.pi) + (1/2) * Real.log (1 - t^(-2:ℝ)) := by
  have ht0 : 0 < t := by linarith
  have h1 : t^(-2:ℝ) ≤ 1/4 := by
    rw [Real.rpow_neg ht0.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  have h2 : 0 < t^(-2:ℝ) := Real.rpow_pos_of_pos ht0 _
  have h3 : Real.log (3/4) ≤ Real.log (1 - t^(-2:ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith)
  have h4 : Real.log 6 ≤ Real.log (2*Real.pi) :=
    Real.log_le_log (by norm_num) (by linarith [Real.pi_gt_three])
  have h5 : Real.log (3/4) = Real.log 3 - Real.log 4 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
  have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h7 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  have h8 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h9 := Real.log_two_gt_d9
  nlinarith

/-- Under RH, the increments of Masullo's corrected prime ramp `M = G/x` are bounded by
`β (a^{-1/2} + b^{-1/2})`. -/
theorem M_sub_le (hRH : RiemannHypothesis) (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    Mfun b - Mfun a ≤ βc * (a ^ (-(1/2:ℝ)) + b ^ (-(1/2:ℝ))) := by
  have h := @MasulloRH.prime_ramp_integrated_explicit_formula
  dsimp only at h
  have hE := h.2 a b ha hab
  have hsa : Summable (fun ρ => Kt a ρ) := (summable_Kt a (by linarith)).of_norm
  have hsb : Summable (fun ρ => Kt b ρ) := (summable_Kt b (by linarith)).of_norm
  have hsplit : (∑' ρ : MasulloRH.ZetaZerosInTraceStrip (1/2),
      ((analyticOrderNatAt riemannZeta ρ.val : ℂ) * (b:ℂ)^(ρ.val-1)/(ρ.val*(ρ.val-1)) -
        (analyticOrderNatAt riemannZeta ρ.val : ℂ) * (a:ℂ)^(ρ.val-1)/(ρ.val*(ρ.val-1)))) =
      (∑' ρ, Kt b ρ) - ∑' ρ, Kt a ρ := (hsb.tsum_sub hsa)
  rw [hsplit] at hE
  have hint : (∫ t in a..b, ((Real.log (2*Real.pi)+(1/2)*Real.log (1-t^(-2:ℝ)):ℝ):ℂ)/(t:ℂ)^2) =
      ((∫ t in a..b, (Real.log (2*Real.pi)+(1/2)*Real.log (1-t^(-2:ℝ)))/t^2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    congr 1; funext t; push_cast; ring
  rw [hint] at hE
  have hpos : 0 ≤ ∫ t in a..b, (Real.log (2*Real.pi)+(1/2)*Real.log (1-t^(-2:ℝ)))/t^2 := by
    apply intervalIntegral.integral_nonneg hab
    intro t ht
    exact div_nonneg (c_nonneg t (by linarith [ht.1])) (by positivity)
  have hre := congrArg Complex.re hE
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hre
  have hMb : Mfun b = ((∑ n ∈ range (⌊b⌋₊+1), vonMangoldt n * max (b/(n:ℝ)-1) 0) -
      b*(Real.log b-1-Real.eulerMascheroniConstant)) / b := rfl
  have hMa : Mfun a = ((∑ n ∈ range (⌊a⌋₊+1), vonMangoldt n * max (a/(n:ℝ)-1) 0) -
      a*(Real.log a-1-Real.eulerMascheroniConstant)) / a := rfl
  have hnb : -(∑' ρ, Kt b ρ).re ≤ βc * b ^ (-(1/2:ℝ)) := by
    have := Complex.abs_re_le_norm (∑' ρ, Kt b ρ)
    have h2 := norm_tsum_le_tsum_norm (summable_Kt b (by linarith))
    have h3 := tsum_norm_Kt_le hRH b (by linarith)
    have := neg_abs_le (∑' ρ, Kt b ρ).re
    linarith
  have hna : (∑' ρ, Kt a ρ).re ≤ βc * a ^ (-(1/2:ℝ)) := by
    have := Complex.abs_re_le_norm (∑' ρ, Kt a ρ)
    have h2 := norm_tsum_le_tsum_norm (summable_Kt a (by linarith))
    have h3 := tsum_norm_Kt_le hRH a (by linarith)
    have := le_abs_self (∑' ρ, Kt a ρ).re
    linarith
  rw [hMb, hMa]

  linarith

end NicCore




namespace NicCore


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

end NicCore




namespace NicCore


noncomputable def vfun (t : ℝ) : ℝ := 1 / Real.log t + 1 / (Real.log t)^2

noncomputable def vdfun (t : ℝ) : ℝ := -(1 / (t * (Real.log t)^2)) - 2 / (t * (Real.log t)^3)

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

lemma vfun_hasDerivAt (t : ℝ) (ht : 1 < t) : HasDerivAt vfun (vdfun t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have h1 := Real.hasDerivAt_log ht0
  have hA := (hasDerivAt_const t (1:ℝ)).div h1 hl
  have hB := (hasDerivAt_const t (1:ℝ)).div (h1.pow 2) (pow_ne_zero 2 hl)
  have := hA.add hB
  have key : vdfun t = (0 * Real.log t - 1 * t⁻¹) / Real.log t ^ 2 +
      (0 * (Real.log t)^2 - 1 * ((2:ℕ) * Real.log t ^ (2 - 1) * t⁻¹)) / ((Real.log t)^2) ^ 2 := by
    unfold vdfun; field_simp; ring
  rw [key]
  exact this

lemma vdfun_continuousOn (a b : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    ContinuousOn vdfun (Set.Icc a b) := by
  have hpos : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht => by linarith [ht.1]
  have hlog : ContinuousOn Real.log (Set.Icc a b) :=
    Real.continuousOn_log.mono (fun t ht => (hpos t ht).ne')
  have hl0 : ∀ t ∈ Set.Icc a b, Real.log t ≠ 0 := fun t ht =>
    (Real.log_pos (by linarith [ht.1])).ne'
  unfold vdfun
  apply ContinuousOn.sub
  · apply ContinuousOn.neg
    apply ContinuousOn.div continuousOn_const (continuousOn_id.mul (hlog.pow 2))
    intro t ht; exact mul_ne_zero (hpos t ht).ne' (pow_ne_zero 2 (hl0 t ht))
  · apply ContinuousOn.div continuousOn_const (continuousOn_id.mul (hlog.pow 3))
    intro t ht; exact mul_ne_zero (hpos t ht).ne' (pow_ne_zero 3 (hl0 t ht))

lemma vdfun_nonpos (t : ℝ) (ht : 1 < t) : vdfun t ≤ 0 := by
  have hl := Real.log_pos ht
  have ht0 : 0 < t := by linarith
  unfold vdfun
  have h1 : 0 < 1 / (t * Real.log t ^ 2) := by positivity
  have h2 : 0 < 2 / (t * Real.log t ^ 3) := by positivity
  linarith

/-- Integration by parts: if the increments of a primitive `u` of `g` on `[x,y]` are bounded
by `B ≥ 0`, then `∫_x^y g v ≤ B v(x)` for the decreasing weight `v`. -/
theorem ibp_bound (x y : ℝ) (hx : 2 ≤ x) (hxy : x ≤ y)
    (hgi : ∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable gfun volume a b)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ t, x ≤ t → t ≤ y → ∫ s in x..t, gfun s ≤ B) :
    ∫ t in x..y, gfun t * vfun t ≤ B * vfun x := by
  have hx0 : 0 < x := by linarith
  let u : ℝ → ℝ := fun t => ∫ s in x..t, gfun s
  have hgxy := hgi x y hx0 (by linarith)
  have hIcc : IntegrableOn gfun (Set.uIcc x y) volume := by
    rw [Set.uIcc_of_le hxy]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hxy).mp hgxy
  have hu_cont : ContinuousOn u (Set.uIcc x y) :=
    intervalIntegral.continuousOn_primitive_interval hIcc
  have hv_cont : ContinuousOn vfun (Set.uIcc x y) := by
    intro t ht
    rw [Set.uIcc_of_le hxy] at ht
    exact (vfun_hasDerivAt t (by linarith [ht.1])).continuousAt.continuousWithinAt
  have hu_der : ∀ t ∈ Set.Ioo (min x y) (max x y),
      HasDerivWithinAt u (gfun t) (Set.Ioi t) t := by
    intro t ht
    rw [min_eq_left hxy, max_eq_right hxy] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have h := intervalIntegral.integral_hasDerivWithinAt_right (hgi x t hx0 ht0)
      (s := Set.Ici t) (t := Set.Ioi t)
      (gfun_measurable.stronglyMeasurable.stronglyMeasurableAtFilter) (gfun_rcont t ht0)
    exact h.mono Set.Ioi_subset_Ici_self
  have hv_der : ∀ t ∈ Set.Ioo (min x y) (max x y),
      HasDerivWithinAt vfun (vdfun t) (Set.Ioi t) t := by
    intro t ht
    rw [min_eq_left hxy, max_eq_right hxy] at ht
    exact (vfun_hasDerivAt t (by linarith [ht.1])).hasDerivWithinAt
  have hvd_int : IntervalIntegrable vdfun volume x y :=
    (vdfun_continuousOn x y (by linarith) hxy).intervalIntegrable_of_Icc hxy
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right
    hu_cont hv_cont hu_der hv_der hgxy hvd_int
  have hux : u x = 0 := intervalIntegral.integral_same
  rw [hux, zero_mul, sub_zero] at hparts
  have hgv : IntervalIntegrable (fun t => gfun t * vfun t) volume x y :=
    hgxy.mul_continuousOn hv_cont
  have huvd_cont : ContinuousOn (fun t => u t * vdfun t) (Set.Icc x y) := by
    apply ContinuousOn.mul
    · rw [← Set.uIcc_of_le hxy]; exact hu_cont
    · exact vdfun_continuousOn x y (by linarith) hxy
  have huvd : IntervalIntegrable (fun t => u t * vdfun t) volume x y :=
    huvd_cont.intervalIntegrable_of_Icc hxy
  rw [intervalIntegral.integral_add hgv huvd] at hparts
  -- bound ∫ u * vd from below by B * ∫ vd
  have hlow : ∫ t in x..y, B * vdfun t ≤ ∫ t in x..y, u t * vdfun t := by
    apply intervalIntegral.integral_mono_on hxy (hvd_int.const_mul B) huvd
    intro t ht
    have h1 := hB t ht.1 ht.2
    have h2 := vdfun_nonpos t (by linarith [ht.1])
    nlinarith
  have hvd_eq : ∫ t in x..y, vdfun t = vfun y - vfun x := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le hxy] at ht
      exact vfun_hasDerivAt t (by linarith [ht.1])
    · exact hvd_int
  rw [intervalIntegral.integral_const_mul, hvd_eq] at hlow
  have huy : u y ≤ B := hB y hxy le_rfl
  have hvy : 0 ≤ vfun y := by
    have := Real.log_pos (show (1:ℝ) < y by linarith)
    unfold vfun; positivity
  have : u y * vfun y ≤ B * vfun y := mul_le_mul_of_nonneg_right huy hvy
  nlinarith

end NicCore




namespace NicCore



noncomputable def wfun (t : ℝ) : ℝ := (Real.log t + 1) / (t * Real.log t)^2

/-- `L(x) = ∑_{p ≤ x} -log(1-1/p)`. -/
noncomputable def Lfun (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime, -Real.log (1 - 1/(p:ℝ))

lemma primes_set_eq (y : ℝ) :
    (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime = (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h2.two_le, by omega⟩, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

lemma one_sub_inv_pos (p : ℕ) (hp : p.Prime) : 0 < 1 - 1/(p:ℝ) := by
  have : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [sub_pos, div_lt_one (by linarith)]; linarith

lemma log_mertensProduct (y : ℝ) :
    Real.log (ArtinPrimitiveRoots.mertensProduct y) = -Lfun y := by
  rw [ArtinPrimitiveRoots.mertensProduct, primes_set_eq, Real.log_prod, Lfun,
    Finset.sum_neg_distrib, neg_neg]
  intro p hp
  exact (one_sub_inv_pos p (Finset.mem_filter.mp hp).2).ne'

lemma mertensProduct_pos (y : ℝ) : 0 < ArtinPrimitiveRoots.mertensProduct y := by
  apply Finset.prod_pos
  intro p hp
  exact one_sub_inv_pos p (Finset.mem_filter.mp hp).2

/-- Mertens: `L(y) - log log y → γ`. -/
lemma tendsto_L_sub : Tendsto (fun y => Lfun y - Real.log (Real.log y)) atTop
    (𝓝 Real.eulerMascheroniConstant) := by
  have h := ArtinPrimitiveRoots.mertens_product.log (Real.exp_pos _).ne'
  rw [Real.log_exp] at h
  have h2 := h.neg
  rw [neg_neg] at h2
  apply h2.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with y hy
  have hl : 0 < Real.log y := Real.log_pos hy
  rw [Real.log_mul (mertensProduct_pos y).ne' hl.ne', log_mertensProduct]
  ring

/-- Telescoping bound. -/
lemma tele (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    ∑ n ∈ Finset.Ioc N M, 1 / ((n:ℝ) * ((n:ℝ) - 1)) = 1 / (N:ℝ) - 1 / (M:ℝ) := by
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
    rw [Finset.sum_Ioc_succ_top (by omega), ih]
    have hM : (1:ℝ) ≤ M := by exact_mod_cast le_trans hN hNM
    have hM0 : (M:ℝ) ≠ 0 := by linarith
    have hM1 : (M:ℝ) + 1 ≠ 0 := by linarith
    push_cast
    rw [show ((M:ℝ) + 1 - 1) = M by ring]
    field_simp
    ring

lemma L_sub_le (x y : ℝ) (hx : 2 ≤ x) (hxy : x ≤ y) :
    Lfun y - Lfun x ≤ (∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, 1/(p:ℝ)) + 1/(⌊x⌋₊:ℝ) := by
  have hfx : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hfxy : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hxy
  have hU : Finset.Icc 2 ⌊y⌋₊ = Finset.Icc 2 ⌊x⌋₊ ∪ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ := by
    ext n; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hD : Disjoint (Finset.Icc 2 ⌊x⌋₊) (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊) := by
    rw [Finset.disjoint_left]; intro n h1 h2
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2; omega
  have hLy : Lfun y = Lfun x + ∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
      -Real.log (1 - 1/(p:ℝ)) := by
    rw [Lfun, Lfun, hU, Finset.filter_union, Finset.sum_union (Finset.disjoint_filter_filter hD)]
  rw [hLy, add_sub_cancel_left]
  have hterm : ∀ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
      -Real.log (1 - 1/(p:ℝ)) ≤ 1/(p:ℝ) + 1/((p:ℝ) * ((p:ℝ) - 1)) := by
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    have h2 : (2:ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hl := Real.one_sub_inv_le_log_of_pos (one_sub_inv_pos p hpp)
    have : 1 - (1 - 1/(p:ℝ))⁻¹ = -(1/(p:ℝ) + 1/((p:ℝ) * ((p:ℝ) - 1))) := by
      have : (p:ℝ) - 1 ≠ 0 := by linarith
      field_simp
      ring
    linarith
  calc _ ≤ ∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
        (1/(p:ℝ) + 1/((p:ℝ) * ((p:ℝ) - 1))) := Finset.sum_le_sum hterm
    _ = (∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, 1/(p:ℝ)) +
        ∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, 1/((p:ℝ) * ((p:ℝ) - 1)) :=
          Finset.sum_add_distrib
    _ ≤ _ := by
      gcongr
      calc _ ≤ ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, 1/((n:ℝ) * ((n:ℝ) - 1)) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro n hn _
            have : (1:ℝ) ≤ n := by
              have := (Finset.mem_Ioc.mp hn).1; exact_mod_cast (by omega : 1 ≤ n)
            apply div_nonneg zero_le_one
            nlinarith
        _ = 1 / (⌊x⌋₊:ℝ) - 1 / (⌊y⌋₊:ℝ) := tele _ _ (by omega) hfxy
        _ ≤ 1 / (⌊x⌋₊:ℝ) := by
            have : (0:ℝ) ≤ 1 / (⌊y⌋₊:ℝ) := by positivity
            linarith

lemma hasDerivAt_f (t : ℝ) (ht : 1 < t) :
    HasDerivAt (fun t : ℝ => (t * Real.log t)⁻¹) (-wfun t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have h := (Real.hasDerivAt_mul_log ht0).inv (mul_ne_zero ht0 hl)
  rw [show -wfun t = -(Real.log t + 1) / (t * Real.log t)^2 by unfold wfun; ring]
  exact h

lemma wfun_continuousOn (a b : ℝ) (ha : 1 < a) :
    ContinuousOn wfun (Set.Icc a b) := by
  have hpos : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht => by linarith [ht.1]
  have hlog : ContinuousOn Real.log (Set.Icc a b) :=
    Real.continuousOn_log.mono (fun t ht => (hpos t ht).ne')
  unfold wfun
  apply ContinuousOn.div (hlog.add continuousOn_const) ((continuousOn_id.mul hlog).pow 2)
  intro t ht
  exact pow_ne_zero 2 (mul_ne_zero (hpos t ht).ne' (Real.log_pos (by linarith [ht.1])).ne')

/-- Abel summation for `∑ 1/p`. -/
lemma abel_primes (x y : ℝ) (hx : 2 ≤ x) (hxy : x ≤ y) :
    (∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, 1/(p:ℝ)) =
      Chebyshev.theta y / (y * Real.log y) - Chebyshev.theta x / (x * Real.log x) +
        ∫ t in x..y, Chebyshev.theta t * wfun t := by
  let c : ℕ → ℝ := fun k => if k.Prime then Real.log k else 0
  have hderiv : ∀ t ∈ Set.Icc x y, deriv (fun t : ℝ => (t * Real.log t)⁻¹) t = -wfun t :=
    fun t ht => (hasDerivAt_f t (by linarith [ht.1])).deriv
  have hA := sum_mul_eq_sub_sub_integral_mul c (by linarith) hxy
    (f := fun t : ℝ => (t * Real.log t)⁻¹)
    (fun t ht => (hasDerivAt_f t (by linarith [ht.1])).differentiableAt)
    (by
      refine IntegrableOn.congr_fun ?_ (fun t ht => (hderiv t ht).symm) measurableSet_Icc
      exact ((wfun_continuousOn x y (by linarith)).neg).integrableOn_Icc)
  have hθ : ∀ t : ℝ, ∑ k ∈ Icc 0 ⌊t⌋₊, c k = Chebyshev.theta t := by
    intro t; rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  simp only [hθ] at hA
  have hL : ∑ k ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, (k * Real.log k)⁻¹ * c k =
      ∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, 1/(p:ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    simp only [c]
    split_ifs with hk
    · have h2 : (1:ℝ) < k := by exact_mod_cast hk.one_lt
      have hl : Real.log k ≠ 0 := (Real.log_pos h2).ne'
      field_simp
    · simp
  rw [hL] at hA
  rw [hA]
  have hI : ∫ t in Set.Ioc x y, deriv (fun t : ℝ => (t * Real.log t)⁻¹) t * Chebyshev.theta t =
      -∫ t in x..y, Chebyshev.theta t * wfun t := by
    rw [intervalIntegral.integral_of_le hxy, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    show deriv (fun t : ℝ => (t * Real.log t)⁻¹) t * Chebyshev.theta t = -(Chebyshev.theta t * wfun t)
    rw [hderiv t ⟨ht.1.le, ht.2⟩]; ring
  rw [hI]
  simp only [div_eq_inv_mul]
  ring

end NicCore

namespace NicCore

lemma theta_intervalIntegrable (a b : ℝ) : IntervalIntegrable Chebyshev.theta volume a b :=
  Chebyshev.theta_mono.intervalIntegrable


lemma wfun_uIcc (x y : ℝ) (hx : 1 < x) (hxy : x ≤ y) : ContinuousOn wfun (Set.uIcc x y) := by
  rw [Set.uIcc_of_le hxy]; exact wfun_continuousOn x y hx

lemma gv_eq (t : ℝ) (ht : 1 < t) : gfun t * vfun t = (Chebyshev.psi t - t) * wfun t := by
  have ht0 : t ≠ 0 := by linarith
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  unfold gfun vfun wfun
  field_simp

lemma int_tw (x y : ℝ) (hx : 2 ≤ x) (hxy : x ≤ y) :
    ∫ t in x..y, t * wfun t = (Real.log (Real.log y) - 1 / Real.log y) -
      (Real.log (Real.log x) - 1 / Real.log x) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [Set.uIcc_of_le hxy] at ht
    have ht1 : 1 < t := by linarith [ht.1]
    have ht0 : t ≠ 0 := by linarith
    have hl : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    have h1 := Real.hasDerivAt_log ht0
    have h2 := h1.log hl
    have h3 := (hasDerivAt_const t (1:ℝ)).div h1 hl
    have h4 := h2.sub h3
    rw [show t * wfun t = t⁻¹ / Real.log t - (0 * Real.log t - 1 * t⁻¹) / Real.log t ^ 2 by
      unfold wfun; field_simp; ring]
    exact h4
  · apply ContinuousOn.intervalIntegrable
    exact continuousOn_id.mul (wfun_uIcc x y (by linarith) hxy)

lemma int_split (x y : ℝ) (hx : 2 ≤ x) (hxy : x ≤ y) :
    ∫ t in x..y, Chebyshev.theta t * wfun t =
      (∫ t in x..y, t * wfun t) + (∫ t in x..y, gfun t * vfun t) -
        ∫ t in x..y, (Chebyshev.psi t - Chebyshev.theta t) * wfun t := by
  have hw := wfun_uIcc x y (by linarith) hxy
  have iθ := (theta_intervalIntegrable x y).mul_continuousOn hw
  have iψ := (psi_intervalIntegrable x y).mul_continuousOn hw
  have it : IntervalIntegrable (fun t => t * wfun t) volume x y :=
    (continuousOn_id.mul hw).intervalIntegrable
  have hgv : ∫ t in x..y, gfun t * vfun t = ∫ t in x..y, (Chebyshev.psi t * wfun t - t * wfun t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hxy] at ht
    simp only
    rw [gv_eq t (by linarith [ht.1])]; ring
  have hpt : ∫ t in x..y, (Chebyshev.psi t - Chebyshev.theta t) * wfun t =
      ∫ t in x..y, (Chebyshev.psi t * wfun t - Chebyshev.theta t * wfun t) := by
    congr 1; funext t; ring
  rw [hgv, hpt, intervalIntegral.integral_sub iψ it, intervalIntegral.integral_sub iψ iθ]
  ring

lemma vfun_anti (s t : ℝ) (hs : 1 < s) (hst : s ≤ t) : vfun t ≤ vfun s := by
  have hl : 0 < Real.log s := Real.log_pos hs
  have hlst : Real.log s ≤ Real.log t := Real.log_le_log (by linarith) hst
  unfold vfun
  have h1 : 1 / Real.log t ≤ 1 / Real.log s := one_div_le_one_div_of_le hl hlst
  have h2 : 1 / Real.log t ^ 2 ≤ 1 / Real.log s ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hl.le hlst 2)
  linarith

lemma int_sqrt (x : ℝ) (hx : 0 < x) :
    ∫ t in x..(4*x), Real.sqrt t / t^2 = 1 / Real.sqrt x := by
  have hxy : x ≤ 4*x := by linarith
  have key : ∀ t ∈ Set.uIcc x (4*x), HasDerivAt (fun t => -2 / Real.sqrt t) (Real.sqrt t / t^2) t := by
    intro t ht
    rw [Set.uIcc_of_le hxy] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have h := (hasDerivAt_const t (-2:ℝ)).div (Real.hasDerivAt_sqrt ht0.ne') hs.ne'
    have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
    have e : Real.sqrt t / t^2 = (0 * Real.sqrt t - (-2) * (1 / (2 * Real.sqrt t))) / Real.sqrt t ^ 2 := by
      rw [hsq]
      field_simp
      nlinarith [hsq]
    rw [e]; exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt key]
  · have h4 : Real.sqrt (4*x) = 2 * Real.sqrt x := by
      rw [Real.sqrt_mul (by norm_num), show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h4]
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
    field_simp; ring
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div Real.continuous_sqrt.continuousOn (continuousOn_pow 2)
    intro t ht
    rw [Set.uIcc_of_le hxy] at ht
    exact pow_ne_zero 2 (by linarith [ht.1])

lemma int_psitheta_lower (x y : ℝ) (hx : 1024 ≤ x) (h4 : 4*x ≤ y)
    (hθ : ∀ s : ℝ, 32 ≤ s → s/2 ≤ Chebyshev.theta s) :
    vfun (4*x) / (2 * Real.sqrt x) ≤
      ∫ t in x..y, (Chebyshev.psi t - Chebyshev.theta t) * wfun t := by
  have hxy : x ≤ y := by linarith
  have hx4 : x ≤ 4*x := by linarith
  have hw := wfun_uIcc x y (by linarith) hxy
  have iψθ : IntervalIntegrable (fun t => (Chebyshev.psi t - Chebyshev.theta t) * wfun t) volume x y :=
    ((psi_intervalIntegrable x y).sub (theta_intervalIntegrable x y)).mul_continuousOn hw
  have hnn : ∀ t, 1 < t → 0 ≤ (Chebyshev.psi t - Chebyshev.theta t) * wfun t := by
    intro t ht
    have h1 := Chebyshev.theta_le_psi t
    have h2 : 0 ≤ wfun t := by
      unfold wfun; have := Real.log_pos ht; positivity
    exact mul_nonneg (by linarith) h2
  have step1 : ∫ t in x..(4*x), (Chebyshev.psi t - Chebyshev.theta t) * wfun t ≤
      ∫ t in x..y, (Chebyshev.psi t - Chebyshev.theta t) * wfun t := by
    apply intervalIntegral.integral_mono_interval le_rfl hx4 h4
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall (fun t ht => hnn t (by linarith [ht.1]))
    · exact iψθ
  have hw4 := wfun_uIcc x (4*x) (by linarith) hx4
  have step2 : ∫ t in x..(4*x), (vfun (4*x) / 2) * (Real.sqrt t / t^2) ≤
      ∫ t in x..(4*x), (Chebyshev.psi t - Chebyshev.theta t) * wfun t := by
    apply intervalIntegral.integral_mono_on hx4
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.div Real.continuous_sqrt.continuousOn (continuousOn_pow 2)
      intro t ht
      rw [Set.uIcc_of_le hx4] at ht
      exact pow_ne_zero 2 (by linarith [ht.1])
    · exact ((psi_intervalIntegrable x (4*x)).sub
        (theta_intervalIntegrable x (4*x))).mul_continuousOn hw4
    · intro t ht
      have ht1 : 1 < t := by linarith [ht.1]
      have ht0 : 0 < t := by linarith
      have hst : 32 ≤ Real.sqrt t := by
        rw [show (32:ℝ) = Real.sqrt (32^2) by rw [Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by nlinarith [ht.1])
      -- ψ t - θ t ≥ ψ(√t) ≥ θ(√t) ≥ √t/2
      have hCP := Chebyshev.psi_sub_theta_ge_psi_add_psi_add_psi ht0.le
      have hs2 : t ^ ((2:ℝ)⁻¹) = Real.sqrt t := by
        rw [Real.sqrt_eq_rpow]; norm_num
      rw [hs2] at hCP
      have hp3 := Chebyshev.psi_nonneg (t ^ ((3:ℝ)⁻¹))
      have hp7 := Chebyshev.psi_nonneg (t ^ ((7:ℝ)⁻¹))
      have hθψ := Chebyshev.theta_le_psi (Real.sqrt t)
      have hθs := hθ (Real.sqrt t) hst
      have hdiff : Real.sqrt t / 2 ≤ Chebyshev.psi t - Chebyshev.theta t := by linarith
      have hweq : wfun t = vfun t / t^2 := by
        have hl : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
        unfold wfun vfun; field_simp
      have hv : vfun (4*x) ≤ vfun t := vfun_anti t (4*x) ht1 ht.2
      have hv0 : 0 ≤ vfun (4*x) := by
        unfold vfun; have := Real.log_pos (show (1:ℝ) < 4*x by linarith); positivity
      rw [hweq]
      have hsq0 : 0 ≤ Real.sqrt t / 2 := by positivity
      calc vfun (4*x) / 2 * (Real.sqrt t / t^2) = (Real.sqrt t / 2) * (vfun (4*x) / t^2) := by ring
        _ ≤ (Chebyshev.psi t - Chebyshev.theta t) * (vfun t / t^2) := by
          apply mul_le_mul hdiff _ (by positivity) (by linarith)
          exact div_le_div_of_nonneg_right hv (by positivity)
  rw [intervalIntegral.integral_const_mul, int_sqrt x (by linarith)] at step2
  have : vfun (4*x) / (2 * Real.sqrt x) = vfun (4*x) / 2 * (1 / Real.sqrt x) := by ring
  rw [this]
  linarith

lemma tendsto_theta_err : Tendsto (fun y => (Chebyshev.theta y - y) / (y * Real.log y)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun y => 1 / Real.log y) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  apply squeeze_zero_norm' _ hlog
  filter_upwards [eventually_gt_atTop (1:ℝ)] with y hy
  have hl := Real.log_pos hy
  have hy0 : 0 < y := by linarith
  have h1 := Chebyshev.theta_nonneg y
  have h2 := Chebyshev.theta_le_log4_mul_x hy0.le
  have h4 : Real.log 4 < 2 := by
    have := Real.log_two_lt_d9
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; linarith
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hy0 hl), div_le_div_iff₀ (mul_pos hy0 hl) hl]
  have : |Chebyshev.theta y - y| ≤ y := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  nlinarith

lemma loglog_theta_le (x : ℝ) (hx : 2 ≤ x) (hT : 1 < Chebyshev.theta x) :
    Real.log (Real.log (Chebyshev.theta x)) ≤
      Real.log (Real.log x) + (Chebyshev.theta x - x) / (x * Real.log x) := by
  set T := Chebyshev.theta x
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hlT : 0 < Real.log T := Real.log_pos hT
  have h1 : Real.log T ≤ Real.log x + (T/x - 1) := by
    have := Real.log_le_sub_one_of_pos (div_pos hT0 hx0)
    rw [Real.log_div hT0.ne' hx0.ne'] at this; linarith
  have h2 : Real.log (Real.log T) ≤ Real.log (Real.log x + (T/x - 1)) :=
    Real.log_le_log hlT h1
  have hpos : 0 < Real.log x + (T/x - 1) := by linarith
  have h3 : Real.log (Real.log x + (T/x - 1)) ≤ Real.log (Real.log x) + (T/x - 1) / Real.log x := by
    have e : Real.log x + (T/x - 1) = Real.log x * (1 + (T/x - 1)/Real.log x) := by
      field_simp
    have hpos' : 0 < 1 + (T/x - 1)/Real.log x := by
      rw [e] at hpos; exact pos_of_mul_pos_right hpos hL.le
    rw [e, Real.log_mul hL.ne' hpos'.ne']
    have := Real.log_le_sub_one_of_pos hpos'
    linarith
  have e2 : (T/x - 1) / Real.log x = (T - x) / (x * Real.log x) := by
    field_simp
  linarith

end NicCore

namespace NicCore

theorem high_core (x : ℝ) (hx : 1024 ≤ x) (E : ℝ)
    (hE : ∀ y, x ≤ y → ∫ t in x..y, gfun t * vfun t ≤ E)
    (hθ : ∀ s : ℝ, 32 ≤ s → s/2 ≤ Chebyshev.theta s)
    (hnum : E + 1/(⌊x⌋₊:ℝ) < vfun (4*x) / (2 * Real.sqrt x)) :
    Real.exp Real.eulerMascheroniConstant * Real.log (Chebyshev.theta x) *
      (∏ p ∈ (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime, (1 - 1/(p : ℝ))) < 1 := by
  have hx2 : 2 ≤ x := by linarith
  set V := vfun (4*x) / (2 * Real.sqrt x)
  set C := Chebyshev.theta x / (x * Real.log x) + Real.log (Real.log x) - 1 / Real.log x
    - E + V - 1/(⌊x⌋₊:ℝ)
  -- inequality for every y ≥ 4x
  have hy : ∀ y, 4*x ≤ y → (Lfun y - Real.log (Real.log y)) -
      (Chebyshev.theta y - y) / (y * Real.log y) ≤ Lfun x - C := by
    intro y h4
    have hxy : x ≤ y := by linarith
    have h1 := L_sub_le x y hx2 hxy
    have h2 := abel_primes x y hx2 hxy
    have h3 := int_split x y hx2 hxy
    have h4' := int_tw x y hx2 hxy
    have h5 := hE y hxy
    have h6 := int_psitheta_lower x y hx h4 hθ
    have hy1 : 0 < Real.log y := Real.log_pos (by linarith)
    have hy0 : 0 < y := by linarith
    have e : Chebyshev.theta y / (y * Real.log y) - 1 / Real.log y =
        (Chebyshev.theta y - y) / (y * Real.log y) := by
      field_simp
    simp only [C]
    linarith
  have hlim := (tendsto_L_sub.sub tendsto_theta_err)
  rw [sub_zero] at hlim
  have hγ : Real.eulerMascheroniConstant ≤ Lfun x - C := by
    apply le_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (4*x)] with y hy4
    exact hy y hy4
  -- the final comparison
  have hθx : x/2 ≤ Chebyshev.theta x := hθ x (by linarith)
  have hT : 1 < Chebyshev.theta x := by linarith
  have hll := loglog_theta_le x hx2 hT
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have e2 : Chebyshev.theta x / (x * Real.log x) - 1 / Real.log x =
      (Chebyshev.theta x - x) / (x * Real.log x) := by
    field_simp
  have hkey : Real.eulerMascheroniConstant + Real.log (Real.log (Chebyshev.theta x)) - Lfun x < 0 := by
    simp only [C] at hγ
    linarith
  -- rewrite the product as exp(-L)
  have hQpos : 0 < ∏ p ∈ (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime, (1 - 1/(p : ℝ)) := by
    apply Finset.prod_pos
    intro p hp; exact one_sub_inv_pos p (Finset.mem_filter.mp hp).2
  have hQlog : Real.log (∏ p ∈ (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime, (1 - 1/(p : ℝ))) = -Lfun x := by
    rw [Real.log_prod, Lfun, Finset.sum_neg_distrib, neg_neg]
    intro p hp; exact (one_sub_inv_pos p (Finset.mem_filter.mp hp).2).ne'
  have hlT : 0 < Real.log (Chebyshev.theta x) := Real.log_pos hT
  have hprod : Real.exp Real.eulerMascheroniConstant * Real.log (Chebyshev.theta x) *
      (∏ p ∈ (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime, (1 - 1/(p : ℝ))) =
      Real.exp (Real.eulerMascheroniConstant + Real.log (Real.log (Chebyshev.theta x)) - Lfun x) := by
    have hQ : Real.exp (Lfun x) = (∏ p ∈ (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime, (1 - 1/(p : ℝ)))⁻¹ := by
      rw [← Real.exp_log hQpos, hQlog, Real.exp_neg, inv_inv]
    rw [Real.exp_sub, Real.exp_add, Real.exp_log hlT, hQ]
    field_simp
  rw [hprod]
  calc _ < Real.exp 0 := Real.exp_lt_exp.mpr hkey
    _ = 1 := Real.exp_zero

end NicCore




namespace NicCore

def primeB (n : ℕ) : Bool :=
  decide (2 ≤ n) && (List.range 65).all (fun d => d < 2 || n < d*d || n % d != 0)

lemma primeB_iff (n : ℕ) (hn : n < 4225) : primeB n = true ↔ n.Prime := by
  unfold primeB
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h2, hall⟩
    by_contra hnp
    have hm := Nat.minFac_sq_le_self (by omega) hnp
    have hmp : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
    have hm2 := hmp.two_le
    have hm65 : Nat.minFac n < 65 := by
      by_contra h; push Not at h; nlinarith
    have := hall (Nat.minFac n) hm65
    rcases this with (h | h) | h
    · omega
    · nlinarith
    · exact h (Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd n))
  · intro hp
    refine ⟨hp.two_le, fun d _ => ?_⟩
    by_cases hd : d < 2
    · left; left; simpa using hd
    by_cases hdd : n < d * d
    · left; right; simpa using hdd
    right
    intro h0
    have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero h0
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · omega
    · subst h1; push Not at hdd; nlinarith [hp.two_le]

def scan : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | k+1, n, P =>
    let P' := if primeB n then P * n else P
    decide (P' * 1000^n ≤ 2718^n) && (decide (n < 32) || decide (27183^(n+1) ≤ P'^2 * 10000^(n+1)))
      && scan k (n+1) P'

set_option maxRecDepth 100000 in
theorem scan_ok : scan 4095 1 1 = true := by decide +kernel

lemma primorial_step (m : ℕ) :
    primorial (m+1) = if (m+1).Prime then primorial m * (m+1) else primorial m := by
  unfold primorial
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.prod_insert (by simp), mul_comm]
  · rfl

lemma scan_spec : ∀ k n : ℕ, 1 ≤ n → n + k ≤ 4225 → scan k n (primorial (n-1)) = true →
    ∀ m, n ≤ m → m < n + k →
      primorial m * 1000^m ≤ 2718^m ∧ (32 ≤ m → 27183^(m+1) ≤ primorial m ^ 2 * 10000^(m+1)) := by
  intro k
  induction k with
  | zero => intro n _ _ _ m h1 h2; omega
  | succ k ih =>
    intro n hn hk hs m hm1 hm2
    have hP : (if primeB n then primorial (n-1) * n else primorial (n-1)) = primorial n := by
      obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n-1, by omega⟩
      rw [primorial_step j]
      simp only [Nat.add_sub_cancel]
      have := primeB_iff (j+1) (by omega)
      by_cases h : (j+1).Prime
      · rw [if_pos (this.mpr h), if_pos h]
      · rw [if_neg (by rwa [this]), if_neg h]
    simp only [scan, hP, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hs
    obtain ⟨⟨h1, h2⟩, h3⟩ := hs
    rcases Nat.eq_or_lt_of_le hm1 with rfl | hlt
    · refine ⟨h1, fun h32 => ?_⟩
      rcases h2 with h | h
      · omega
      · exact h
    · have h3' : scan k (n+1) (primorial (n+1-1)) = true := by simpa using h3
      exact ih (n+1) (by omega) (by omega) h3' m (by omega) (by omega)

lemma exp_nat_ge (m : ℕ) : (2718/1000:ℝ)^m ≤ Real.exp m := by
  rw [← Real.exp_one_pow]
  apply pow_le_pow_left₀ (by norm_num)
  have := Real.exp_one_gt_d9; linarith

lemma exp_nat_le (m : ℕ) : Real.exp m ≤ (27183/10000:ℝ)^m := by
  rw [← Real.exp_one_pow]
  apply pow_le_pow_left₀ (Real.exp_pos 1).le
  have := Real.exp_one_lt_d9; linarith

/-- `θ(n) ≤ n` for `1 ≤ n ≤ 4095`. -/
lemma theta_le_self_small (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 4095) : Chebyshev.theta n ≤ n := by
  have hs := (scan_spec 4095 1 le_rfl (by norm_num) (by simpa using scan_ok) n h1 (by omega)).1
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
  have hP : 0 < primorial n := primorial_pos n
  rw [Real.log_le_iff_le_exp (by exact_mod_cast hP)]
  have hR : ((primorial n : ℕ) : ℝ) * 1000^n ≤ 2718^n := by exact_mod_cast hs
  have : ((primorial n : ℕ) : ℝ) ≤ (2718/1000:ℝ)^n := by
    rw [div_pow, le_div_iff₀ (by positivity)]; exact hR
  exact this.trans (exp_nat_ge n)

/-- `(n+1)/2 ≤ θ(n)` for `32 ≤ n ≤ 4095`. -/
lemma theta_ge_half_small (n : ℕ) (h1 : 32 ≤ n) (h2 : n ≤ 4095) :
    ((n:ℝ) + 1) / 2 ≤ Chebyshev.theta n := by
  have hs := (scan_spec 4095 1 le_rfl (by norm_num) (by simpa using scan_ok) n (by omega)
    (by omega)).2 h1
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
  have hP : 0 < primorial n := primorial_pos n
  have hPr : (0:ℝ) < primorial n := by exact_mod_cast hP
  have hR : (27183:ℝ)^(n+1) ≤ ((primorial n : ℕ) : ℝ)^2 * 10000^(n+1) := by exact_mod_cast hs
  have h3 : Real.exp ((n:ℝ)+1) ≤ ((primorial n : ℕ) : ℝ)^2 := by
    have := exp_nat_le (n+1)
    push_cast at this
    refine this.trans ?_
    rw [div_pow, div_le_iff₀ (by positivity)]; exact hR
  have h4 : (n:ℝ) + 1 ≤ 2 * Real.log (primorial n) := by
    have := Real.log_le_log (Real.exp_pos _) h3
    rw [Real.log_exp, Real.log_pow] at this
    push_cast at this; linarith
  linarith

lemma theta_ge_half_large (s : ℝ) (hs : 10000 ≤ s) : s / 2 ≤ Chebyshev.theta s := by
  have h := Chebyshev.theta_ge' (show (1:ℝ) ≤ s by linarith)
  set u := Real.sqrt s with hu
  have hu0 : 100 ≤ u := by
    rw [hu, show (100:ℝ) = Real.sqrt (100^2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsu : s = u^2 := (Real.sq_sqrt (by linarith)).symm
  have hlogs : Real.log s = 2 * Real.log u := by
    rw [hsu, Real.log_pow]; push_cast; ring
  have hlu : Real.log u ≤ 3.6063 + u / 100 := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < u/100 by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    have h100 : Real.log 100 < 4.6063 := by
      rw [show (100:ℝ) = 2^2 * 5^2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow, Real.log_pow]
      have h2 := Real.log_two_lt_d9
      have h5 : Real.log 5 < 1.61 := by
        rw [Real.log_lt_iff_lt_exp (by norm_num)]
        have := Real.exp_one_gt_d9
        have e : Real.exp 1.61 = Real.exp 1 * Real.exp 0.61 := by
          rw [← Real.exp_add]; norm_num
        have h6 : 1 + 0.61 + 0.61^2/2 + 0.61^3/6 + 0.61^4/24 ≤ Real.exp 0.61 := by
          have := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 0.61 by norm_num) 5
          simpa [Finset.sum_range_succ, Nat.factorial] using this
        rw [e]; nlinarith
      push_cast; linarith
    linarith
  have hlog2 : 2 * Real.log 2 + 2 * Real.log u ≥ Real.log (s + 2) := by
    rw [← hlogs]
    have h1 : Real.log (s+2) ≤ Real.log (2*s) := Real.log_le_log (by linarith) (by linarith)
    have e : Real.log (2*s) = Real.log 2 + Real.log s := Real.log_mul (by norm_num) (by linarith)
    have := Real.log_pos (show (1:ℝ) < 2 by norm_num)
    linarith
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hlu0 : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  rw [hlogs] at h
  nlinarith [mul_le_mul_of_nonneg_left hlu (show (0:ℝ) ≤ 4*u+2 by linarith)]

/-- `θ(s) ≥ s/2` for all real `s ≥ 32`. -/
theorem theta_ge_half (s : ℝ) (hs : 32 ≤ s) : s / 2 ≤ Chebyshev.theta s := by
  rcases lt_or_ge s 4096 with h | h
  · set n := ⌊s⌋₊
    have hn1 : 32 ≤ n := Nat.le_floor (by exact_mod_cast hs)
    have hn2 : n ≤ 4095 := by
      have : (n:ℝ) < 4096 := lt_of_le_of_lt (Nat.floor_le (by linarith)) h
      exact_mod_cast (show (n:ℝ) ≤ 4095 by
        have : (n:ℝ) < (4096:ℕ) := by exact_mod_cast this
        have h' : n < 4096 := by exact_mod_cast this
        exact_mod_cast (by omega : n ≤ 4095))
    rw [Chebyshev.theta_eq_theta_coe_floor]
    have := theta_ge_half_small n hn1 hn2
    have hlt : s < (n:ℝ) + 1 := Nat.lt_floor_add_one s
    linarith
  rcases lt_or_ge s 10000 with h' | h'
  · have h3 := TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_low s (by linarith) (by norm_num; linarith)
    have hsq : Real.sqrt s ≤ s / 4 := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    linarith
  · exact theta_ge_half_large s h'

end NicCore




namespace NicCore


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

/-- The numerical inequality behind the analytic range `x ≥ 4096`. -/
lemma numeric_high (x : ℝ) (hx : 4096 ≤ x) (m : ℝ) (hm0 : 0 ≤ m) (hm : m < 1/10) :
    2 * m * x ^ (-(1/2:ℝ)) * vfun x + 1/(⌊x⌋₊:ℝ) < vfun (4*x) / (2 * Real.sqrt x) := by
  set a := Real.sqrt x with ha
  have ha64 : 64 ≤ a := by
    rw [ha, show (64:ℝ) = Real.sqrt (64^2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hxa : x = a^2 := (Real.sq_sqrt (by linarith)).symm
  have hrp : x ^ (-(1/2:ℝ)) = 1 / a := by
    rw [Real.rpow_neg (by linarith), ← Real.sqrt_eq_rpow, one_div]
  rw [hrp]
  set L := Real.log x with hL
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hL0 : 8.3177 ≤ L := by
    have : Real.log 4096 ≤ L := Real.log_le_log (by norm_num) hx
    have e : Real.log 4096 = 12 * Real.log 2 := by
      rw [show (4096:ℝ) = 2^12 by norm_num, Real.log_pow]; norm_num
    linarith
  have hLa : L ≤ 6.3178 + a / 32 := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < a/64 by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    have e : Real.log 64 = 6 * Real.log 2 := by
      rw [show (64:ℝ) = 2^6 by norm_num, Real.log_pow]; norm_num
    have e2 : L = 2 * Real.log a := by
      rw [hL, hxa, Real.log_pow]; push_cast; ring
    linarith
  have hL4 : Real.log (4*x) = L + 2 * Real.log 2 := by
    rw [Real.log_mul (by norm_num) (by linarith), hL]
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
  have hLpos : 0 < L := by linarith
  -- v(x) ≤ 1.1203 / L
  have hv : vfun x ≤ 1.1203 / L := by
    unfold vfun
    rw [← hL]
    have : 1 / L^2 ≤ 0.1203 / L := by
      rw [div_le_div_iff₀ (by positivity) hLpos]; nlinarith
    have e : 1.1203 / L = 1 / L + 0.1203 / L := by ring
    linarith
  -- v(4x) ≥ 0.857 / L
  have hv4 : 0.857 / L ≤ vfun (4*x) := by
    unfold vfun
    rw [hL4]
    have hpos : 0 < L + 2 * Real.log 2 := by linarith
    have h1 : 0.857 / L ≤ 1 / (L + 2 * Real.log 2) := by
      rw [div_le_div_iff₀ hLpos hpos]; nlinarith
    have h2 : 0 ≤ 1 / (L + 2 * Real.log 2)^2 := by positivity
    linarith
  -- ⌊x⌋ ≥ x - 1
  have hfl : x - 1 ≤ (⌊x⌋₊:ℝ) := by
    have := Nat.lt_floor_add_one x; linarith
  have hfl0 : 0 < x - 1 := by linarith
  have hfl1 : 1 / (⌊x⌋₊:ℝ) ≤ 1 / (x - 1) := one_div_le_one_div_of_le hfl0 hfl
  have hx1 : 1 / (x - 1) ≤ 1.00025 / a^2 := by
    rw [div_le_div_iff₀ hfl0 (by positivity)]; rw [← hxa]; nlinarith
  have ha0 : 0 < a := by linarith
  -- assemble
  have hmv : 2 * m * (1 / a) * vfun x ≤ 2 * (1/10) * (1/a) * (1.1203 / L) := by
    have hv0 : 0 ≤ vfun x := by
      unfold vfun; rw [← hL]; positivity
    have : 2 * m * (1/a) ≤ 2 * (1/10) * (1/a) := by
      have : 0 < 1/a := by positivity
      nlinarith
    calc 2 * m * (1 / a) * vfun x ≤ 2 * (1/10) * (1/a) * vfun x :=
          mul_le_mul_of_nonneg_right this hv0
      _ ≤ _ := mul_le_mul_of_nonneg_left hv (by positivity)
  have hfin : 2 * (1/10) * (1/a) * (1.1203 / L) + 1.00025 / a^2 < (0.857 / L) / (2 * a) := by
    rw [show 2 * (1/10) * (1/a) * (1.1203 / L) + 1.00025 / a^2 =
      (0.22406 * a + 1.00025 * L) / (a^2 * L) by field_simp; ring]
    rw [show (0.857 / L) / (2 * a) = (0.4285 * a) / (a^2 * L) by field_simp; ring]
    rw [div_lt_div_iff_of_pos_right (by positivity)]
    nlinarith
  have hv4' : (0.857 / L) / (2 * a) ≤ vfun (4*x) / (2 * a) :=
    div_le_div_of_nonneg_right hv4 (by positivity)
  linarith

/-- Low range: `θ(x) ≤ x` and Rosser–Schoenfeld's lower product bound. -/
lemma low_range (x : ℝ) (hx : 2 ≤ x) (hx8 : x ≤ 10^8) (hθ : Chebyshev.theta x ≤ x) :
    Real.exp Real.eulerMascheroniConstant * Real.log (Chebyshev.theta x) *
      (∏ p ∈ (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime, (1 - 1/(p : ℝ))) < 1 := by
  have hRS := TaoFivePrimes.rosser_schoenfeld_product_bound_lower x hx hx8
  have hset : Nat.primesLE ⌊x⌋₊ = (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime := by
    ext p
    simp only [Nat.primesLE, Nat.primesBelow, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h2.two_le, by omega⟩, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  rw [hset] at hRS
  set S := (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime
  have hprod : (∏ p ∈ S, (p:ℝ) / ((p:ℝ) - 1)) * (∏ p ∈ S, (1 - 1/(p:ℝ))) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p hp
    have h2 : (2:ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    have : (p:ℝ) - 1 ≠ 0 := by linarith
    have : (p:ℝ) ≠ 0 := by linarith
    field_simp
  have hQ : 0 < ∏ p ∈ S, (1 - 1/(p:ℝ)) := by
    apply Finset.prod_pos
    intro p hp
    have h2 : (2:ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have hθ0 : 0 < Chebyshev.theta x := Chebyshev.theta_pos hx
  have hlog : Real.log (Chebyshev.theta x) ≤ Real.log x := Real.log_le_log hθ0 hθ
  have he := Real.exp_pos Real.eulerMascheroniConstant
  calc Real.exp Real.eulerMascheroniConstant * Real.log (Chebyshev.theta x) * (∏ p ∈ S, (1 - 1/(p:ℝ)))
      ≤ Real.exp Real.eulerMascheroniConstant * Real.log x * (∏ p ∈ S, (1 - 1/(p:ℝ))) := by
        apply mul_le_mul_of_nonneg_right _ hQ.le
        exact mul_le_mul_of_nonneg_left hlog he.le
    _ < (∏ p ∈ S, (p:ℝ) / ((p:ℝ) - 1)) * (∏ p ∈ S, (1 - 1/(p:ℝ))) :=
        mul_lt_mul_of_pos_right hRS hQ
    _ = 1 := hprod

end NicCore


namespace NicCore

theorem nicolasAux_of_RH (hRH : RiemannHypothesis) :
    ∀ x : ℝ, 2 ≤ x → Real.exp Real.eulerMascheroniConstant * Real.log (Chebyshev.theta x) *
      (∏ p ∈ (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime, (1 - 1/(p : ℝ))) < 1 := by
  intro x hx
  rcases lt_or_ge x 4096 with h | h
  · apply low_range x hx (by linarith)
    have hn2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    have hn : ⌊x⌋₊ ≤ 4095 := by
      have h' : ⌊x⌋₊ < 4096 := by
        have := Nat.floor_lt (show (0:ℝ) ≤ x by linarith) |>.mpr (show x < ((4096:ℕ):ℝ) by
          exact_mod_cast h)
        exact this
      omega
    rw [Chebyshev.theta_eq_theta_coe_floor]
    exact (theta_le_self_small ⌊x⌋₊ (by omega) hn).trans (Nat.floor_le (by linarith))
  · set m := max βc 0
    have hm0 : 0 ≤ m := le_max_right _ _
    have hm : m < 1/10 := max_lt beta_lt (by norm_num)
    have hx0 : 0 < x := by linarith
    apply high_core x (by linarith) (2 * m * x ^ (-(1/2:ℝ)) * vfun x) _ theta_ge_half
      (numeric_high x h m hm0 hm)
    intro y hxy
    apply ibp_bound x y (by linarith) hxy
      (fun a b ha hb => gfun_intervalIntegrable a b ha hb) (2 * m * x ^ (-(1/2:ℝ)))
      (by positivity)
    intro t hxt _
    rw [integral_gfun x t (by linarith) hxt]
    have h1 := M_sub_le hRH x t (by linarith) hxt
    have h2 : t ^ (-(1/2:ℝ)) ≤ x ^ (-(1/2:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hx0 hxt (by norm_num)
    have h3 : βc ≤ m := le_max_left _ _
    have h4 : 0 ≤ t ^ (-(1/2:ℝ)) := Real.rpow_nonneg (by linarith) _
    have h5 : 0 ≤ x ^ (-(1/2:ℝ)) := Real.rpow_nonneg hx0.le _
    nlinarith

end NicCore

theorem solution :
    ∀ x : ℝ, 2 ≤ x → Real.exp Real.eulerMascheroniConstant * Real.log (Chebyshev.theta x) * (∏ p ∈ (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime, (1 - 1/(p : ℝ))) < 1 :=
  NicCore.nicolasAux_of_RH riemann_hypothesis
