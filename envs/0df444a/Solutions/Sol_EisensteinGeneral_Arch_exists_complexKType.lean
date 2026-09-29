-- Prove2me | solution 1 for EisensteinGeneral.Arch.exists_complexKType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/ca50f797-d033-5d70-be58-f5e72c239f77

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Theorems.Thm_EisensteinGeneral_Arch_exists_norm_archIntegral_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_EisensteinGeneral_Arch_exists_complexKType

open Set MeasureTheory
set_option autoImplicit false

namespace EgenArch

private theorem e1_norm_kernel (c : ℂ) (r u : ℝ) :
    ‖Complex.exp (-c * (u + r ^ 2 / u))‖ = Real.exp (-c.re * (u + r ^ 2 / u)) := by
  have h : (u + r ^ 2 / u : ℂ) = ((u + r ^ 2 / u : ℝ) : ℂ) := by
    simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_pow]
  rw [Complex.norm_exp, h, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.neg_re]

private theorem e1_kernel_continuousOn (c : ℂ) (r : ℝ) :
    ContinuousOn (fun u : ℝ => Complex.exp (-c * (u + r ^ 2 / u))) (Ioi 0) :=
  ContinuousOn.cexp (continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.add
    (continuousOn_const.div Complex.continuous_ofReal.continuousOn fun _ hu =>
      Complex.ofReal_ne_zero.mpr (ne_of_gt hu))))

open Asymptotics _root_.Filter _root_.Asymptotics.Filter in

private theorem e1_kernel_isBigO_atTop (c : ℂ) (hc : 0 < c.re) (r : ℝ) :
    (fun u : ℝ => Complex.exp (-c * (u + r ^ 2 / u))) =O[atTop] fun u : ℝ => Real.exp (-c.re * u) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  rw [e1_norm_kernel, one_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp]
  exact mul_le_mul_of_nonpos_left (le_add_of_nonneg_right (div_nonneg (sq_nonneg r) hu.le))
    (neg_nonpos.mpr hc.le)

open Asymptotics _root_.Filter _root_.Asymptotics.Filter Topology in

private theorem e1_kernel_isBigO_nhdsGT (c : ℂ) (hc : 0 < c.re) (r : ℝ) (hr : r ≠ 0) (b : ℝ) :
    (fun u : ℝ => Complex.exp (-c * (u + r ^ 2 / u))) =O[𝓝[>] 0] fun u : ℝ => u ^ (-b) := by
  have hκ : 0 < c.re * r ^ 2 := mul_pos hc (lt_of_le_of_ne (sq_nonneg r) (Ne.symm (pow_ne_zero 2 hr)))
  have h1 : (fun u : ℝ => Complex.exp (-c * (u + r ^ 2 / u))) =O[𝓝[>] 0]
      fun u : ℝ => Real.exp (-(c.re * r ^ 2) * u⁻¹) := by
    refine IsBigO.of_bound 1 (eventually_nhdsWithin_of_forall fun u hu => ?_)
    rw [e1_norm_kernel, one_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp]
    calc -c.re * (u + r ^ 2 / u) ≤ -c.re * (r ^ 2 / u) :=
          mul_le_mul_of_nonpos_left (le_add_of_nonneg_left (le_of_lt hu)) (neg_nonpos.mpr hc.le)
      _ = -(c.re * r ^ 2) * u⁻¹ := by ring
  have h2 : (fun u : ℝ => Real.exp (-(c.re * r ^ 2) * u⁻¹)) =o[𝓝[>] 0] fun u : ℝ => u ^ (-b) := by
    refine ((isLittleO_exp_neg_mul_rpow_atTop hκ b).comp_tendsto tendsto_inv_nhdsGT_zero).congr'
      (Eventually.of_forall fun u => rfl) (eventually_nhdsWithin_of_forall fun u hu => ?_)
    show u⁻¹ ^ b = u ^ (-b)
    rw [Real.inv_rpow (le_of_lt hu), Real.rpow_neg (le_of_lt hu)]
  exact h1.trans h2.isBigO

private theorem e1_mellin_differentiableAt (c : ℂ) (hc : 0 < c.re) (r : ℝ) (hr : r ≠ 0) (s : ℂ) :
    DifferentiableAt ℂ (mellin fun u : ℝ => Complex.exp (-c * (u + r ^ 2 / u))) s :=
  mellin_differentiableAt_of_isBigO_rpow_exp hc
    ((e1_kernel_continuousOn c r).locallyIntegrableOn measurableSet_Ioi)
    (e1_kernel_isBigO_atTop c hc r) (e1_kernel_isBigO_nhdsGT c hc r hr (s.re - 1)) (sub_one_lt _)

private theorem differentiable_archIntegral (c : ℂ) (hc : 0 < c.re) (r : ℝ) (hr : r ≠ 0) :
    Differentiable ℂ (fun z : ℂ =>
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ z * Complex.exp (-c * (u + r ^ 2 / u))) := by
  have h : (fun z : ℂ => ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ z * Complex.exp (-c * (u + r ^ 2 / u)))
      = (mellin fun u : ℝ => Complex.exp (-c * (u + r ^ 2 / u))) ∘ fun z : ℂ => z + 1 := by
    funext z
    simp only [Function.comp_apply, mellin, add_sub_cancel_right, smul_eq_mul]
  have hg : Differentiable ℂ (mellin fun u : ℝ => Complex.exp (-c * (u + r ^ 2 / u))) :=
    fun s => e1_mellin_differentiableAt c hc r hr s
  have hf : Differentiable ℂ fun z : ℂ => z + 1 := differentiable_id.add_const 1
  rw [h]
  exact hg.comp hf

private theorem e4_max_pow_mul_exp_le {x k : ℝ} (hx : 0 ≤ x) (hk : 0 < k) (m : ℕ) :
    max 1 (x ^ m) * Real.exp (-k * x)
      ≤ max 1 ((Nat.factorial m : ℝ) / (k / 2) ^ m) * Real.exp (-(k / 2) * x) := by
  have hk2 : 0 < k / 2 := half_pos hk
  have hkx : 0 ≤ k / 2 * x := mul_nonneg hk2.le hx
  have hexp : Real.exp (-k * x) ≤ Real.exp (-(k / 2) * x) := Real.exp_le_exp.mpr (by linarith)
  rw [max_mul_of_nonneg _ _ (Real.exp_nonneg _)]
  refine max_le ?_ ?_
  · rw [one_mul]
    exact hexp.trans (le_mul_of_one_le_left (Real.exp_nonneg _) (le_max_left _ _))
  · have h1 : x ^ m ≤ (Nat.factorial m : ℝ) / (k / 2) ^ m * Real.exp (k / 2 * x) := by
      have h := Real.pow_div_factorial_le_exp _ hkx m
      rw [mul_pow, div_le_iff₀ (by positivity)] at h
      rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hk2 m)]
      calc x ^ m * (k / 2) ^ m = (k / 2) ^ m * x ^ m := mul_comm _ _
        _ ≤ Real.exp (k / 2 * x) * (Nat.factorial m : ℝ) := h
        _ = (Nat.factorial m : ℝ) * Real.exp (k / 2 * x) := mul_comm _ _
    calc x ^ m * Real.exp (-k * x)
        ≤ (Nat.factorial m : ℝ) / (k / 2) ^ m * Real.exp (k / 2 * x) * Real.exp (-k * x) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
      _ = (Nat.factorial m : ℝ) / (k / 2) ^ m * Real.exp (-(k / 2) * x) := by
          rw [mul_assoc, ← Real.exp_add, show k / 2 * x + -k * x = -(k / 2) * x by ring]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _)

private theorem e4_pow_mul_exp_le {x k : ℝ} (hx : 0 ≤ x) (hk : 0 < k) (m : ℕ) :
    x ^ m * Real.exp (-k * x) ≤ max 1 ((Nat.factorial m : ℝ) / (k / 2) ^ m) * Real.exp (-(k / 2) * x) :=
  (mul_le_mul_of_nonneg_right (le_max_right 1 (x ^ m)) (Real.exp_nonneg _)).trans (e4_max_pow_mul_exp_le hx hk m)

private theorem e4_max_rpow_le {x : ℝ} (hx : 0 < x) {N N' : ℕ} (h : N ≤ N') :
    max 1 (x ^ (-(N : ℝ))) ≤ max 1 (x ^ (-(N' : ℝ))) := by
  rw [Real.rpow_neg hx.le, Real.rpow_neg hx.le, Real.rpow_natCast, Real.rpow_natCast]
  refine max_le (le_max_left _ _) ?_
  rcases le_or_gt x 1 with h1 | h1
  · exact le_max_of_le_right (inv_anti₀ (pow_pos hx N') (pow_le_pow_of_le_one hx.le h1 h))
  · exact le_max_of_le_left (inv_le_one_of_one_le₀ (one_le_pow₀ h1.le))

private theorem e4_exists_pos_le {κ : Type} (T : Finset κ) (f : κ → ℝ) (hf : ∀ i ∈ T, 0 < f i) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ i ∈ T, c₂ ≤ f i := by
  rcases T.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, fun i hi => by simp [h] at hi⟩
  · obtain ⟨i₀, hi₀T, hi₀⟩ := T.exists_min_image f h
    exact ⟨f i₀, hf i₀ hi₀T, fun i hi => hi₀ i hi⟩

private theorem differentiable_sum_archIntegral {κ : Type} (T : Finset κ) (a : κ → ℂ → ℂ)
    (ha : ∀ i ∈ T, Differentiable ℂ (a i)) (β b : κ → ℂ) (l : κ → ℕ)
    (c : ℂ) (hc : 0 < c.re) (r : ℝ) (hr : r ≠ 0) :
    Differentiable ℂ (fun z : ℂ => ∑ i ∈ T, a i z * β i * (r : ℂ) ^ l i *
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (z + b i) * Complex.exp (-c * (u + r ^ 2 / u))) := by
  have hI := differentiable_archIntegral c hc r hr
  have hJ : ∀ i : κ, Differentiable ℂ (fun z : ℂ =>
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (z + b i) * Complex.exp (-c * (u + r ^ 2 / u))) :=
    fun i => hI.fun_comp (f := fun z : ℂ => z + b i) (by fun_prop)
  apply Differentiable.fun_sum
  intro i hi
  have h1 := ha i hi
  have h2 := hJ i
  fun_prop

private theorem exists_norm_sum_archIntegral_le {κ : Type} (T : Finset κ) (a : κ → ℂ → ℂ)
    (ha : ∀ i ∈ T, Differentiable ℂ (a i)) (b : κ → ℂ) (l : κ → ℕ) (c : ℂ) (hc : 0 < c.re) (R : ℝ) :
    ∃ C c' : ℝ, ∃ N : ℕ, 0 < C ∧ 0 < c' ∧ ∀ (β : κ → ℂ), (∀ i ∈ T, ‖β i‖ ≤ 1) →
      ∀ (z : ℂ) (r : ℝ), ‖z‖ ≤ R → r ≠ 0 →
      ‖∑ i ∈ T, a i z * β i * (r : ℂ) ^ l i *
          ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (z + b i) * Complex.exp (-c * (u + r ^ 2 / u))‖
        ≤ C * max 1 (|r| ^ (-(N : ℝ))) * Real.exp (-c' * |r|) := by
  choose Ci ci Ni hCi hci hE2 using fun i : κ => EisensteinGeneral.Arch.exists_norm_archIntegral_le c hc (R + ‖b i‖)
  have hbound : ∀ i : κ, ∃ A : ℝ, 0 ≤ A ∧ (i ∈ T → ∀ z : ℂ, ‖z‖ ≤ R → ‖a i z‖ ≤ A) := by
    intro i
    by_cases hi : i ∈ T
    · obtain ⟨B, hB⟩ :=
        (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn (ha i hi).continuous.continuousOn
      refine ⟨max B 0, le_max_right _ _, fun _ z hz => (hB z ?_).trans (le_max_left _ _)⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hz
    · exact ⟨0, le_rfl, fun h => absurd h hi⟩
  choose A hA0 hA using hbound
  obtain ⟨c₂, hc₂, hc₂le⟩ := e4_exists_pos_le T (fun i => ci i / 2) (fun i _ => half_pos (hci i))
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ i ∈ T, Ni i ≤ N₂ := ⟨T.sup Ni, fun i hi => Finset.le_sup (f := Ni) hi⟩
  refine ⟨(∑ i ∈ T, A i * Ci i * max 1 ((Nat.factorial (l i) : ℝ) / (ci i / 2) ^ l i)) + 1, c₂, N₂, ?_, hc₂, ?_⟩
  · refine add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun i _ => ?_) one_pos
    have := hA0 i
    have := hCi i
    positivity
  intro β hβ z r hz hr
  have hr0 : 0 < |r| := abs_pos.mpr hr
  have hX : 0 ≤ max 1 (|r| ^ (-(N₂ : ℝ))) * Real.exp (-c₂ * |r|) := by positivity
  have hterm : ∀ i ∈ T,
      ‖a i z * β i * (r : ℂ) ^ l i *
          ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (z + b i) * Complex.exp (-c * (u + r ^ 2 / u))‖
        ≤ A i * Ci i * max 1 ((Nat.factorial (l i) : ℝ) / (ci i / 2) ^ l i) *
            (max 1 (|r| ^ (-(N₂ : ℝ))) * Real.exp (-c₂ * |r|)) := by
    intro i hi
    have hre : |(z + b i).re| ≤ R + ‖b i‖ :=
      (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans (add_le_add hz le_rfl))
    have hI := hE2 i (z + b i) r hre hr
    have ha' := hA i hi z hz
    have hβ' := hβ i hi
    have hA0i := hA0 i
    have hCi' := hCi i
    have hmax := e4_max_rpow_le hr0 (hN₂ i hi)
    have hpow := e4_pow_mul_exp_le (abs_nonneg r) (hci i) (l i)
    have hc₂i : c₂ ≤ ci i / 2 := hc₂le i hi
    have hexp : Real.exp (-(ci i / 2) * |r|) ≤ Real.exp (-c₂ * |r|) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hc₂i (abs_nonneg r)])
    rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    calc _ ≤ A i * 1 * |r| ^ l i * (Ci i * max 1 (|r| ^ (-(Ni i : ℝ))) * Real.exp (-ci i * |r|)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul ha' hβ' (norm_nonneg _) hA0i) (by positivity)) hI
            (norm_nonneg _) (by positivity)
      _ = A i * Ci i * (max 1 (|r| ^ (-(Ni i : ℝ))) * (|r| ^ l i * Real.exp (-ci i * |r|))) := by ring
      _ ≤ A i * Ci i * (max 1 (|r| ^ (-(N₂ : ℝ))) *
            (max 1 ((Nat.factorial (l i) : ℝ) / (ci i / 2) ^ l i) * Real.exp (-(ci i / 2) * |r|))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hmax hpow (by positivity) (by positivity)) (by positivity)
      _ ≤ A i * Ci i * (max 1 (|r| ^ (-(N₂ : ℝ))) *
            (max 1 ((Nat.factorial (l i) : ℝ) / (ci i / 2) ^ l i) * Real.exp (-c₂ * |r|))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (by positivity)) (by positivity))
            (by positivity)
      _ = _ := by ring
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.sum_mul]
  calc _ ≤ ((∑ i ∈ T, A i * Ci i * max 1 ((Nat.factorial (l i) : ℝ) / (ci i / 2) ^ l i)) + 1) *
        (max 1 (|r| ^ (-(N₂ : ℝ))) * Real.exp (-c₂ * |r|)) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hX
    _ = _ := by ring

private noncomputable def e7G (a b : ℕ) (v : ℝ) (ζ : ℂ) : ℂ :=
  ∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
    * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))

private noncomputable def e7E (v : ℝ) (ζ : ℂ) : ℂ :=
  Complex.exp (-(4 * (Real.pi : ℂ) ^ 2) * ((ζ.re : ℂ) ^ 2 + (ζ.im : ℂ) ^ 2) / (v : ℂ))

private noncomputable def e7T (γ : ℂ) (p q m : ℕ) (v : ℝ) (ζ : ℂ) : ℂ :=
  γ * ζ ^ p * (starRingEnd ℂ) ζ ^ q * ((v : ℂ) ^ (m + 1))⁻¹ * e7E v ζ

private theorem e7_one_add_pow_le (v : ℝ) (hv : 0 < v) (N : ℕ) (hN : 0 < N) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 ≤ t → (1 + t) ^ N ≤ K * Real.exp (v * t) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  refine ⟨(max 1 ((N : ℝ) / v)) ^ N, by positivity, fun t ht => ?_⟩
  have h1 : 1 + t ≤ max 1 ((N : ℝ) / v) * (1 + v / N * t) := by
    rcases le_total 1 ((N : ℝ) / v) with h | h
    · rw [max_eq_right h]
      have h2 : (N : ℝ) / v * (1 + v / N * t) = N / v + t := by
        field_simp
      rw [h2]
      linarith
    · rw [max_eq_left h, one_mul]
      have h3 : (N : ℝ) ≤ v := by rwa [div_le_one hv] at h
      have h4 : 1 ≤ v / N := by rw [le_div_iff₀ hNpos]; linarith
      nlinarith
  have h2 : 1 + v / N * t ≤ Real.exp (v / N * t) := by
    have := Real.add_one_le_exp (v / N * t)
    linarith
  have h3 : (1 + v / N * t) ^ N ≤ Real.exp (v * t) := by
    calc (1 + v / N * t) ^ N ≤ (Real.exp (v / N * t)) ^ N := by
          gcongr
      _ = Real.exp (v * t) := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
  calc (1 + t) ^ N ≤ (max 1 ((N : ℝ) / v) * (1 + v / N * t)) ^ N := by gcongr
    _ = (max 1 ((N : ℝ) / v)) ^ N * (1 + v / N * t) ^ N := mul_pow _ _ _
    _ ≤ (max 1 ((N : ℝ) / v)) ^ N * Real.exp (v * t) := by gcongr

private theorem e7_gauss_moment_integrable (n : ℕ) (v : ℝ) (hv : 0 < v) :
    Integrable (fun z : ℂ => ‖z‖ ^ n * Real.exp (-(v * ‖z‖ ^ 2))) := by
  obtain ⟨K, hK, hKle⟩ := e7_one_add_pow_le v hv (n + 2) (by omega)
  have hmaj : Integrable (fun z : ℂ => K * ((1 : ℝ) + ‖z‖ ^ 2) ^ (-(4 : ℝ) / 2)) :=
    (integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 4)
      (by rw [Complex.finrank_real_complex]; norm_num)).const_mul K
  refine hmaj.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact (by fun_prop : Continuous fun z : ℂ => ‖z‖ ^ n * Real.exp (-(v * ‖z‖ ^ 2))).aestronglyMeasurable
  · have ht0 : (0 : ℝ) ≤ ‖z‖ ^ 2 := by positivity
    have h1t : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
    have h1t' : (1 : ℝ) + ‖z‖ ^ 2 ≠ 0 := h1t.ne'
    rw [Real.norm_of_nonneg (by positivity)]
    have hz : ‖z‖ ≤ 1 + ‖z‖ ^ 2 := by nlinarith [norm_nonneg z, sq_nonneg (‖z‖ - 1)]
    have hzn : ‖z‖ ^ n ≤ (1 + ‖z‖ ^ 2) ^ n := by gcongr
    have hexp : Real.exp (-(v * ‖z‖ ^ 2)) ≤ K / (1 + ‖z‖ ^ 2) ^ (n + 2) := by
      rw [le_div_iff₀ (by positivity), Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
      have := hKle (‖z‖ ^ 2) ht0
      linarith [this]
    have hr : ((1 : ℝ) + ‖z‖ ^ 2) ^ (-(4 : ℝ) / 2) = ((1 + ‖z‖ ^ 2) ^ 2)⁻¹ := by
      rw [show (-(4 : ℝ) / 2) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg h1t.le, Real.rpow_natCast]
    rw [hr]
    calc ‖z‖ ^ n * Real.exp (-(v * ‖z‖ ^ 2)) ≤ (1 + ‖z‖ ^ 2) ^ n * (K / (1 + ‖z‖ ^ 2) ^ (n + 2)) := by
          gcongr
      _ = K * ((1 + ‖z‖ ^ 2) ^ 2)⁻¹ := by
          field_simp
          ring

private theorem e7_norm_Gint (a b : ℕ) (v : ℝ) (ζ z : ℂ) :
    ‖z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
      * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))‖
      = ‖z‖ ^ (a + b) * Real.exp (-(v * ‖z‖ ^ 2)) := by
  have hchar : ‖Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))‖ = 1 := by
    rw [← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
  have h1 : (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2) = ((-(v * ‖z‖ ^ 2) : ℝ) : ℂ) := by push_cast; ring
  have hg : ‖Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)‖ = Real.exp (-(v * ‖z‖ ^ 2)) := by
    rw [Complex.norm_exp, h1, Complex.ofReal_re]
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, hg, hchar, mul_one, pow_add]

private theorem e7_Gint_continuous (a b : ℕ) (v : ℝ) (ζ : ℂ) :
    Continuous (fun z : ℂ => z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
      * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))) := by
  fun_prop

private theorem e7_Gint_integrable (a b : ℕ) (v : ℝ) (hv : 0 < v) (ζ : ℂ) :
    Integrable (fun z : ℂ => z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
      * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))) := by
  refine (e7_gauss_moment_integrable (a + b) v hv).mono'
    (e7_Gint_continuous a b v ζ).aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  rw [e7_norm_Gint]

private theorem e7_ofReal_norm_sq (ζ : ℂ) : ((‖ζ‖ : ℝ) : ℂ) ^ 2 = (ζ.re : ℂ) ^ 2 + (ζ.im : ℂ) ^ 2 := by
  rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.normSq_apply]
  push_cast
  ring

private theorem e7G_zero_zero (v : ℝ) (hv : 0 < v) (ζ : ℂ) :
    e7G 0 0 v ζ = e7T (Real.pi : ℂ) 0 0 0 v ζ := by
  have hb : (0 : ℝ) < (v : ℂ).re := by simpa using hv
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := ℂ) hb
    (-(4 * (Real.pi : ℂ) * Complex.I)) ((starRingEnd ℂ) ζ)
  have hL : e7G 0 0 v ζ = ∫ z : ℂ, Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2
      + -(4 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ ((starRingEnd ℂ) ζ) z : ℝ) : ℂ)) := by
    unfold e7G
    congr 1
    funext z
    rw [pow_zero, pow_zero, one_mul, one_mul, ← Complex.exp_add]
    congr 1
    rw [Complex.inner, starRingEnd_self_apply, mul_comm z ζ]
    push_cast
    ring
  have hfin : ((Module.finrank ℝ ℂ : ℂ) / 2) = 1 := by
    rw [Complex.finrank_real_complex]
    norm_num
  have hI : (-(4 * (Real.pi : ℂ) * Complex.I)) ^ 2 = -(16 * (Real.pi : ℂ) ^ 2) := by
    ring_nf
    rw [Complex.I_sq]
    ring
  have hv' : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  rw [hL, h, hfin, Complex.cpow_one, hI, Complex.norm_conj, e7_ofReal_norm_sq]
  unfold e7T e7E
  simp only [pow_zero, mul_one, zero_add, pow_one]
  rw [div_eq_mul_inv]
  congr 1
  field_simp
  ring_nf

private noncomputable def e7c (d z : ℂ) : ℂ := -(((4 * Real.pi * (d * z).re : ℝ) : ℂ) * Complex.I)

private noncomputable def e7Gd (a b : ℕ) (v : ℝ) (ζ d : ℂ) : ℂ :=
  ∫ z : ℂ, e7c d z * (z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
    * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)))

private theorem e7c_continuous (d : ℂ) : Continuous (fun z : ℂ => e7c d z) := by
  simp only [e7c]
  fun_prop

private theorem e7_norm_e7c_le (d z : ℂ) : ‖e7c d z‖ ≤ 4 * Real.pi * ‖d‖ * ‖z‖ := by
  have h1 : |(d * z).re| ≤ ‖d‖ * ‖z‖ := by
    rw [← norm_mul]
    exact Complex.abs_re_le_norm _
  have h2 : ‖e7c d z‖ = 4 * Real.pi * |(d * z).re| := by
    unfold e7c
    rw [norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 4 * Real.pi)]
  rw [h2]
  calc 4 * Real.pi * |(d * z).re| ≤ 4 * Real.pi * (‖d‖ * ‖z‖) := by gcongr
    _ = 4 * Real.pi * ‖d‖ * ‖z‖ := by ring

private theorem e7_norm_Gd_le (a b : ℕ) (v : ℝ) (ζ d z : ℂ) :
    ‖e7c d z * (z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
      * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)))‖
      ≤ 4 * Real.pi * ‖d‖ * (‖z‖ ^ (a + b + 1) * Real.exp (-(v * ‖z‖ ^ 2))) := by
  rw [norm_mul, e7_norm_Gint]
  calc ‖e7c d z‖ * (‖z‖ ^ (a + b) * Real.exp (-(v * ‖z‖ ^ 2)))
      ≤ 4 * Real.pi * ‖d‖ * ‖z‖ * (‖z‖ ^ (a + b) * Real.exp (-(v * ‖z‖ ^ 2))) :=
        mul_le_mul_of_nonneg_right (e7_norm_e7c_le d z) (by positivity)
    _ = 4 * Real.pi * ‖d‖ * (‖z‖ ^ (a + b + 1) * Real.exp (-(v * ‖z‖ ^ 2))) := by ring

private theorem e7_Gd_integrable (a b : ℕ) (v : ℝ) (hv : 0 < v) (ζ d : ℂ) :
    Integrable (fun z : ℂ => e7c d z * (z ^ a * (starRingEnd ℂ) z ^ b
      * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
      * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)))) :=
  ((e7_gauss_moment_integrable (a + b + 1) v hv).const_mul (4 * Real.pi * ‖d‖)).mono'
    ((e7c_continuous d).mul (e7_Gint_continuous a b v ζ)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => e7_norm_Gd_le a b v ζ d z)

private theorem e7_char_line (ζ₀ d z : ℂ) (x : ℝ) :
    (-(((4 * Real.pi * ((ζ₀ + x * d) * z).re : ℝ) : ℂ) * Complex.I))
      = (-(((4 * Real.pi * (ζ₀ * z).re : ℝ) : ℂ) * Complex.I)) + (x : ℂ) * e7c d z := by
  unfold e7c
  simp only [add_mul, Complex.add_re, mul_assoc, Complex.re_ofReal_mul]
  push_cast
  ring

private theorem e7_line_hasDerivAt (ζ₀ d z A : ℂ) (x : ℝ) :
    HasDerivAt
      (fun x : ℝ => A * Complex.exp (-(((4 * Real.pi * ((ζ₀ + x * d) * z).re : ℝ) : ℂ) * Complex.I)))
      (e7c d z * (A * Complex.exp (-(((4 * Real.pi * ((ζ₀ + x * d) * z).re : ℝ) : ℂ) * Complex.I))))
      x := by
  simp only [e7_char_line]
  have hlin : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) x := by
    simpa using (hasDerivAt_id x).ofReal_comp
  exact ((((hlin.mul_const (e7c d z)).const_add
    (-(((4 * Real.pi * (ζ₀ * z).re : ℝ) : ℂ) * Complex.I))).cexp).const_mul A).congr_deriv (by ring)

private theorem e7G_hasDerivAt_line (a b : ℕ) (v : ℝ) (hv : 0 < v) (ζ₀ d : ℂ) :
    HasDerivAt (fun x : ℝ => e7G a b v (ζ₀ + x * d)) (e7Gd a b v ζ₀ d) 0 := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := (0 : ℝ))
    (F := fun (x : ℝ) (z : ℂ) => z ^ a * (starRingEnd ℂ) z ^ b
      * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
      * Complex.exp (-(((4 * Real.pi * ((ζ₀ + x * d) * z).re : ℝ) : ℂ) * Complex.I)))
    (F' := fun (x : ℝ) (z : ℂ) => e7c d z * (z ^ a * (starRingEnd ℂ) z ^ b
      * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
      * Complex.exp (-(((4 * Real.pi * ((ζ₀ + x * d) * z).re : ℝ) : ℂ) * Complex.I))))
    (bound := fun z : ℂ => 4 * Real.pi * ‖d‖ * (‖z‖ ^ (a + b + 1) * Real.exp (-(v * ‖z‖ ^ 2))))
    Filter.univ_mem
    (Filter.Eventually.of_forall fun x => (e7_Gint_continuous a b v (ζ₀ + x * d)).aestronglyMeasurable)
    (e7_Gint_integrable a b v hv (ζ₀ + (0 : ℝ) * d))
    (e7_Gd_integrable a b v hv (ζ₀ + (0 : ℝ) * d) d).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z x _ => e7_norm_Gd_le a b v (ζ₀ + x * d) d z)
    ((e7_gauss_moment_integrable (a + b + 1) v hv).const_mul (4 * Real.pi * ‖d‖))
    (Filter.Eventually.of_forall fun z x _ => e7_line_hasDerivAt ζ₀ d z _ x)
  unfold e7G e7Gd
  exact key.2.congr_deriv (by simp only [Complex.ofReal_zero, zero_mul, add_zero])

private theorem e7_conj_eq (z : ℂ) : (starRingEnd ℂ) z = (z.re : ℂ) - (z.im : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

private theorem e7Gd_sub (a b : ℕ) (v : ℝ) (hv : 0 < v) (ζ : ℂ) :
    e7Gd a b v ζ 1 - Complex.I * e7Gd a b v ζ Complex.I
      = -(4 * (Real.pi : ℂ) * Complex.I) * e7G (a + 1) b v ζ := by
  unfold e7Gd e7G
  rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (e7_Gd_integrable a b v hv ζ 1)
    ((e7_Gd_integrable a b v hv ζ Complex.I).const_mul Complex.I)]
  congr 1
  funext z
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := (Complex.re_add_im z).symm
  have key : ∀ w : ℂ, e7c 1 z * w - Complex.I * (e7c Complex.I z * w)
      = -(4 * (Real.pi : ℂ) * Complex.I) * (z * w) := by
    intro w
    unfold e7c
    simp only [one_mul, Complex.I_mul_re]
    push_cast
    linear_combination (4 * (Real.pi : ℂ) * Complex.I * w) * hz
  rw [key]
  ring

private theorem e7Gd_add (a b : ℕ) (v : ℝ) (hv : 0 < v) (ζ : ℂ) :
    e7Gd a b v ζ 1 + Complex.I * e7Gd a b v ζ Complex.I
      = -(4 * (Real.pi : ℂ) * Complex.I) * e7G a (b + 1) v ζ := by
  unfold e7Gd e7G
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (e7_Gd_integrable a b v hv ζ 1)
    ((e7_Gd_integrable a b v hv ζ Complex.I).const_mul Complex.I)]
  congr 1
  funext z
  have hzc := e7_conj_eq z
  have key : ∀ w : ℂ, e7c 1 z * w + Complex.I * (e7c Complex.I z * w)
      = -(4 * (Real.pi : ℂ) * Complex.I) * ((starRingEnd ℂ) z * w) := by
    intro w
    unfold e7c
    simp only [one_mul, Complex.I_mul_re]
    push_cast
    linear_combination (4 * (Real.pi : ℂ) * Complex.I * w) * hzc
  rw [key]
  ring

private noncomputable def e7Thol (γ : ℂ) (p q m : ℕ) (v : ℝ) (ζ₀ d u : ℂ) : ℂ :=
  γ * (ζ₀ + u * d) ^ p * ((starRingEnd ℂ) ζ₀ + u * (starRingEnd ℂ) d) ^ q * ((v : ℂ) ^ (m + 1))⁻¹
    * Complex.exp (-(4 * (Real.pi : ℂ) ^ 2) * (((ζ₀.re : ℂ) + u * (d.re : ℂ)) ^ 2
        + ((ζ₀.im : ℂ) + u * (d.im : ℂ)) ^ 2) / (v : ℂ))

private theorem e7T_line_eq (γ : ℂ) (p q m : ℕ) (v : ℝ) (ζ₀ d : ℂ) (x : ℝ) :
    e7T γ p q m v (ζ₀ + x * d) = e7Thol γ p q m v ζ₀ d x := by
  simp only [e7T, e7E, e7Thol, map_add, map_mul, Complex.conj_ofReal, Complex.add_re, Complex.add_im,
    Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.ofReal_add, Complex.ofReal_mul]

private noncomputable def e7Tder (γ : ℂ) (p q m : ℕ) (v : ℝ) (ζ₀ d : ℂ) : ℂ :=
  e7T (γ * p * d) (p - 1) q m v ζ₀ + e7T (γ * q * (starRingEnd ℂ) d) p (q - 1) m v ζ₀
    + e7T (γ * (-(8 * (Real.pi : ℂ) ^ 2)) * ((ζ₀.re : ℂ) * (d.re : ℂ) + (ζ₀.im : ℂ) * (d.im : ℂ)))
        p q (m + 1) v ζ₀

private theorem e7Thol_hasDerivAt (γ : ℂ) (p q m : ℕ) (v : ℝ) (ζ₀ d : ℂ) :
    HasDerivAt (fun u : ℂ => e7Thol γ p q m v ζ₀ d u) (e7Tder γ p q m v ζ₀ d) ((0 : ℝ) : ℂ) := by
  simp only [e7Thol]
  have h1 : HasDerivAt (fun u : ℂ => ζ₀ + u * d) (1 * d) ((0 : ℝ) : ℂ) :=
    ((hasDerivAt_id' _).mul_const d).const_add ζ₀
  have h2 : HasDerivAt (fun u : ℂ => (starRingEnd ℂ) ζ₀ + u * (starRingEnd ℂ) d)
      (1 * (starRingEnd ℂ) d) ((0 : ℝ) : ℂ) :=
    ((hasDerivAt_id' _).mul_const _).const_add _
  have h3 : HasDerivAt (fun u : ℂ => (ζ₀.re : ℂ) + u * (d.re : ℂ)) (1 * (d.re : ℂ)) ((0 : ℝ) : ℂ) :=
    ((hasDerivAt_id' _).mul_const _).const_add _
  have h4 : HasDerivAt (fun u : ℂ => (ζ₀.im : ℂ) + u * (d.im : ℂ)) (1 * (d.im : ℂ)) ((0 : ℝ) : ℂ) :=
    ((hasDerivAt_id' _).mul_const _).const_add _
  have hQ := (((h3.fun_pow 2).fun_add (h4.fun_pow 2)).const_mul
    (-(4 * (Real.pi : ℂ) ^ 2))).div_const (v : ℂ)
  have h := ((((h1.fun_pow p).const_mul γ).fun_mul (h2.fun_pow q)).mul_const
    ((v : ℂ) ^ (m + 1))⁻¹).fun_mul hQ.cexp
  refine h.congr_deriv ?_
  simp only [e7Tder, e7T, e7E, Complex.ofReal_zero, zero_mul, add_zero, Nat.cast_ofNat, Nat.reduceSub,
    pow_one]
  ring

private theorem e7T_line_hasDerivAt (γ : ℂ) (p q m : ℕ) (v : ℝ) (ζ₀ d : ℂ) :
    HasDerivAt (fun x : ℝ => e7T γ p q m v (ζ₀ + x * d)) (e7Tder γ p q m v ζ₀ d) 0 :=
  (e7Thol_hasDerivAt γ p q m v ζ₀ d).comp_ofReal.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x => e7T_line_eq γ p q m v ζ₀ d x)

private theorem e7T_mul_left (c γ : ℂ) {p q m : ℕ} {v : ℝ} {ζ : ℂ} :
    e7T (c * γ) p q m v ζ = c * e7T γ p q m v ζ := by
  unfold e7T
  ring

private theorem e7Tder_sub (γ : ℂ) (p q m : ℕ) (v : ℝ) (ζ₀ : ℂ) :
    e7Tder γ p q m v ζ₀ 1 - Complex.I * e7Tder γ p q m v ζ₀ Complex.I
      = e7T (γ * (2 * p)) (p - 1) q m v ζ₀
        + e7T (γ * (-(8 * (Real.pi : ℂ) ^ 2))) p (q + 1) (m + 1) v ζ₀ := by
  have hC := e7_conj_eq ζ₀
  simp only [e7Tder, e7T, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, map_one,
    Complex.conj_I, Complex.ofReal_one, Complex.ofReal_zero]
  linear_combination
    (-(γ * p) * ζ₀ ^ (p - 1) * (starRingEnd ℂ) ζ₀ ^ q * ((v : ℂ) ^ (m + 1))⁻¹ * e7E v ζ₀
        + γ * q * ζ₀ ^ p * (starRingEnd ℂ) ζ₀ ^ (q - 1) * ((v : ℂ) ^ (m + 1))⁻¹ * e7E v ζ₀)
      * Complex.I_sq
    + (8 * (Real.pi : ℂ) ^ 2 * γ * ζ₀ ^ p * (starRingEnd ℂ) ζ₀ ^ q * ((v : ℂ) ^ (m + 1 + 1))⁻¹
        * e7E v ζ₀) * hC

private theorem e7Tder_add (γ : ℂ) (p q m : ℕ) (v : ℝ) (ζ₀ : ℂ) :
    e7Tder γ p q m v ζ₀ 1 + Complex.I * e7Tder γ p q m v ζ₀ Complex.I
      = e7T (γ * (2 * q)) p (q - 1) m v ζ₀
        + e7T (γ * (-(8 * (Real.pi : ℂ) ^ 2))) (p + 1) q (m + 1) v ζ₀ := by
  have hz : ζ₀ = (ζ₀.re : ℂ) + (ζ₀.im : ℂ) * Complex.I := (Complex.re_add_im ζ₀).symm
  simp only [e7Tder, e7T, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, map_one,
    Complex.conj_I, Complex.ofReal_one, Complex.ofReal_zero]
  linear_combination
    (γ * p * ζ₀ ^ (p - 1) * (starRingEnd ℂ) ζ₀ ^ q * ((v : ℂ) ^ (m + 1))⁻¹ * e7E v ζ₀
        - γ * q * ζ₀ ^ p * (starRingEnd ℂ) ζ₀ ^ (q - 1) * ((v : ℂ) ^ (m + 1))⁻¹ * e7E v ζ₀)
      * Complex.I_sq
    + (8 * (Real.pi : ℂ) ^ 2 * γ * ζ₀ ^ p * (starRingEnd ℂ) ζ₀ ^ q * ((v : ℂ) ^ (m + 1 + 1))⁻¹
        * e7E v ζ₀) * hz

private theorem e7_family_left (a b : ℕ)
    (h : ∃ (n : ℕ) (γ : Fin n → ℂ) (p q m : Fin n → ℕ), ∀ v : ℝ, 0 < v → ∀ ζ : ℂ,
      e7G a b v ζ = ∑ i, e7T (γ i) (p i) (q i) (m i) v ζ) :
    ∃ (n : ℕ) (γ : Fin n → ℂ) (p q m : Fin n → ℕ), ∀ v : ℝ, 0 < v → ∀ ζ : ℂ,
      e7G (a + 1) b v ζ = ∑ i, e7T (γ i) (p i) (q i) (m i) v ζ := by
  obtain ⟨n, γ, p, q, m, hfam⟩ := h
  have hκ : (-(4 * (Real.pi : ℂ) * Complex.I)) ≠ 0 := by
    simp [Real.pi_ne_zero]
  refine ⟨n + n,
    Fin.append (fun i => (-(4 * (Real.pi : ℂ) * Complex.I))⁻¹ * (γ i * (2 * (p i : ℂ))))
      (fun i => (-(4 * (Real.pi : ℂ) * Complex.I))⁻¹ * (γ i * (-(8 * (Real.pi : ℂ) ^ 2)))),
    Fin.append (fun i => p i - 1) (fun i => p i),
    Fin.append (fun i => q i) (fun i => q i + 1),
    Fin.append (fun i => m i) (fun i => m i + 1), fun v hv ζ₀ => ?_⟩
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rw [← Finset.sum_add_distrib]
  have hD : ∀ d : ℂ, e7Gd a b v ζ₀ d = ∑ i, e7Tder (γ i) (p i) (q i) (m i) v ζ₀ d := by
    intro d
    have hG := e7G_hasDerivAt_line a b v hv ζ₀ d
    have hfun : (fun x : ℝ => e7G a b v (ζ₀ + x * d))
        = fun x : ℝ => ∑ i, e7T (γ i) (p i) (q i) (m i) v (ζ₀ + x * d) :=
      funext fun x => hfam v hv _
    rw [hfun] at hG
    exact hG.unique
      (HasDerivAt.fun_sum fun i _ => e7T_line_hasDerivAt (γ i) (p i) (q i) (m i) v ζ₀ d)
  have hmain : -(4 * (Real.pi : ℂ) * Complex.I) * e7G (a + 1) b v ζ₀
      = ∑ i, (e7T (γ i * (2 * (p i : ℂ))) (p i - 1) (q i) (m i) v ζ₀
          + e7T (γ i * (-(8 * (Real.pi : ℂ) ^ 2))) (p i) (q i + 1) (m i + 1) v ζ₀) := by
    rw [← e7Gd_sub a b v hv ζ₀, hD 1, hD Complex.I, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => e7Tder_sub (γ i) (p i) (q i) (m i) v ζ₀
  calc e7G (a + 1) b v ζ₀
      = (-(4 * (Real.pi : ℂ) * Complex.I))⁻¹
          * (-(4 * (Real.pi : ℂ) * Complex.I) * e7G (a + 1) b v ζ₀) := by
        rw [← mul_assoc, inv_mul_cancel₀ hκ, one_mul]
    _ = ∑ i, (e7T ((-(4 * (Real.pi : ℂ) * Complex.I))⁻¹ * (γ i * (2 * (p i : ℂ))))
            (p i - 1) (q i) (m i) v ζ₀
          + e7T ((-(4 * (Real.pi : ℂ) * Complex.I))⁻¹ * (γ i * (-(8 * (Real.pi : ℂ) ^ 2))))
            (p i) (q i + 1) (m i + 1) v ζ₀) := by
        rw [hmain, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_add, ← e7T_mul_left (-(4 * (Real.pi : ℂ) * Complex.I))⁻¹ (γ i * (2 * (p i : ℂ))),
          ← e7T_mul_left (-(4 * (Real.pi : ℂ) * Complex.I))⁻¹ (γ i * (-(8 * (Real.pi : ℂ) ^ 2)))]

private theorem e7_family_right (a b : ℕ)
    (h : ∃ (n : ℕ) (γ : Fin n → ℂ) (p q m : Fin n → ℕ), ∀ v : ℝ, 0 < v → ∀ ζ : ℂ,
      e7G a b v ζ = ∑ i, e7T (γ i) (p i) (q i) (m i) v ζ) :
    ∃ (n : ℕ) (γ : Fin n → ℂ) (p q m : Fin n → ℕ), ∀ v : ℝ, 0 < v → ∀ ζ : ℂ,
      e7G a (b + 1) v ζ = ∑ i, e7T (γ i) (p i) (q i) (m i) v ζ := by
  obtain ⟨n, γ, p, q, m, hfam⟩ := h
  have hκ : (-(4 * (Real.pi : ℂ) * Complex.I)) ≠ 0 := by
    simp [Real.pi_ne_zero]
  refine ⟨n + n,
    Fin.append (fun i => (-(4 * (Real.pi : ℂ) * Complex.I))⁻¹ * (γ i * (2 * (q i : ℂ))))
      (fun i => (-(4 * (Real.pi : ℂ) * Complex.I))⁻¹ * (γ i * (-(8 * (Real.pi : ℂ) ^ 2)))),
    Fin.append (fun i => p i) (fun i => p i + 1),
    Fin.append (fun i => q i - 1) (fun i => q i),
    Fin.append (fun i => m i) (fun i => m i + 1), fun v hv ζ₀ => ?_⟩
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rw [← Finset.sum_add_distrib]
  have hD : ∀ d : ℂ, e7Gd a b v ζ₀ d = ∑ i, e7Tder (γ i) (p i) (q i) (m i) v ζ₀ d := by
    intro d
    have hG := e7G_hasDerivAt_line a b v hv ζ₀ d
    have hfun : (fun x : ℝ => e7G a b v (ζ₀ + x * d))
        = fun x : ℝ => ∑ i, e7T (γ i) (p i) (q i) (m i) v (ζ₀ + x * d) :=
      funext fun x => hfam v hv _
    rw [hfun] at hG
    exact hG.unique
      (HasDerivAt.fun_sum fun i _ => e7T_line_hasDerivAt (γ i) (p i) (q i) (m i) v ζ₀ d)
  have hmain : -(4 * (Real.pi : ℂ) * Complex.I) * e7G a (b + 1) v ζ₀
      = ∑ i, (e7T (γ i * (2 * (q i : ℂ))) (p i) (q i - 1) (m i) v ζ₀
          + e7T (γ i * (-(8 * (Real.pi : ℂ) ^ 2))) (p i + 1) (q i) (m i + 1) v ζ₀) := by
    rw [← e7Gd_add a b v hv ζ₀, hD 1, hD Complex.I, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => e7Tder_add (γ i) (p i) (q i) (m i) v ζ₀
  calc e7G a (b + 1) v ζ₀
      = (-(4 * (Real.pi : ℂ) * Complex.I))⁻¹
          * (-(4 * (Real.pi : ℂ) * Complex.I) * e7G a (b + 1) v ζ₀) := by
        rw [← mul_assoc, inv_mul_cancel₀ hκ, one_mul]
    _ = ∑ i, (e7T ((-(4 * (Real.pi : ℂ) * Complex.I))⁻¹ * (γ i * (2 * (q i : ℂ))))
            (p i) (q i - 1) (m i) v ζ₀
          + e7T ((-(4 * (Real.pi : ℂ) * Complex.I))⁻¹ * (γ i * (-(8 * (Real.pi : ℂ) ^ 2))))
            (p i + 1) (q i) (m i + 1) v ζ₀) := by
        rw [hmain, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_add, ← e7T_mul_left (-(4 * (Real.pi : ℂ) * Complex.I))⁻¹ (γ i * (2 * (q i : ℂ))),
          ← e7T_mul_left (-(4 * (Real.pi : ℂ) * Complex.I))⁻¹ (γ i * (-(8 * (Real.pi : ℂ) ^ 2)))]

private theorem e7_family_zero_zero :
    ∃ (n : ℕ) (γ : Fin n → ℂ) (p q m : Fin n → ℕ), ∀ v : ℝ, 0 < v → ∀ ζ : ℂ,
      e7G 0 0 v ζ = ∑ i, e7T (γ i) (p i) (q i) (m i) v ζ :=
  ⟨1, fun _ => (Real.pi : ℂ), fun _ => 0, fun _ => 0, fun _ => 0, fun v hv ζ => by
    rw [Fin.sum_univ_one, e7G_zero_zero v hv ζ]⟩

private theorem e7_family_zero (b : ℕ) :
    ∃ (n : ℕ) (γ : Fin n → ℂ) (p q m : Fin n → ℕ), ∀ v : ℝ, 0 < v → ∀ ζ : ℂ,
      e7G 0 b v ζ = ∑ i, e7T (γ i) (p i) (q i) (m i) v ζ := by
  induction b with
  | zero => exact e7_family_zero_zero
  | succ b ih => exact e7_family_right 0 b ih

private theorem e7_family (a b : ℕ) :
    ∃ (n : ℕ) (γ : Fin n → ℂ) (p q m : Fin n → ℕ), ∀ v : ℝ, 0 < v → ∀ ζ : ℂ,
      e7G a b v ζ = ∑ i, e7T (γ i) (p i) (q i) (m i) v ζ := by
  induction a with
  | zero => exact e7_family_zero b
  | succ a ih => exact e7_family_left a b ih

private theorem e7_norm_pow_le (z : ℂ) (n : ℕ) : ‖z‖ ^ n ≤ (1 + ‖z‖ ^ 2) ^ ((n : ℝ) / 2) := by
  have h1 : ‖z‖ ^ n = (‖z‖ ^ 2) ^ ((n : ℝ) / 2) := by
    rw [← Real.rpow_natCast ‖z‖ n, ← Real.rpow_natCast ‖z‖ 2, ← Real.rpow_mul (norm_nonneg z)]
    congr 1
    push_cast
    ring
  rw [h1]
  exact Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)

private theorem e7_majorant_integrable (n : ℕ) (σ : ℝ) (hσ : (n : ℝ) / 2 + 1 < σ) :
    Integrable (fun z : ℂ => ‖z‖ ^ n * (1 + ‖z‖ ^ 2) ^ (-σ)) := by
  have hnr : (Module.finrank ℝ ℂ : ℝ) < 2 * σ - n := by
    rw [Complex.finrank_real_complex]
    push_cast
    linarith
  refine (integrable_rpow_neg_one_add_norm_sq hnr).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact (by fun_prop : Measurable fun z : ℂ => ‖z‖ ^ n * (1 + ‖z‖ ^ 2) ^ (-σ)).aestronglyMeasurable
  · have hpos : 0 < 1 + ‖z‖ ^ 2 := by positivity
    rw [Real.norm_of_nonneg (by positivity)]
    calc ‖z‖ ^ n * (1 + ‖z‖ ^ 2) ^ (-σ)
        ≤ (1 + ‖z‖ ^ 2) ^ ((n : ℝ) / 2) * (1 + ‖z‖ ^ 2) ^ (-σ) :=
          mul_le_mul_of_nonneg_right (e7_norm_pow_le z n) (by positivity)
      _ = (1 + ‖z‖ ^ 2) ^ (-(2 * σ - n) / 2) := by
          rw [← Real.rpow_add hpos]
          congr 1
          ring

private theorem e7_norm_char (ζ z : ℂ) : ‖Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))‖ = 1 := by
  rw [← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]

private theorem e7_laplace (X : ℝ) (hX : 0 < X) (w : ℂ) (hw : 0 < w.re) :
    ((X : ℂ)) ^ (-w) * Complex.Gamma w
      = ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (w - 1) * Complex.exp (-((X : ℂ) * v)) := by
  have harg : ((X : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hX.le]
    exact Real.pi_ne_zero.symm
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi hw hX, one_div, Complex.inv_cpow _ _ harg,
    Complex.cpow_neg]

private theorem e7_laplaceKernel_integrableOn_real (X σ : ℝ) (hX : 0 < X) (hσ : 0 < σ) :
    IntegrableOn (fun v : ℝ => v ^ (σ - 1) * Real.exp (-(X * v))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := σ - 1) (p := 1) (b := X)
    (by linarith) one_pos hX
  refine h.congr_fun (fun v _ => ?_) measurableSet_Ioi
  dsimp only
  rw [Real.rpow_one, neg_mul]

private theorem e7_laplaceKernel_integrableOn (X : ℝ) (hX : 0 < X) (w : ℂ) (hw : 0 < w.re) :
    IntegrableOn (fun v : ℝ => (v : ℂ) ^ (w - 1) * Complex.exp (-((X : ℂ) * v))) (Ioi 0) := by
  refine Integrable.mono' (e7_laplaceKernel_integrableOn_real X w.re hX hw) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun v hv => ?_) measurableSet_Ioi
    exact (ContinuousAt.mul
      (ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const
        (Complex.ofReal_mem_slitPlane.mpr (mem_Ioi.mp hv)))
      (Complex.continuous_exp.comp (by fun_prop)).continuousAt).continuousWithinAt
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun v hv => le_of_eq ?_
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (mem_Ioi.mp hv), Complex.sub_re,
      Complex.one_re, Complex.norm_exp, Complex.neg_re, ← Complex.ofReal_mul, Complex.ofReal_re]

private theorem e7_joint_integrable (a b : ℕ) (w ζ : ℂ) (hw : ((a + b : ℕ) : ℝ) / 2 + 1 < w.re) :
    Integrable (Function.uncurry fun (z : ℂ) (v : ℝ) =>
        z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)) * ((v : ℂ) ^ (w - 1) * Complex.exp (-(((1 + ‖z‖ ^ 2 : ℝ) : ℂ) * v))))
      ((volume : Measure ℂ).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hσ : 0 < w.re := by
    have h0 : (0 : ℝ) ≤ ((a + b : ℕ) : ℝ) / 2 := by positivity
    linarith

  have hmeas : AEStronglyMeasurable (Function.uncurry fun (z : ℂ) (v : ℝ) =>
        z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)) * ((v : ℂ) ^ (w - 1) * Complex.exp (-(((1 + ‖z‖ ^ 2 : ℝ) : ℂ) * v))))
      ((volume : Measure ℂ).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hc : ContinuousOn (fun p : ℂ × ℝ =>
        p.1 ^ a * (starRingEnd ℂ) p.1 ^ b * Complex.exp (-(((4 * Real.pi * (ζ * p.1).re : ℝ) : ℂ) * Complex.I)) * ((p.2 : ℂ) ^ (w - 1) * Complex.exp (-(((1 + ‖p.1‖ ^ 2 : ℝ) : ℂ) * p.2)))) (univ ×ˢ Ioi (0 : ℝ)) := by
      refine ContinuousOn.mul (Continuous.continuousOn ?_)
        (ContinuousOn.mul ?_ (Continuous.continuousOn ?_))
      · exact ((continuous_fst.pow a).mul
          ((Complex.continuous_conj.comp continuous_fst).pow b)).mul
          (Complex.continuous_exp.comp (by fun_prop))
      · intro p hp
        exact (ContinuousAt.cpow (Complex.continuous_ofReal.comp continuous_snd).continuousAt
          continuousAt_const
          (Complex.ofReal_mem_slitPlane.mpr (mem_Ioi.mp (Set.mem_prod.mp hp).2))).continuousWithinAt
      · exact Complex.continuous_exp.comp (by fun_prop)
    have h := hc.aestronglyMeasurable (μ := (volume : Measure ℂ).prod (volume : Measure ℝ))
      (MeasurableSet.univ.prod measurableSet_Ioi)
    rw [← Measure.prod_restrict, Measure.restrict_univ] at h
    exact h

  have h5 : ∀ z : ℂ, ∫ v in Ioi (0 : ℝ), ‖z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)) * ((v : ℂ) ^ (w - 1) * Complex.exp (-(((1 + ‖z‖ ^ 2 : ℝ) : ℂ) * v)))‖
      = Real.Gamma w.re * (‖z‖ ^ (a + b) * (1 + ‖z‖ ^ 2) ^ (-w.re)) := by
    intro z
    have hX : 0 < 1 + ‖z‖ ^ 2 := by positivity
    have hnorm : ∀ v ∈ Ioi (0 : ℝ), ‖z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)) * ((v : ℂ) ^ (w - 1) * Complex.exp (-(((1 + ‖z‖ ^ 2 : ℝ) : ℂ) * v)))‖
        = ‖z‖ ^ (a + b) * (v ^ (w.re - 1) * Real.exp (-((1 + ‖z‖ ^ 2) * v))) := by
      intro v hv
      rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, e7_norm_char ζ z,
        mul_one, ← pow_add, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (mem_Ioi.mp hv),
        Complex.sub_re, Complex.one_re, Complex.norm_exp, Complex.neg_re, ← Complex.ofReal_mul,
        Complex.ofReal_re]
    rw [setIntegral_congr_fun measurableSet_Ioi hnorm, integral_const_mul,
      Real.integral_rpow_mul_exp_neg_mul_Ioi hσ hX, one_div, Real.inv_rpow hX.le,
      ← Real.rpow_neg hX.le]
    ring
  rw [integrable_prod_iff hmeas]
  refine ⟨Filter.Eventually.of_forall fun z => ?_, ?_⟩
  · show Integrable (fun v : ℝ => z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))
        * ((v : ℂ) ^ (w - 1) * Complex.exp (-(((1 + ‖z‖ ^ 2 : ℝ) : ℂ) * v)))) (volume.restrict (Ioi (0 : ℝ)))
    exact Integrable.const_mul (e7_laplaceKernel_integrableOn (1 + ‖z‖ ^ 2) (by positivity) w hσ)
      (z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)))
  · exact ((e7_majorant_integrable (a + b) w.re hw).const_mul (Real.Gamma w.re)).congr
      (Filter.Eventually.of_forall fun z => (h5 z).symm)

private theorem e7_transform_eq_laplace (a b : ℕ) (w ζ : ℂ)
    (hw : ((a + b : ℕ) : ℝ) / 2 + 1 < w.re) :
    Complex.Gamma w * (∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)))
      = ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (w - 1) * Complex.exp (-(v : ℂ)) *
          ∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
            * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)) := by
  have hσ : 0 < w.re := by
    have h0 : (0 : ℝ) ≤ ((a + b : ℕ) : ℝ) / 2 := by positivity
    linarith

  have h1 : ∀ z : ℂ, Complex.Gamma w * (z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
        * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)))
      = ∫ v in Ioi (0 : ℝ), z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)) * ((v : ℂ) ^ (w - 1) * Complex.exp (-(((1 + ‖z‖ ^ 2 : ℝ) : ℂ) * v))) := by
    intro z
    rw [integral_const_mul, ← e7_laplace (1 + ‖z‖ ^ 2) (by positivity) w hσ]
    ring

  have h2 : ∀ v : ℝ, (∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)) * ((v : ℂ) ^ (w - 1) * Complex.exp (-(((1 + ‖z‖ ^ 2 : ℝ) : ℂ) * v))))
      = (v : ℂ) ^ (w - 1) * Complex.exp (-(v : ℂ)) *
          ∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
            * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)) := by
    intro v
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)) * ((v : ℂ) ^ (w - 1) * Complex.exp (-(((1 + ‖z‖ ^ 2 : ℝ) : ℂ) * v)))
      = (v : ℂ) ^ (w - 1) * Complex.exp (-(v : ℂ)) *
          (z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
            * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)))
    have hsplit : Complex.exp (-(((1 + ‖z‖ ^ 2 : ℝ) : ℂ) * v))
        = Complex.exp (-(v : ℂ)) * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hsplit]
    ring
  calc Complex.Gamma w * (∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)))
      = ∫ z : ℂ, Complex.Gamma w * (z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))) := (integral_const_mul _ _).symm
    _ = ∫ z : ℂ, ∫ v in Ioi (0 : ℝ), z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)) * ((v : ℂ) ^ (w - 1) * Complex.exp (-(((1 + ‖z‖ ^ 2 : ℝ) : ℂ) * v))) :=
          integral_congr_ae (Filter.Eventually.of_forall h1)
    _ = ∫ v in Ioi (0 : ℝ), ∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)) * ((v : ℂ) ^ (w - 1) * Complex.exp (-(((1 + ‖z‖ ^ 2 : ℝ) : ℂ) * v))) :=
          integral_integral_swap (e7_joint_integrable a b w ζ hw)
    _ = ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (w - 1) * Complex.exp (-(v : ℂ)) *
          ∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
            * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)) :=
          integral_congr_ae (Filter.Eventually.of_forall h2)

private theorem e7_re_sq_add_im_sq (ζ : ℂ) :
    ((ζ.re : ℝ) : ℂ) ^ 2 + ((ζ.im : ℝ) : ℂ) ^ 2 = ((‖ζ‖ : ℝ) : ℂ) ^ 2 := by
  have h : ‖ζ‖ ^ 2 = ζ.re ^ 2 + ζ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  exact_mod_cast h.symm

private theorem e7_expKernel_integrableOn_real (σ t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun u : ℝ => u ^ σ * Real.exp (-(u + t / u))) (Ioi 0) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (-1 - σ)
  have hg : IntegrableOn
      (fun u : ℝ => (Nat.factorial N : ℝ) / t ^ N * (u ^ (σ + N) * Real.exp (-u))) (Ioi 0) := by
    refine Integrable.const_mul ?_ _
    have h := Real.GammaIntegral_convergent (s := σ + N + 1) (by linarith)
    refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
    show Real.exp (-u) * u ^ (σ + N + 1 - 1) = u ^ (σ + N) * Real.exp (-u)
    rw [add_sub_cancel_right, mul_comm]
  refine Integrable.mono' hg ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun u hu => ?_) measurableSet_Ioi
    have hu : 0 < u := mem_Ioi.mp hu
    have h1 : ContinuousAt (fun u : ℝ => -(u + t / u)) u := by fun_prop (disch := exact hu.ne')
    exact ((Real.continuousAt_rpow_const u σ (Or.inl hu.ne')).mul
      (Real.continuous_exp.continuousAt.comp h1)).continuousWithinAt
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun u hu => ?_
    have hu : 0 < u := mem_Ioi.mp hu
    have hx : 0 < t / u := div_pos ht hu
    have hbound : Real.exp (-(t / u)) ≤ (Nat.factorial N : ℝ) * u ^ N / t ^ N := by
      calc Real.exp (-(t / u)) = (Real.exp (t / u))⁻¹ := Real.exp_neg _
        _ ≤ ((t / u) ^ N / (Nat.factorial N : ℝ))⁻¹ :=
            inv_anti₀ (by positivity) (Real.pow_div_factorial_le_exp (t / u) hx.le N)
        _ = (Nat.factorial N : ℝ) * u ^ N / t ^ N := by
            rw [inv_div, div_pow, div_div_eq_mul_div]
    show ‖u ^ σ * Real.exp (-(u + t / u))‖
      ≤ (Nat.factorial N : ℝ) / t ^ N * (u ^ (σ + N) * Real.exp (-u))
    calc ‖u ^ σ * Real.exp (-(u + t / u))‖ = u ^ σ * Real.exp (-u) * Real.exp (-(t / u)) := by
          rw [Real.norm_of_nonneg (by positivity), neg_add, Real.exp_add, mul_assoc]
      _ ≤ u ^ σ * Real.exp (-u) * ((Nat.factorial N : ℝ) * u ^ N / t ^ N) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = (Nat.factorial N : ℝ) / t ^ N * (u ^ (σ + N) * Real.exp (-u)) := by
          rw [Real.rpow_add_natCast hu.ne']
          ring

private theorem e7_archKernel_integrableOn (z : ℂ) (r : ℝ) (hr : r ≠ 0) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ z
      * Complex.exp (-(1 : ℂ) * ((u : ℂ) + (r : ℂ) ^ 2 / (u : ℂ)))) (Ioi 0) := by
  refine Integrable.mono' (e7_expKernel_integrableOn_real z.re (r ^ 2) (by positivity)) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun u hu => ?_) measurableSet_Ioi
    have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (mem_Ioi.mp hu))
    have h1 : ContinuousAt (fun u : ℝ => -(1 : ℂ) * ((u : ℂ) + (r : ℂ) ^ 2 / (u : ℂ))) u := by
      fun_prop (disch := exact hu0)
    exact (ContinuousAt.mul
      (ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const
        (Complex.ofReal_mem_slitPlane.mpr (mem_Ioi.mp hu)))
      (Complex.continuous_exp.continuousAt.comp h1)).continuousWithinAt
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun u hu => le_of_eq ?_
    have hu : 0 < u := mem_Ioi.mp hu
    have hcast : -(1 : ℂ) * ((u : ℂ) + (r : ℂ) ^ 2 / (u : ℂ)) = ((-(u + r ^ 2 / u) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, hcast, Complex.norm_exp_ofReal]

private theorem e7_head_of_family (a b : ℕ)
    (hfam : ∃ (n : ℕ) (γ : Fin n → ℂ) (p q m : Fin n → ℕ), ∀ v : ℝ, 0 < v → ∀ ζ : ℂ,
      e7G a b v ζ = ∑ i, e7T (γ i) (p i) (q i) (m i) v ζ) :
    ∃ J : ℂ → ℂ → ℂ,
      (∀ ζ : ℂ, ζ ≠ 0 → Differentiable ℂ (fun w : ℂ => J w ζ)) ∧
      (∀ (w ζ : ℂ), ((a + b : ℕ) : ℝ) / 2 + 1 < w.re → ζ ≠ 0 →
        J w ζ = ∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))) ∧
      (∀ R : ℝ, ∃ C c' : ℝ, ∃ N : ℕ, 0 < C ∧ 0 < c' ∧ ∀ (w ζ : ℂ), ‖w‖ ≤ R → ζ ≠ 0 →
        ‖J w ζ‖ ≤ C * max 1 (‖ζ‖ ^ (-(N : ℝ))) * Real.exp (-c' * ‖ζ‖)) := by
  obtain ⟨n, γ, p, q, m, hfam⟩ := hfam

  have ha : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      Differentiable ℂ ((fun (i : Fin n) (w : ℂ) => γ i * (Complex.Gamma w)⁻¹) i) :=
    fun i _ => Complex.differentiable_one_div_Gamma.const_mul (γ i)

  have hβ : ∀ ζ : ℂ, ∀ i ∈ (Finset.univ : Finset (Fin n)),
      ‖ζ ^ p i * (starRingEnd ℂ) ζ ^ q i / ((2 * Real.pi * ‖ζ‖ : ℝ) : ℂ) ^ (p i + q i)‖ ≤ 1 := by
    intro ζ i _
    have hle : ‖ζ‖ ≤ 2 * Real.pi * ‖ζ‖ := by nlinarith [Real.two_le_pi, norm_nonneg ζ]
    rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_conj, ← pow_add, norm_pow,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi * ‖ζ‖)]
    exact div_le_one_of_le₀ (pow_le_pow_left₀ (norm_nonneg _) hle _) (by positivity)
  refine ⟨fun w ζ => ∑ i : Fin n, (γ i * (Complex.Gamma w)⁻¹)
      * (ζ ^ p i * (starRingEnd ℂ) ζ ^ q i / ((2 * Real.pi * ‖ζ‖ : ℝ) : ℂ) ^ (p i + q i))
      * ((2 * Real.pi * ‖ζ‖ : ℝ) : ℂ) ^ (p i + q i)
      * ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (w + (-2 - (m i : ℂ))) * Complex.exp (-(1 : ℂ) * ((u : ℂ) + ((2 * Real.pi * ‖ζ‖ : ℝ) : ℂ) ^ 2 / (u : ℂ))),
    fun ζ hζ => ?_, fun w ζ hw hζ => ?_, fun R => ?_⟩
  ·
    have hr : 2 * Real.pi * ‖ζ‖ ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (norm_ne_zero_iff.mpr hζ)
    try dsimp only
    exact differentiable_sum_archIntegral (Finset.univ : Finset (Fin n))
      (fun (i : Fin n) (w : ℂ) => γ i * (Complex.Gamma w)⁻¹) ha
      (fun i => ζ ^ p i * (starRingEnd ℂ) ζ ^ q i / ((2 * Real.pi * ‖ζ‖ : ℝ) : ℂ) ^ (p i + q i))
      (fun i => -2 - (m i : ℂ)) (fun i => p i + q i) 1 (by norm_num) (2 * Real.pi * ‖ζ‖) hr
  ·
    have hσ : 0 < w.re := by
      have h0 : (0 : ℝ) ≤ ((a + b : ℕ) : ℝ) / 2 := by positivity
      linarith
    have hΓ : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hσ
    have hr : 2 * Real.pi * ‖ζ‖ ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (norm_ne_zero_iff.mpr hζ)
    have hrC : ((2 * Real.pi * ‖ζ‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr

    have hterm : ∀ i : Fin n, ∀ v ∈ Ioi (0 : ℝ),
        (v : ℂ) ^ (w - 1) * Complex.exp (-(v : ℂ)) * e7T (γ i) (p i) (q i) (m i) v ζ
          = (γ i * ζ ^ p i * (starRingEnd ℂ) ζ ^ q i)
            * ((v : ℂ) ^ (w + (-2 - (m i : ℂ))) * Complex.exp (-(1 : ℂ) * ((v : ℂ) + ((2 * Real.pi * ‖ζ‖ : ℝ) : ℂ) ^ 2 / (v : ℂ)))) := by
      intro i v hv
      have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (mem_Ioi.mp hv))
      have hpow : (v : ℂ) ^ (w - 1) * ((v : ℂ) ^ (m i + 1))⁻¹ = (v : ℂ) ^ (w + (-2 - (m i : ℂ))) := by
        rw [← Complex.cpow_natCast, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hv0]
        congr 1
        push_cast
        ring
      have hexp : Complex.exp (-(v : ℂ)) * e7E v ζ
          = Complex.exp (-(1 : ℂ) * ((v : ℂ) + ((2 * Real.pi * ‖ζ‖ : ℝ) : ℂ) ^ 2 / (v : ℂ))) := by
        rw [e7E, ← Complex.exp_add]
        congr 1
        rw [e7_re_sq_add_im_sq ζ]
        push_cast
        ring
      rw [e7T]
      calc _ = (γ i * ζ ^ p i * (starRingEnd ℂ) ζ ^ q i)
            * (((v : ℂ) ^ (w - 1) * ((v : ℂ) ^ (m i + 1))⁻¹) * (Complex.exp (-(v : ℂ)) * e7E v ζ)) := by
              ring
        _ = _ := by rw [hpow, hexp]

    have hint : ∀ i : Fin n, IntegrableOn (fun v : ℝ =>
        (v : ℂ) ^ (w - 1) * Complex.exp (-(v : ℂ)) * e7T (γ i) (p i) (q i) (m i) v ζ) (Ioi 0) :=
      fun i => IntegrableOn.congr_fun
        (Integrable.const_mul (e7_archKernel_integrableOn (w + (-2 - (m i : ℂ))) (2 * Real.pi * ‖ζ‖) hr)
          (γ i * ζ ^ p i * (starRingEnd ℂ) ζ ^ q i))
        (fun v hv => (hterm i v hv).symm) measurableSet_Ioi

    have hG : ∀ v ∈ Ioi (0 : ℝ),
        (v : ℂ) ^ (w - 1) * Complex.exp (-(v : ℂ)) *
            (∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
              * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)))
          = ∑ i, (v : ℂ) ^ (w - 1) * Complex.exp (-(v : ℂ)) * e7T (γ i) (p i) (q i) (m i) v ζ := by
      intro v hv
      have hfam' := hfam v (mem_Ioi.mp hv) ζ
      simp only [e7G] at hfam'
      rw [hfam', Finset.mul_sum]
    have hI : ∀ i : Fin n,
        (∫ v in Ioi (0 : ℝ),
            (v : ℂ) ^ (w - 1) * Complex.exp (-(v : ℂ)) * e7T (γ i) (p i) (q i) (m i) v ζ)
          = (γ i * ζ ^ p i * (starRingEnd ℂ) ζ ^ q i)
            * ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (w + (-2 - (m i : ℂ))) * Complex.exp (-(1 : ℂ) * ((v : ℂ) + ((2 * Real.pi * ‖ζ‖ : ℝ) : ℂ) ^ 2 / (v : ℂ))) := by
      intro i
      rw [setIntegral_congr_fun measurableSet_Ioi (hterm i), integral_const_mul]
    try dsimp only
    apply mul_left_cancel₀ hΓ
    rw [e7_transform_eq_laplace a b w ζ hw, setIntegral_congr_fun measurableSet_Ioi hG,
      integral_finsetSum _ (fun i _ => hint i), Finset.sum_congr rfl (fun i _ => hI i),
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← mul_div_assoc, div_mul_cancel₀ _ (pow_ne_zero _ hrC)]
    calc _ = (Complex.Gamma w * (Complex.Gamma w)⁻¹) * (γ i * (ζ ^ p i * (starRingEnd ℂ) ζ ^ q i)
            * ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (w + (-2 - (m i : ℂ))) * Complex.exp (-(1 : ℂ) * ((v : ℂ) + ((2 * Real.pi * ‖ζ‖ : ℝ) : ℂ) ^ 2 / (v : ℂ)))) := by
          ring
      _ = _ := by
          rw [mul_inv_cancel₀ hΓ]
          ring
  ·
    obtain ⟨C, c', N, hC, hc', hB⟩ := exists_norm_sum_archIntegral_le
      (Finset.univ : Finset (Fin n)) (fun (i : Fin n) (w : ℂ) => γ i * (Complex.Gamma w)⁻¹) ha
      (fun i => -2 - (m i : ℂ)) (fun i => p i + q i) 1 (by norm_num) R
    refine ⟨C, 2 * Real.pi * c', N, hC, by positivity, fun w ζ hwR hζ => ?_⟩
    have hr : 2 * Real.pi * ‖ζ‖ ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (norm_ne_zero_iff.mpr hζ)
    have h := hB (fun i => ζ ^ p i * (starRingEnd ℂ) ζ ^ q i
        / ((2 * Real.pi * ‖ζ‖ : ℝ) : ℂ) ^ (p i + q i)) (hβ ζ) w (2 * Real.pi * ‖ζ‖) hwR hr
    try dsimp only
    refine h.trans ?_
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi * ‖ζ‖)]
    have hmax : max 1 ((2 * Real.pi * ‖ζ‖) ^ (-(N : ℝ))) ≤ max 1 (‖ζ‖ ^ (-(N : ℝ))) := by
      refine max_le_max le_rfl ?_
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 * Real.pi * ‖ζ‖), Real.rpow_neg (norm_nonneg ζ)]
      refine inv_anti₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr hζ) _) ?_
      exact Real.rpow_le_rpow (norm_nonneg ζ) (by nlinarith [Real.two_le_pi, norm_nonneg ζ])
        (Nat.cast_nonneg N)
    have hexp : Real.exp (-c' * (2 * Real.pi * ‖ζ‖)) = Real.exp (-(2 * Real.pi * c') * ‖ζ‖) := by
      congr 1
      ring
    rw [hexp]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax hC.le) (Real.exp_pos _).le

end EgenArch

theorem solution (a b : ℕ) :
    ∃ J : ℂ → ℂ → ℂ,
      (∀ ζ : ℂ, ζ ≠ 0 → Differentiable ℂ (fun w : ℂ => J w ζ)) ∧
      (∀ (w ζ : ℂ), ((a + b : ℕ) : ℝ) / 2 + 1 < w.re → ζ ≠ 0 →
        J w ζ = ∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))) ∧
      (∀ R : ℝ, ∃ C c' : ℝ, ∃ N : ℕ, 0 < C ∧ 0 < c' ∧ ∀ (w ζ : ℂ), ‖w‖ ≤ R → ζ ≠ 0 →
        ‖J w ζ‖ ≤ C * max 1 (‖ζ‖ ^ (-(N : ℝ))) * Real.exp (-c' * ‖ζ‖)) := by
  exact EgenArch.e7_head_of_family a b (EgenArch.e7_family a b)

#print axioms solution

end S_EisensteinGeneral_Arch_exists_complexKType
end P2MW
export P2MW.S_EisensteinGeneral_Arch_exists_complexKType (solution)
