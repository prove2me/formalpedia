-- Prove2me | solution 1 for FractionalCalc.laplace_rlIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-11-24T02:17:00.948807+00:00
-- url     : https://prove2.me/submissions/18bb46e2-2935-4f0a-ad00-1515fdb6a616

import Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftMellinIntegral
import Definitions.Def_FractionalCalc_rlIntegral
import Definitions.Def_QueueingFundamentals_Transient_laplace

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open QueueingFundamentals.Transient

namespace FractionalCalc.LaplaceIntegralProof

def weighted (f : ℝ → ℝ) (s : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-s * (t : ℂ)) * (f t : ℂ)

theorem weighted_norm (f : ℝ → ℝ) (s : ℂ) (t : ℝ) :
    ‖weighted f s t‖ = Real.exp (-s.re * t) * |f t| := by
  simp only [weighted, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.norm_real, Real.norm_eq_abs]

theorem weighted_continuousOn (f : ℝ → ℝ) (s : ℂ) (A : Set ℝ)
    (hf : ContinuousOn f A) : ContinuousOn (weighted f s) A := by
  unfold weighted
  exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn.mul
    (Complex.continuous_ofReal.comp_continuousOn hf)

/-- The original continuity and exponential-order hypotheses really imply
integrability of the complex Laplace input. -/
theorem weighted_integrable_of_exponentialOrder (α : ℝ) (f : ℝ → ℝ) (s : ℂ)
    (hf : ContinuousOn f (Ici 0))
    (hexp : ∃ M T : ℝ, 0 < M ∧ 0 < T ∧
      ∀ t ≥ T, |f t| ≤ M * Real.exp (α * t))
    (hsα : α < s.re) : IntegrableOn (weighted f s) (Ioi 0) := by
  obtain ⟨M, T, _hM, _hT, hbound⟩ := hexp
  have hO : weighted f s =O[atTop] (fun t : ℝ => Real.exp ((α - s.re) * t)) := by
    apply Asymptotics.IsBigO.of_bound M
    filter_upwards [eventually_ge_atTop T] with t ht
    rw [weighted_norm]
    calc
      _ ≤ Real.exp (-s.re * t) * (M * Real.exp (α * t)) :=
        mul_le_mul_of_nonneg_left (hbound t ht) (Real.exp_pos _).le
      _ = M * (Real.exp (-s.re * t) * Real.exp (α * t)) := by ring
      _ = M * Real.exp ((α - s.re) * t) := by
        rw [← Real.exp_add]
        congr 2
        ring
      _ = _ := by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hlocal : LocallyIntegrableOn (weighted f s) (Ici 0) :=
    (weighted_continuousOn f s _ hf).locallyIntegrableOn measurableSet_Ici
  have htail : IntegrableAtFilter (fun t : ℝ => Real.exp ((α - s.re) * t)) atTop volume :=
    ⟨Ioi 0, Ioi_mem_atTop 0, integrableOn_exp_mul_Ioi (by linarith) 0⟩
  exact (hlocal.integrableOn_of_isBigO_atTop hO htail).mono_set Ioi_subset_Ici_self

/-- The fractional memory kernel has an integrable exponential weight for every
positive order, including the singular range below one. -/
theorem weighted_kernel_integrable (ν : ℝ) (s : ℂ) (hν : 0 < ν) (hs : 0 < s.re) :
    IntegrableOn (weighted (fun t : ℝ => t ^ (ν - 1)) s) (Ioi 0) := by
  have hpower : ContinuousOn (fun t : ℝ => t ^ (ν - 1)) (Ioi 0) := by
    intro t ht
    exact (Real.continuousAt_rpow_const t (ν - 1) (Or.inl (ne_of_gt ht))).continuousWithinAt
  have hm : AEStronglyMeasurable (weighted (fun t : ℝ => t ^ (ν - 1)) s)
      (volume.restrict (Ioi 0)) :=
    (weighted_continuousOn _ s _ hpower).aestronglyMeasurable measurableSet_Ioi
  have hbase : IntegrableOn (fun t : ℝ => t ^ (ν - 1) * Real.exp (-s.re * t)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := ν - 1) (p := 1) (b := s.re)
        (by linarith) zero_lt_one hs)
  apply hbase.mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [weighted_norm, abs_of_pos (Real.rpow_pos_of_pos ht _)]
  exact le_of_eq (mul_comm _ _)

/-- Exponential weights factor over the two time intervals of a causal convolution. -/
theorem weighted_product (f g : ℝ → ℝ) (s : ℂ) (t u : ℝ) :
    weighted f s u * weighted g s (t - u) =
      Complex.exp (-s * (t : ℂ)) * ((f u * g (t - u) : ℝ) : ℂ) := by
  have hexp : -s * (u : ℂ) + -s * ((t - u : ℝ) : ℂ) = -s * (t : ℂ) := by
    push_cast
    ring
  unfold weighted
  calc
    _ = (Complex.exp (-s * (u : ℂ)) * Complex.exp (-s * ((t - u : ℝ) : ℂ))) *
        ((f u : ℂ) * (g (t - u) : ℂ)) := by ring
    _ = _ := by rw [← Complex.exp_add, hexp, Complex.ofReal_mul]

/-- Moving the exponential into the actual one-sided integral is valid without
replacing the continuum kernel by a discrete or finite approximation. -/
theorem weighted_inner (f g : ℝ → ℝ) (s : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    Complex.exp (-s * (t : ℂ)) * ((∫ u in Ioo 0 t, f u * g (t - u) : ℝ) : ℂ) =
      ∫ u in (0 : ℝ)..t, weighted f s u * weighted g s (t - u) := by
  rw [intervalIntegral.integral_of_le ht, integral_Ioc_eq_integral_Ioo]
  rw [← integral_complex_ofReal (μ := volume.restrict (Ioo 0 t))
    (f := fun u => f u * g (t - u)), ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u _
  exact (weighted_product f g s t u).symm

/-- The complex one-sided Laplace convolution identity, with both weighted
integrability requirements explicit. -/
theorem laplace_causal_convolution (f g : ℝ → ℝ) (s : ℂ)
    (hf : IntegrableOn (weighted f s) (Ioi 0))
    (hg : IntegrableOn (weighted g s) (Ioi 0)) :
    laplace (fun t => ∫ u in Ioo 0 t, f u * g (t - u)) s = laplace f s * laplace g s := by
  have hc := integral_posConvolution hf hg (ContinuousLinearMap.mul ℝ ℂ)
  calc
    _ = ∫ t in Ioi (0 : ℝ), ∫ u in (0 : ℝ)..t,
        weighted f s u * weighted g s (t - u) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact weighted_inner f g s t ht.le
    _ = _ := by simpa only [ContinuousLinearMap.mul_apply', laplace, weighted] using hc

theorem laplace_const_mul (c : ℝ) (f : ℝ → ℝ) (s : ℂ) :
    laplace (fun t => c * f t) s = (c : ℂ) * laplace f s := by
  unfold laplace
  calc
    _ = ∫ t in Ioi (0 : ℝ), (c : ℂ) * (Complex.exp (-s * (t : ℂ)) * (f t : ℂ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      push_cast
      ring
    _ = _ := integral_const_mul _ _

/-- A reduction of the exact fractional integral transform to its kernel transform.
The kernel-evaluation hypothesis is supplied by `kernel_transform` below. -/
theorem fractional_transform_of_kernel (ν : ℝ) (f : ℝ → ℝ) (s : ℂ) (hν : 0 < ν)
    (hf : IntegrableOn (weighted f s) (Ioi 0))
    (hk : IntegrableOn (weighted (fun t : ℝ => t ^ (ν - 1)) s) (Ioi 0))
    (hkernel : laplace (fun t : ℝ => t ^ (ν - 1)) s =
      (Real.Gamma ν : ℂ) / s ^ (ν : ℂ)) :
    laplace (rlIntegral 0 ν f) s = laplace f s / s ^ (ν : ℂ) := by
  have hfun : rlIntegral 0 ν f = fun t => (Real.Gamma ν)⁻¹ *
      ∫ u in Ioo 0 t, f u * (t - u) ^ (ν - 1) := by
    funext t
    simp only [rlIntegral, if_neg (ne_of_gt hν)]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioo
    intro u _
    ring
  rw [hfun, laplace_const_mul, laplace_causal_convolution f _ s hf hk, hkernel]
  have hΓ : (Real.Gamma ν : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.Gamma_pos_of_pos hν))
  simp only [Complex.ofReal_inv]
  calc
    _ = ((Real.Gamma ν : ℂ)⁻¹ * (Real.Gamma ν : ℂ)) * laplace f s / s ^ (ν : ℂ) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hΓ, one_mul]


theorem kernel_recurrence (ν : ℝ) (s : ℂ) (hν : 0 < ν) (hs : 0 < s.re) :
    s * laplace (fun t : ℝ => t ^ ν) s =
      (ν : ℂ) * laplace (fun t : ℝ => t ^ (ν - 1)) s := by
  let u : ℝ → ℂ := fun t => (t ^ ν : ℝ)
  let v : ℝ → ℂ := fun t => Complex.exp (-s * (t : ℂ))
  let u' : ℝ → ℂ := fun t => ((ν * t ^ (ν - 1) : ℝ) : ℂ)
  let v' : ℝ → ℂ := fun t => -s * Complex.exp (-s * (t : ℂ))
  have hu : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt u (u' t) t := by
    intro t ht
    exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht))).ofReal_comp
  have hv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt v (v' t) t := by
    intro t _
    convert (((hasDerivAt_id t).ofReal_comp.const_mul (-s)).cexp) using 1 <;> simp [v, v', mul_comm]
  have hki := weighted_kernel_integrable (ν + 1) s (by linarith) hs
  have hkl := weighted_kernel_integrable ν s hν hs
  have hright : IntegrableOn (u * v') (Ioi 0) := by
    have heq : u * v' = fun t => -s * weighted (fun t : ℝ => t ^ (ν + 1 - 1)) s t := by
      funext t
      simp only [Pi.mul_apply, u, v', weighted, add_sub_cancel_right]
      ring
    rw [heq]
    exact hki.const_mul (-s)
  have hleft : IntegrableOn (u' * v) (Ioi 0) := by
    have heq : u' * v = fun t => (ν : ℂ) * weighted (fun t : ℝ => t ^ (ν - 1)) s t := by
      funext t
      simp only [Pi.mul_apply, u', v, weighted, Complex.ofReal_mul]
      ring
    rw [heq]
    exact hkl.const_mul (ν : ℂ)
  have hzero : Tendsto (u * v) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : ContinuousAt (u * v) 0 := by
      apply ContinuousAt.mul
      · exact Complex.continuous_ofReal.continuousAt.comp
          (Real.continuousAt_rpow_const 0 ν (Or.inr hν.le))
      · exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousAt
    have hval : (u * v) 0 = 0 := by simp [u, v, Real.zero_rpow (ne_of_gt hν)]
    rw [← hval]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hinfty : Tendsto (u * v) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ν s.re hs).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp only [Pi.mul_apply, u, v, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos ht _), Complex.norm_exp, Complex.mul_re,
      Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im,
      mul_zero, sub_zero]
  have hip := integral_Ioi_mul_deriv_eq_deriv_mul hu hv hright hleft hzero hinfty
  have hR : (∫ t in Ioi (0 : ℝ), u t * v' t) =
      -s * laplace (fun t : ℝ => t ^ ν) s := by
    unfold laplace
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp [u, v', laplace]
    ring
  have hL : (∫ t in Ioi (0 : ℝ), u' t * v t) =
      (ν : ℂ) * laplace (fun t : ℝ => t ^ (ν - 1)) s := by
    unfold laplace
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp [u', v, laplace]
    push_cast
    ring
  rw [hR, hL] at hip
  linear_combination -hip

theorem kernel_below_one (ν : ℝ) (s : ℂ) (hν : 0 < ν) (hν1 : ν < 1)
    (hs : 0 < s.re) :
    laplace (fun t : ℝ => t ^ (ν - 1)) s = (Real.Gamma ν : ℂ) / s ^ (ν : ℂ) := by
  have h := Kyprianou.Ch01.stableGammaStrictLeftMellinIntegral
    (1 - ν) (by linarith) (by linarith) (-s) (by simpa using hs)
  have hsne : s ≠ 0 := by intro hz; simp [hz] at hs
  have ha : -(1 - ν) = ν - 1 := by ring
  have hb : 1 - (1 - ν) = ν := by ring
  have hc : (1 - ν - 1 : ℝ) = -ν := by ring
  rw [ha, hb, hc, neg_neg] at h
  change laplace (fun t : ℝ => t ^ (ν - 1)) s = _ at h
  rw [Complex.ofReal_neg, mul_comm (- (ν : ℂ)) (Complex.log s),
    ← Complex.cpow_def_of_ne_zero hsne, Complex.cpow_neg] at h
  simpa only [div_eq_mul_inv] using h

theorem kernel_one (s : ℂ) (hs : 0 < s.re) :
    laplace (fun t : ℝ => t ^ ((1 : ℝ) - 1)) s = (Real.Gamma 1 : ℂ) / s ^ ((1 : ℝ) : ℂ) := by
  simpa [laplace, Real.Gamma_one] using
    integral_exp_mul_complex_Ioi (a := -s) (by simpa using hs) 0

/-- Repeated integration by parts extends the fractional base strip to every
positive order; the principal complex power obeys the same recurrence. -/
theorem kernel_shift (r : ℝ) (s : ℂ) (hr : 0 < r) (hr1 : r ≤ 1) (hs : 0 < s.re) :
    ∀ n : ℕ, laplace (fun t : ℝ => t ^ (r + n - 1)) s =
      (Real.Gamma (r + n) : ℂ) / s ^ ((r + n : ℝ) : ℂ) := by
  have hsne : s ≠ 0 := by intro hz; simp [hz] at hs
  intro n
  induction n with
  | zero =>
    simp only [Nat.cast_zero, add_zero]
    rcases lt_or_eq_of_le hr1 with hlt | heq
    · exact kernel_below_one r s hr hlt hs
    · subst r
      exact kernel_one s hs
  | succ n ih =>
    have hp : 0 < r + (n : ℝ) := add_pos_of_pos_of_nonneg hr (Nat.cast_nonneg n)
    have hrec := kernel_recurrence (r + n) s hp hs
    have hexp : r + (↑(n + 1) : ℝ) - 1 = r + n := by push_cast; ring
    have hγ : Real.Gamma (r + (↑(n + 1) : ℝ)) =
        (r + n) * Real.Gamma (r + n) := by
      have he : r + (↑(n + 1) : ℝ) = r + n + 1 := by push_cast; ring
      rw [he, Real.Gamma_add_one (ne_of_gt hp)]
    have hcp : s ^ ((r + (↑(n + 1) : ℝ) : ℝ) : ℂ) =
        s ^ ((r + (n : ℝ) : ℝ) : ℂ) * s := by
      have he : ((r + (↑(n + 1) : ℝ) : ℝ) : ℂ) = ((r + (n : ℝ) : ℝ) : ℂ) + 1 := by
        push_cast
        ring
      rw [he, Complex.cpow_add _ _ hsne, Complex.cpow_one]
    rw [hexp]
    calc
      _ = ((r + (n : ℝ) : ℝ) : ℂ) * laplace (fun t : ℝ => t ^ (r + n - 1)) s / s := by
        apply (eq_div_iff hsne).2
        simpa only [mul_comm] using hrec
      _ = _ := by
        rw [ih, hγ, hcp, Complex.ofReal_mul]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring

/-- The Gamma kernel transform for arbitrary positive real order and arbitrary
complex Laplace parameter in the open right half-plane. -/
theorem kernel_transform (ν : ℝ) (s : ℂ) (hν : 0 < ν) (hs : 0 < s.re) :
    laplace (fun t : ℝ => t ^ (ν - 1)) s = (Real.Gamma ν : ℂ) / s ^ (ν : ℂ) := by
  let N : ℕ := ⌈ν⌉₊
  have hN : 1 ≤ N := Nat.one_le_ceil_iff.mpr hν
  let r : ℝ := ν + 1 - N
  have hr : 0 < r := by
    have hb := Nat.ceil_lt_add_one hν.le
    dsimp [r, N]
    linarith
  have hr1 : r ≤ 1 := by
    have hb := Nat.le_ceil ν
    dsimp [r, N]
    linarith
  have hdecomp : r + ((N - 1 : ℕ) : ℝ) = ν := by
    rw [Nat.cast_sub hN, Nat.cast_one]
    dsimp [r]
    ring
  simpa only [hdecomp] using kernel_shift r s hr hr1 hs (N - 1)

end FractionalCalc.LaplaceIntegralProof

open FractionalCalc FractionalCalc.LaplaceIntegralProof

theorem solution (ν α : ℝ) (f : ℝ → ℝ) (s : ℂ)
    (hν : 0 < ν) (hf : ContinuousOn f (Ici 0))
    (hexp : ∃ M T : ℝ, 0 < M ∧ 0 < T ∧ ∀ t ≥ T, |f t| ≤ M * Real.exp (α * t))
    (hsα : α < s.re) (hs0 : 0 < s.re) :
    laplace (rlIntegral 0 ν f) s = laplace f s / s ^ (ν : ℂ) := by
  exact fractional_transform_of_kernel ν f s hν
    (weighted_integrable_of_exponentialOrder α f s hf hexp hsα)
    (weighted_kernel_integrable ν s hν hs0)
    (kernel_transform ν s hν hs0)

end
