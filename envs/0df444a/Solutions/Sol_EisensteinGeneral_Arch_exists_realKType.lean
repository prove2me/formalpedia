-- Prove2me | solution 1 for EisensteinGeneral.Arch.exists_realKType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/54d62ae1-1eac-58e4-97c8-14295316cc6d

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

namespace P2MW.S_EisensteinGeneral_Arch_exists_realKType

open Set MeasureTheory
set_option autoImplicit false

namespace EgenArch

open EisensteinGeneral.Arch

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
  choose Ci ci Ni hCi hci hE2 using fun i : κ => exists_norm_archIntegral_le c hc (R + ‖b i‖)
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

private noncomputable def e6_K (z : ℂ) (t : ℝ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ z * Complex.exp (-(Real.pi : ℂ) * (u + t ^ 2 / u))

private def e6_IsComb (Φ : ℂ → ℝ → ℂ) : Prop :=
  ∃ (κ : Type) (T : Finset κ) (a : κ → ℂ → ℂ) (β b : κ → ℂ) (l : κ → ℕ),
    (∀ i ∈ T, Differentiable ℂ (a i)) ∧ (∀ i ∈ T, ‖β i‖ ≤ 1) ∧
      ∀ (w : ℂ) (t : ℝ), t ≠ 0 → Φ w t = ∑ i ∈ T, a i w * β i * (t : ℂ) ^ l i *
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (w + b i) * Complex.exp (-(Real.pi : ℂ) * (u + t ^ 2 / u))

private theorem e6_isComb_congr {Φ Ψ : ℂ → ℝ → ℂ} (h : e6_IsComb Φ)
    (hΨ : ∀ (w : ℂ) (t : ℝ), t ≠ 0 → Ψ w t = Φ w t) : e6_IsComb Ψ := by
  obtain ⟨κ, T, a, β, b, l, ha, hβ, hΦ⟩ := h
  exact ⟨κ, T, a, β, b, l, ha, hβ, fun w t ht => (hΨ w t ht).trans (hΦ w t ht)⟩

private theorem e6_isComb_term (a : ℂ → ℂ) (ha : Differentiable ℂ a) (l : ℕ) (b : ℂ) :
    e6_IsComb (fun w t => a w * (t : ℂ) ^ l * e6_K (w + b) t) := by
  refine ⟨Unit, {()}, fun _ => a, fun _ => 1, fun _ => b, fun _ => l, fun _ _ => ha,
    fun _ _ => by simp, fun w t _ => ?_⟩
  rw [Finset.sum_singleton]
  show a w * (t : ℂ) ^ l * e6_K (w + b) t = a w * 1 * (t : ℂ) ^ l * e6_K (w + b) t
  rw [mul_one]

private theorem e6_isComb_add {Φ Ψ : ℂ → ℝ → ℂ} (hΦ : e6_IsComb Φ) (hΨ : e6_IsComb Ψ) :
    e6_IsComb (fun w t => Φ w t + Ψ w t) := by
  obtain ⟨κ₁, T₁, a₁, β₁, b₁, l₁, ha₁, hβ₁, h₁⟩ := hΦ
  obtain ⟨κ₂, T₂, a₂, β₂, b₂, l₂, ha₂, hβ₂, h₂⟩ := hΨ
  refine ⟨κ₁ ⊕ κ₂, T₁.disjSum T₂, Sum.elim a₁ a₂, Sum.elim β₁ β₂, Sum.elim b₁ b₂, Sum.elim l₁ l₂,
    ?_, ?_, fun w t ht => ?_⟩
  · rintro (i | i) hi
    · exact ha₁ i (Finset.inl_mem_disjSum.mp hi)
    · exact ha₂ i (Finset.inr_mem_disjSum.mp hi)
  · rintro (i | i) hi
    · exact hβ₁ i (Finset.inl_mem_disjSum.mp hi)
    · exact hβ₂ i (Finset.inr_mem_disjSum.mp hi)
  · show Φ w t + Ψ w t = _
    rw [h₁ w t ht, h₂ w t ht, Finset.sum_disjSum]
    simp only [Sum.elim_inl, Sum.elim_inr]

private theorem e6_isComb_const_mul {Φ : ℂ → ℝ → ℂ} (hΦ : e6_IsComb Φ) (c : ℂ) :
    e6_IsComb (fun w t => c * Φ w t) := by
  obtain ⟨κ, T, a, β, b, l, ha, hβ, h⟩ := hΦ
  refine ⟨κ, T, fun i w => c * a i w, β, b, l, fun i hi => (ha i hi).const_mul c, hβ,
    fun w t ht => ?_⟩
  show c * Φ w t = _
  rw [h w t ht, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_assoc]

private theorem e6_isComb_shift {Φ : ℂ → ℝ → ℂ} (hΦ : e6_IsComb Φ) (s : ℂ) :
    e6_IsComb (fun w t => Φ (w + s) t) := by
  obtain ⟨κ, T, a, β, b, l, ha, hβ, h⟩ := hΦ
  refine ⟨κ, T, fun i w => a i (w + s), β, fun i => b i + s, l,
    fun i hi => (ha i hi).comp (differentiable_id.add_const s), hβ, fun w t ht => ?_⟩
  show Φ (w + s) t = _
  rw [h (w + s) t ht]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [add_assoc, add_comm s (b i)]

private noncomputable def e6_A (w : ℂ) : ℂ := (Real.pi : ℂ) ^ w * (Complex.Gamma w)⁻¹

private theorem e6_differentiable_A : Differentiable ℂ e6_A := by
  show Differentiable ℂ fun w => (Real.pi : ℂ) ^ w * (Complex.Gamma w)⁻¹
  refine Differentiable.mul (fun w => ?_) Complex.differentiable_one_div_Gamma
  exact differentiableAt_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))

private noncomputable def e6_Phi (ε : ℝ) : ℕ → ℂ → ℝ → ℂ
  | 0 => fun w t => e6_A w * e6_K (w - 3 / 2) t
  | 1 => fun w t => -Complex.I * e6_A w * t * e6_K (w - 5 / 2) t
      + ε * Complex.I * (e6_A w * e6_K (w - 3 / 2) t)
  | m + 2 => fun w t => e6_Phi ε m (w - 1) t + 2 * ε * Complex.I * e6_Phi ε (m + 1) w t

private theorem e6_isComb_Phi (ε : ℝ) (m : ℕ) : e6_IsComb (e6_Phi ε m) := by
  have h0 : e6_IsComb (e6_Phi ε 0) := by
    refine e6_isComb_congr (e6_isComb_term e6_A e6_differentiable_A 0 (-(3 / 2))) ?_
    intro w t _
    show e6_A w * e6_K (w - 3 / 2) t = e6_A w * (t : ℂ) ^ 0 * e6_K (w + -(3 / 2)) t
    rw [pow_zero, mul_one, sub_eq_add_neg]
  have h1 : e6_IsComb (e6_Phi ε 1) := by
    refine e6_isComb_congr (e6_isComb_add (e6_isComb_term (fun w => -Complex.I * e6_A w)
      (e6_differentiable_A.const_mul _) 1 (-(5 / 2))) (e6_isComb_const_mul h0 (ε * Complex.I))) ?_
    intro w t _
    show -Complex.I * e6_A w * t * e6_K (w - 5 / 2) t + ε * Complex.I * (e6_A w * e6_K (w - 3 / 2) t)
      = -Complex.I * e6_A w * (t : ℂ) ^ 1 * e6_K (w + -(5 / 2)) t + ε * Complex.I * e6_Phi ε 0 w t
    rw [pow_one, sub_eq_add_neg]
    rfl
  have hstep : ∀ m, e6_IsComb (e6_Phi ε m) → e6_IsComb (e6_Phi ε (m + 1)) →
      e6_IsComb (e6_Phi ε (m + 2)) := by
    intro m hm hm1
    refine e6_isComb_congr (e6_isComb_add (e6_isComb_shift hm (-1))
      (e6_isComb_const_mul hm1 (2 * ε * Complex.I))) ?_
    intro w t _
    show e6_Phi ε m (w - 1) t + 2 * ε * Complex.I * e6_Phi ε (m + 1) w t
      = e6_Phi ε m (w + -1) t + 2 * ε * Complex.I * e6_Phi ε (m + 1) w t
    rw [sub_eq_add_neg]
  have key : ∀ m, e6_IsComb (e6_Phi ε m) ∧ e6_IsComb (e6_Phi ε (m + 1)) := by
    intro m
    induction m with
    | zero => exact ⟨h0, h1⟩
    | succ m ih => exact ⟨ih.2, hstep m ih.1 ih.2⟩
  exact (key m).1

private noncomputable def e6_sgn (k : ℤ) : ℝ := if 0 ≤ k then -1 else 1

private theorem e6_sgn_cases (k : ℤ) : e6_sgn k = 1 ∨ e6_sgn k = -1 := by
  unfold e6_sgn
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

private noncomputable def e6_J (k : ℤ) (w : ℂ) (t : ℝ) : ℂ :=
  e6_Phi (e6_sgn k) k.natAbs (w + (k.natAbs : ℂ) / 2) t

private theorem e6_isComb_J (k : ℤ) : e6_IsComb (e6_J k) :=
  e6_isComb_shift (e6_isComb_Phi (e6_sgn k) k.natAbs) ((k.natAbs : ℂ) / 2)

private noncomputable def e6_chr (t x : ℝ) : ℂ := Complex.exp (↑(-2 * Real.pi * x * t) * Complex.I)

private noncomputable def e6_G (ε : ℝ) (m : ℕ) (w : ℂ) (t : ℝ) : ℂ :=
  ∫ x : ℝ, ((x : ℂ) + ε * Complex.I) ^ m * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) * e6_chr t x

private theorem e6_integrableOn_laplace (w : ℂ) (hw : 0 < w.re) (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun v : ℝ => (v : ℂ) ^ (w - 1) * Complex.exp (-((r : ℂ) * v))) (Ioi 0) := by
  by_contra h
  have key := Complex.integral_cpow_mul_exp_neg_mul_Ioi hw hr
  rw [integral_undef h] at key
  refine (mul_ne_zero ?_ (Complex.Gamma_ne_zero_of_re_pos hw)) key.symm
  rw [Complex.cpow_def_of_ne_zero (one_div_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'))]
  exact Complex.exp_ne_zero _

private theorem e6_laplace (w : ℂ) (hw : 0 < w.re) (x : ℝ) :
    (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) = e6_A w *
      ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (w - 1) * Complex.exp (-(((Real.pi * (1 + x ^ 2) : ℝ) : ℂ) * v)) := by
  have hq : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hr : (0 : ℝ) < Real.pi * (1 + x ^ 2) := mul_pos Real.pi_pos hq
  have hΓ : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hw
  have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hQ : (((1 + x ^ 2 : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hπw : ((Real.pi : ℝ) : ℂ) ^ w ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hπ]
    exact Complex.exp_ne_zero _
  have hQw : (((1 + x ^ 2 : ℝ) : ℂ)) ^ w ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hQ]
    exact Complex.exp_ne_zero _
  have h1 : (1 / ((Real.pi * (1 + x ^ 2) : ℝ) : ℂ)) ^ w
      = (((Real.pi : ℝ) : ℂ) ^ w)⁻¹ * ((((1 + x ^ 2 : ℝ)) : ℂ) ^ w)⁻¹ := by
    rw [one_div, Complex.inv_cpow _ _
        (by rw [Complex.arg_ofReal_of_nonneg hr.le]; exact Real.pi_ne_zero.symm),
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le hq.le, mul_inv]
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi hw hr, h1, Complex.cpow_neg]
  unfold e6_A
  field_simp

private theorem e6_integrable_weight (g : ℝ → ℂ) (hg : Continuous g) (p : ℕ)
    (hgb : ∀ x, ‖g x‖ ≤ (1 + x ^ 2) ^ ((p : ℝ) / 2)) (w : ℂ) (hw : ((p : ℝ) + 1) / 2 < w.re)
    (t : ℝ) :
    Integrable (fun x : ℝ => g x * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) * e6_chr t x) := by
  have hr : (Module.finrank ℝ ℝ : ℝ) < 2 * w.re - p := by
    rw [Module.finrank_self]
    push_cast
    linarith
  refine (integrable_rpow_neg_one_add_norm_sq hr).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    refine (hg.mul ?_).mul ?_
    · exact Continuous.cpow (by fun_prop) continuous_const
        (fun x => Complex.ofReal_mem_slitPlane.mpr (by positivity))
    · unfold e6_chr
      fun_prop
  · have hq : (0 : ℝ) < 1 + x ^ 2 := by positivity
    rw [norm_mul, norm_mul, e6_chr, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_cpow_eq_rpow_re_of_pos hq, Complex.neg_re, Real.norm_eq_abs, sq_abs]
    calc ‖g x‖ * (1 + x ^ 2) ^ (-w.re)
        ≤ (1 + x ^ 2) ^ ((p : ℝ) / 2) * (1 + x ^ 2) ^ (-w.re) := by
          gcongr
          exact hgb x
      _ = (1 + x ^ 2) ^ (-(2 * w.re - p) / 2) := by
          rw [← Real.rpow_add hq]
          congr 1
          ring

private theorem e6_fubini (g : ℝ → ℂ) (hg : Continuous g) (p : ℕ)
    (hgb : ∀ x, ‖g x‖ ≤ (1 + x ^ 2) ^ ((p : ℝ) / 2)) (w : ℂ) (hw : ((p : ℝ) + 1) / 2 < w.re)
    (t : ℝ) :
    ∫ x : ℝ, g x * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) * e6_chr t x
      = e6_A w * ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (w - 1) * Complex.exp (-((Real.pi * v : ℝ) : ℂ)) *
          ∫ x : ℝ, e6_chr t x * (g x * Complex.exp (-(Real.pi : ℂ) * v * x ^ 2)) := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hw0 : 0 < w.re := by linarith
  have hL : ∀ x : ℝ, g x * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) * e6_chr t x
      = e6_A w * ∫ v in Ioi (0 : ℝ), g x * e6_chr t x *
          ((v : ℂ) ^ (w - 1) * Complex.exp (-(((Real.pi * (1 + x ^ 2) : ℝ) : ℂ) * v))) := by
    intro x
    rw [e6_laplace w hw0 x, integral_const_mul]
    ring
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (x v : ℝ) => g x * e6_chr t x *
      ((v : ℂ) ^ (w - 1) * Complex.exp (-(((Real.pi * (1 + x ^ 2) : ℝ) : ℂ) * v))))
      ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) := by
    refine Measurable.aestronglyMeasurable ?_
    show Measurable fun q : ℝ × ℝ => g q.1 * e6_chr t q.1 *
      ((q.2 : ℂ) ^ (w - 1) * Complex.exp (-(((Real.pi * (1 + q.1 ^ 2) : ℝ) : ℂ) * q.2)))
    have hgm : Measurable g := hg.measurable
    unfold e6_chr
    fun_prop
  have hInt : Integrable (Function.uncurry fun (x v : ℝ) => g x * e6_chr t x *
      ((v : ℂ) ^ (w - 1) * Complex.exp (-(((Real.pi * (1 + x ^ 2) : ℝ) : ℂ) * v))))
      ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) := by
    rw [integrable_prod_iff hmeas]
    refine ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
    · simp only [Function.uncurry_apply_pair]
      exact (e6_integrableOn_laplace w hw0 _ (mul_pos Real.pi_pos (by positivity))).const_mul _
    · simp only [Function.uncurry_apply_pair]
      have hnorm : ∀ x : ℝ, ∫ v in Ioi (0 : ℝ), ‖g x * e6_chr t x *
          ((v : ℂ) ^ (w - 1) * Complex.exp (-(((Real.pi * (1 + x ^ 2) : ℝ) : ℂ) * v)))‖
            = ‖g x‖ * ((1 / (Real.pi * (1 + x ^ 2))) ^ w.re * Real.Gamma w.re) := by
        intro x
        have hq : (0 : ℝ) < 1 + x ^ 2 := by positivity
        rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi hw0 (mul_pos Real.pi_pos hq),
          ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
        have hv : (0 : ℝ) < v := hv
        have hre : (-((((Real.pi * (1 + x ^ 2) : ℝ) : ℂ)) * v)).re
            = -(Real.pi * (1 + x ^ 2) * v) := by
          rw [← Complex.ofReal_mul, Complex.neg_re, Complex.ofReal_re]
        rw [norm_mul, norm_mul, norm_mul, e6_chr, Complex.norm_exp_ofReal_mul_I, mul_one,
          Complex.norm_cpow_eq_rpow_re_of_pos hv, Complex.sub_re, Complex.one_re, Complex.norm_exp,
          hre]
      simp_rw [hnorm]
      have hr : (Module.finrank ℝ ℝ : ℝ) < 2 * w.re - p := by
        rw [Module.finrank_self]
        push_cast
        linarith
      refine ((integrable_rpow_neg_one_add_norm_sq hr).const_mul
        (Real.Gamma w.re * Real.pi ^ (-w.re))).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
      · refine Continuous.aestronglyMeasurable (hg.norm.mul (Continuous.mul ?_ continuous_const))
        exact (continuous_const.div (by fun_prop)
          (fun x => (mul_pos Real.pi_pos (by positivity)).ne')).rpow_const
          (fun x => Or.inr hw0.le)
      · have hq : (0 : ℝ) < 1 + x ^ 2 := by positivity
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs, sq_abs]
        calc ‖g x‖ * ((1 / (Real.pi * (1 + x ^ 2))) ^ w.re * Real.Gamma w.re)
            ≤ (1 + x ^ 2) ^ ((p : ℝ) / 2) * ((1 / (Real.pi * (1 + x ^ 2))) ^ w.re * Real.Gamma w.re) := by
              gcongr
              exact hgb x
          _ = Real.Gamma w.re * Real.pi ^ (-w.re) * ((1 : ℝ) + x ^ 2) ^ (-(2 * w.re - p) / 2) := by
              rw [one_div, Real.inv_rpow (mul_pos Real.pi_pos hq).le, Real.mul_rpow Real.pi_pos.le hq.le,
                Real.rpow_neg Real.pi_pos.le,
                show (-(2 * w.re - (p : ℝ)) / 2) = (p : ℝ) / 2 + -w.re by ring,
                Real.rpow_add hq, Real.rpow_neg hq.le]
              ring
  simp_rw [hL]
  rw [integral_const_mul]
  congr 1
  rw [integral_integral_swap hInt]
  refine setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
  have hsplit : ∀ x : ℝ, g x * e6_chr t x *
      ((v : ℂ) ^ (w - 1) * Complex.exp (-(((Real.pi * (1 + x ^ 2) : ℝ) : ℂ) * v)))
        = (v : ℂ) ^ (w - 1) * Complex.exp (-((Real.pi * v : ℝ) : ℂ)) *
          (e6_chr t x * (g x * Complex.exp (-(Real.pi : ℂ) * v * x ^ 2))) := by
    intro x
    have hexp : Complex.exp (-(((Real.pi * (1 + x ^ 2) : ℝ) : ℂ) * v))
        = Complex.exp (-((Real.pi * v : ℝ) : ℂ)) * Complex.exp (-(Real.pi : ℂ) * v * x ^ 2) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    ring
  simp_rw [hsplit]
  rw [integral_const_mul]

private theorem e6_gaussFT (v : ℝ) (hv : 0 < v) (t : ℝ) :
    FourierTransform.fourier (fun x : ℝ => Complex.exp (-(Real.pi : ℂ) * v * x ^ 2)) t
      = 1 / (v : ℂ) ^ (1 / 2 : ℂ) * Complex.exp (-(Real.pi : ℂ) / v * t ^ 2) := by
  have hb : 0 < (v : ℂ).re := by rwa [Complex.ofReal_re]
  rw [fourier_gaussian_pi hb]

private theorem e6_xgaussFT (v : ℝ) (hv : 0 < v) (t : ℝ) :
    ∫ x : ℝ, e6_chr t x * ((x : ℂ) * Complex.exp (-(Real.pi : ℂ) * v * x ^ 2))
      = 1 / (v : ℂ) ^ (1 / 2 : ℂ) * Complex.exp (-(Real.pi : ℂ) / v * t ^ 2)
          * (-Complex.I * t / v) := by
  have hb : 0 < ((Real.pi : ℂ) * v).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_pos Real.pi_pos hv
  have hfi : Integrable (fun x : ℝ => Complex.exp (-(Real.pi : ℂ) * v * x ^ 2)) := by
    simpa only [neg_mul] using integrable_cexp_neg_mul_sq hb
  have hfi' : Integrable (fun x : ℝ => x • Complex.exp (-(Real.pi : ℂ) * v * x ^ 2)) := by
    simpa only [neg_mul, Complex.real_smul] using integrable_mul_cexp_neg_mul_sq hb
  have hD := Real.hasDerivAt_fourier hfi hfi' t
  rw [fourier_gaussian_pi (by rwa [Complex.ofReal_re] : 0 < (v : ℂ).re)] at hD
  have hD' : HasDerivAt (fun s : ℝ => 1 / (v : ℂ) ^ (1 / 2 : ℂ) * Complex.exp (-(Real.pi : ℂ) / v * s ^ 2))
      (1 / (v : ℂ) ^ (1 / 2 : ℂ) * (Complex.exp (-(Real.pi : ℂ) / v * t ^ 2)
        * (-(Real.pi : ℂ) / v * (2 * t)))) t := by
    refine HasDerivAt.const_mul _ (HasDerivAt.cexp ?_)
    have h2 : HasDerivAt (fun s : ℝ => (s : ℂ) ^ 2) (2 * (t : ℂ)) t := by
      simpa using (hasDerivAt_pow 2 t).ofReal_comp
    exact h2.const_mul _
  have huniq := hD.unique hD'
  rw [Real.fourier_real_eq_integral_exp_smul] at huniq
  simp only [smul_eq_mul] at huniq
  have hlin : ∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * t) * Complex.I)
      * (-2 * (Real.pi : ℂ) * Complex.I * x * Complex.exp (-(Real.pi : ℂ) * v * x ^ 2))
      = (-2 * (Real.pi : ℂ) * Complex.I)
        * ∫ x : ℝ, e6_chr t x * ((x : ℂ) * Complex.exp (-(Real.pi : ℂ) * v * x ^ 2)) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    unfold e6_chr
    ring
  rw [hlin] at huniq
  have hc : (-2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  apply mul_left_cancel₀ hc
  rw [huniq]
  set c : ℂ := 1 / (v : ℂ) ^ (1 / 2 : ℂ)
  set E : ℂ := Complex.exp (-(Real.pi : ℂ) / v * t ^ 2)
  linear_combination (-2 * (Real.pi : ℂ) * c * E * t / v) * Complex.I_sq

private theorem e6_coe_bound (x : ℝ) : ‖((x : ℝ) : ℂ)‖ ≤ (1 + x ^ 2) ^ (((1 : ℕ) : ℝ) / 2) := by
  rw [Complex.norm_real, Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs, Nat.cast_one, ← Real.sqrt_eq_rpow]
  exact Real.sqrt_le_sqrt (by nlinarith)

private theorem e6_base0 (w : ℂ) (hw : 1 / 2 < w.re) (t : ℝ) :
    e6_A w * e6_K (w - 3 / 2) t
      = ∫ x : ℝ, 1 * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) * e6_chr t x := by
  rw [e6_fubini (fun _ : ℝ => (1 : ℂ)) continuous_const 0 (fun x => by simp) w
    (by push_cast; linarith) t]
  congr 1
  unfold e6_K
  refine setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
  have hv : (0 : ℝ) < v := hv
  have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hinner : ∫ x : ℝ, e6_chr t x * (1 * Complex.exp (-(Real.pi : ℂ) * v * x ^ 2))
      = 1 / (v : ℂ) ^ (1 / 2 : ℂ) * Complex.exp (-(Real.pi : ℂ) / v * t ^ 2) := by
    simp_rw [one_mul]
    rw [← e6_gaussFT v hv t, Real.fourier_real_eq_integral_exp_smul]
    simp_rw [smul_eq_mul]
    rfl
  rw [hinner]
  have h1 : (v : ℂ) ^ (w - 3 / 2) = (v : ℂ) ^ (w - 1) * (v : ℂ) ^ (-(1 / 2 : ℂ)) := by
    rw [← Complex.cpow_add _ _ hv0]
    congr 1
    ring
  have h2 : Complex.exp (-(Real.pi : ℂ) * (v + t ^ 2 / v))
      = Complex.exp (-((Real.pi * v : ℝ) : ℂ)) * Complex.exp (-(Real.pi : ℂ) / v * t ^ 2) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h1, h2, one_div ((v : ℂ) ^ (1 / 2 : ℂ)), ← Complex.cpow_neg]
  ring

private theorem e6_base1 (w : ℂ) (hw : 1 < w.re) (t : ℝ) :
    -Complex.I * e6_A w * t * e6_K (w - 5 / 2) t
      = ∫ x : ℝ, (x : ℂ) * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) * e6_chr t x := by
  rw [e6_fubini (fun x : ℝ => ((x : ℝ) : ℂ)) Complex.continuous_ofReal 1 e6_coe_bound w
    (by push_cast; linarith) t]
  unfold e6_K
  rw [show -Complex.I * e6_A w * t * (∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (w - 5 / 2) *
        Complex.exp (-(Real.pi : ℂ) * (u + t ^ 2 / u)))
      = e6_A w * ∫ u in Ioi (0 : ℝ), -Complex.I * t * ((u : ℂ) ^ (w - 5 / 2) *
        Complex.exp (-(Real.pi : ℂ) * (u + t ^ 2 / u))) by rw [integral_const_mul]; ring]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
  have hv : (0 : ℝ) < v := hv
  have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  rw [e6_xgaussFT v hv t]
  have h1 : (v : ℂ) ^ (w - 5 / 2) = (v : ℂ) ^ (w - 1) * (v : ℂ) ^ (-(1 / 2 : ℂ)) * (v : ℂ)⁻¹ := by
    rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hv0, ← Complex.cpow_add _ _ hv0]
    congr 1
    ring
  have h2 : Complex.exp (-(Real.pi : ℂ) * (v + t ^ 2 / v))
      = Complex.exp (-((Real.pi * v : ℝ) : ℂ)) * Complex.exp (-(Real.pi : ℂ) / v * t ^ 2) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h1, h2, one_div ((v : ℂ) ^ (1 / 2 : ℂ)), ← Complex.cpow_neg]
  ring

private theorem e6_G_zero (ε : ℝ) (w : ℂ) (t : ℝ) (hw : 1 / 2 < w.re) :
    e6_Phi ε 0 w t = e6_G ε 0 w t := by
  show e6_A w * e6_K (w - 3 / 2) t
    = ∫ x : ℝ, ((x : ℂ) + ε * Complex.I) ^ 0 * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) * e6_chr t x
  simp_rw [pow_zero]
  exact e6_base0 w hw t

private theorem e6_G_one (ε : ℝ) (w : ℂ) (t : ℝ) (hw : 1 < w.re) :
    e6_Phi ε 1 w t = e6_G ε 1 w t := by
  have hw' : 1 / 2 < w.re := by linarith
  have hX := e6_integrable_weight (fun x : ℝ => ((x : ℝ) : ℂ)) Complex.continuous_ofReal 1
    e6_coe_bound w (by push_cast; linarith) t
  have h0 := e6_integrable_weight (fun _ : ℝ => (1 : ℂ)) continuous_const 0 (fun x => by simp) w
    (by push_cast; linarith) t
  show -Complex.I * e6_A w * t * e6_K (w - 5 / 2) t + ε * Complex.I * (e6_A w * e6_K (w - 3 / 2) t)
    = e6_G ε 1 w t
  rw [e6_base1 w hw t, e6_base0 w hw' t]
  unfold e6_G
  rw [← integral_const_mul, ← integral_add hX (h0.const_mul _)]
  congr 1
  funext x
  ring

private theorem e6_norm_integrand (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (m : ℕ) (w : ℂ) (t x : ℝ) :
    ‖((x : ℂ) + ε * Complex.I) ^ m * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) * e6_chr t x‖
      = (1 + x ^ 2) ^ ((m : ℝ) / 2 - w.re) := by
  have hq : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hε2 : ε ^ 2 = 1 := by rcases hε with h | h <;> simp [h]
  have hroot : Real.sqrt (x ^ 2 + ε ^ 2) = (1 + x ^ 2) ^ (1 / 2 : ℝ) := by
    rw [hε2, add_comm, Real.sqrt_eq_rpow]
  have hpow : ((1 + x ^ 2) ^ (1 / 2 : ℝ)) ^ m = (1 + x ^ 2) ^ ((1 / 2 : ℝ) * m) := by
    rw [Real.rpow_mul hq.le, Real.rpow_natCast]
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_add_mul_I, hroot, hpow, e6_chr,
    Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos hq, Complex.neg_re,
    ← Real.rpow_add hq]
  congr 1
  ring

private theorem e6_integrable (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (m : ℕ) (w : ℂ) (t : ℝ)
    (hw : ((m : ℝ) + 1) / 2 < w.re) :
    Integrable (fun x : ℝ =>
      ((x : ℂ) + ε * Complex.I) ^ m * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) * e6_chr t x) := by
  have hr : (Module.finrank ℝ ℝ : ℝ) < 2 * w.re - m := by
    rw [Module.finrank_self]
    push_cast
    linarith
  refine (integrable_rpow_neg_one_add_norm_sq hr).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    refine ((Continuous.pow (by fun_prop) m).mul ?_).mul ?_
    · exact Continuous.cpow (by fun_prop) continuous_const
        (fun x => Complex.ofReal_mem_slitPlane.mpr (by positivity))
    · unfold e6_chr
      fun_prop
  · rw [e6_norm_integrand ε hε m w t x, Real.norm_eq_abs, sq_abs]
    apply le_of_eq
    congr 1
    ring

private theorem e6_G_rec (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (m : ℕ) (w : ℂ) (t : ℝ)
    (hw : ((m : ℝ) + 3) / 2 < w.re) :
    e6_G ε (m + 2) w t = e6_G ε m (w - 1) t + 2 * ε * Complex.I * e6_G ε (m + 1) w t := by
  have hε2 : (ε : ℂ) ^ 2 = 1 := by rcases hε with h | h <;> simp [h]
  have hpt : ∀ x : ℝ,
      ((x : ℂ) + ε * Complex.I) ^ (m + 2) * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) * e6_chr t x
        = ((x : ℂ) + ε * Complex.I) ^ m * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-(w - 1)) * e6_chr t x
          + 2 * ε * Complex.I
            * (((x : ℂ) + ε * Complex.I) ^ (m + 1) * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) * e6_chr t x) := by
    intro x
    have hq : (((1 + x ^ 2 : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
    have hshift : (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-(w - 1))
        = (((1 + x ^ 2 : ℝ) : ℂ)) * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) := by
      rw [show -(w - 1) = 1 + -w by ring, Complex.cpow_add _ _ hq, Complex.cpow_one]
    have hQ : (((1 + x ^ 2 : ℝ) : ℂ))
        = ((x : ℂ) + ε * Complex.I) ^ 2 - 2 * ε * Complex.I * ((x : ℂ) + ε * Complex.I) := by
      push_cast
      linear_combination (ε : ℂ) ^ 2 * Complex.I_sq - hε2
    rw [hshift]
    linear_combination
      (-(((x : ℂ) + ε * Complex.I) ^ m * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) * e6_chr t x)) * hQ
  have h1 := e6_integrable ε hε m (w - 1) t (by rw [Complex.sub_re, Complex.one_re]; linarith)
  have h2 := (e6_integrable ε hε (m + 1) w t (by push_cast; linarith)).const_mul
    (2 * ε * Complex.I)
  unfold e6_G
  simp_rw [hpt]
  rw [integral_add h1 h2, integral_const_mul]

private theorem e6_Phi_eq_G (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (m : ℕ) (w : ℂ) (t : ℝ)
    (hw : ((m : ℝ) + 1) / 2 < w.re) : e6_Phi ε m w t = e6_G ε m w t := by
  have key : ∀ (n : ℕ) (w : ℂ), ((n : ℝ) + 1) / 2 < w.re →
      e6_Phi ε n w t = e6_G ε n w t ∧
        (((n : ℝ) + 2) / 2 < w.re → e6_Phi ε (n + 1) w t = e6_G ε (n + 1) w t) := by
    intro n
    induction n with
    | zero =>
      intro w hw
      refine ⟨e6_G_zero ε w t (by norm_num at hw; linarith), fun hw' => ?_⟩
      exact e6_G_one ε w t (by norm_num at hw'; linarith)
    | succ n ih =>
      intro w hw
      push_cast at hw ih
      refine ⟨(ih w (by linarith)).2 (by linarith), fun hw' => ?_⟩
      push_cast at hw'
      show e6_Phi ε n (w - 1) t + 2 * ε * Complex.I * e6_Phi ε (n + 1) w t = e6_G ε (n + 2) w t
      have hw1 : ((n : ℝ) + 1) / 2 < (w - 1).re := by
        rw [Complex.sub_re, Complex.one_re]
        linarith
      rw [(ih (w - 1) hw1).1, (ih w (by linarith)).2 (by linarith),
        e6_G_rec ε hε n w t (by linarith)]
  exact (key m w hw).1

private theorem e6_weight (k : ℤ) (x : ℝ) :
    ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
      = (((x : ℝ) : ℂ) + (e6_sgn k : ℝ) * Complex.I) ^ k.natAbs
        * (((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) ^ k.natAbs)⁻¹ := by
  have hq : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hS : ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hq).ne'
  have hS2 : ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) ^ 2 = (x : ℂ) ^ 2 + 1 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hq.le]
    push_cast
    ring
  have hxI : (x : ℂ) - Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    have hsgn : e6_sgn (n : ℤ) = -1 := if_pos hk
    rw [hsgn, Int.natAbs_natCast, zpow_natCast, div_pow, div_eq_mul_inv]
    push_cast
    ring
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = -(n : ℤ) := ⟨k.natAbs, by omega⟩
    have hsgn : e6_sgn (-(n : ℤ)) = 1 := if_neg (not_le.mpr hk)
    have hflip : ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) / ((x : ℂ) - Complex.I)
        = ((x : ℂ) + Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) := by
      rw [div_eq_div_iff hxI hS, ← sq, hS2]
      linear_combination Complex.I_sq
    rw [hsgn, Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_natCast, ← inv_pow, inv_div, hflip,
      div_pow, div_eq_mul_inv]
    push_cast
    ring

private theorem e6_G_eq_head (k : ℤ) (w : ℂ) (t : ℝ) :
    e6_G (e6_sgn k) k.natAbs (w + (k.natAbs : ℂ) / 2) t
      = ∫ x : ℝ, ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
          * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I)) := by
  unfold e6_G
  congr 1
  funext x
  have hq : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hQ : (((1 + x ^ 2 : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hkey : (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-((k.natAbs : ℂ) / 2))
      = (((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) ^ k.natAbs)⁻¹ := by
    rw [Complex.cpow_neg, show ((k.natAbs : ℂ) / 2) = (((1 / 2 : ℝ) * (k.natAbs : ℝ) : ℝ) : ℂ) by
        push_cast; ring,
      ← Complex.ofReal_cpow hq.le, Real.rpow_mul hq.le, ← Real.sqrt_eq_rpow, Real.rpow_natCast,
      Complex.ofReal_pow]
  have hchr : e6_chr t x = Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I)) := by
    unfold e6_chr
    congr 1
    push_cast
    ring
  rw [e6_weight k x, neg_add, Complex.cpow_add _ _ hQ, hkey, hchr]
  ring

end EgenArch

open EgenArch

theorem solution (k : ℤ) :
    ∃ J : ℂ → ℝ → ℂ,
      (∀ t : ℝ, t ≠ 0 → Differentiable ℂ (fun w : ℂ => J w t)) ∧
      (∀ (w : ℂ) (t : ℝ), 1 / 2 < w.re → t ≠ 0 →
        J w t = ∫ x : ℝ, ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
          * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I))) ∧
      (∀ R : ℝ, ∃ C c' : ℝ, ∃ N : ℕ, 0 < C ∧ 0 < c' ∧ ∀ (w : ℂ) (t : ℝ), ‖w‖ ≤ R → t ≠ 0 →
        ‖J w t‖ ≤ C * max 1 (|t| ^ (-(N : ℝ))) * Real.exp (-c' * |t|)) := by
  have hπ : 0 < ((Real.pi : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    exact Real.pi_pos
  obtain ⟨κ, T, a, β, b, l, ha, hβ, hJ⟩ := e6_isComb_J k
  refine ⟨e6_J k, fun t ht => ?_, fun w t hw ht => ?_, fun R => ?_⟩
  · have hfun : (fun w : ℂ => e6_J k w t) = fun w => ∑ i ∈ T, a i w * β i * (t : ℂ) ^ l i *
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (w + b i) * Complex.exp (-(Real.pi : ℂ) * (u + t ^ 2 / u)) :=
      funext fun w => hJ w t ht
    rw [hfun]
    exact differentiable_sum_archIntegral T a ha β b l (Real.pi : ℂ) hπ t ht
  · have hre : (w + (k.natAbs : ℂ) / 2).re = w.re + (k.natAbs : ℝ) / 2 := by simp
    show e6_Phi (e6_sgn k) k.natAbs (w + (k.natAbs : ℂ) / 2) t = _
    rw [e6_Phi_eq_G (e6_sgn k) (e6_sgn_cases k) k.natAbs _ t (by rw [hre]; linarith)]
    exact e6_G_eq_head k w t
  · obtain ⟨C, c', N, hC, hc', hB⟩ := exists_norm_sum_archIntegral_le T a ha b l (Real.pi : ℂ) hπ R
    refine ⟨C, c', N, hC, hc', fun w t hw ht => ?_⟩
    rw [hJ w t ht]
    exact hB β hβ w t hw ht

#print axioms solution

end S_EisensteinGeneral_Arch_exists_realKType
end P2MW
export P2MW.S_EisensteinGeneral_Arch_exists_realKType (solution)
