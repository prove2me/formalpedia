-- Prove2me | solution 1 for EisensteinSeries.ramanujan_system_qExpansion_int
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/20bd5679-0e96-5469-a172-478a500de698

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_EisensteinSeries_ramanujan_system_qExpansion_int

set_option autoImplicit false

p2m_open "UpperHalfPlane~I"
open Complex Filter Function
open scoped Real Topology MatrixGroups Manifold ModularForm ArithmeticFunction.sigma

noncomputable section

namespace EisensteinSeries
p2m_export "EisensteinSeries" "E_qExpansion_coeff E2_slash_action E2 D2 E2_eq_tsum_cexp r"
namespace RamanujanSystemInt
p2m_open "EisensteinSeries"

local notation "𝕢₁" => Periodic.qParam 1

theorem qParam_one_eq (z : ℂ) : 𝕢₁ z = cexp (2 * π * I * z) := by
  simp [Periodic.qParam]

theorem norm_qParam_one_lt_one (τ : ℍ) : ‖𝕢₁ τ‖ < 1 := by
  simpa using τ.norm_qParam_lt_one 1

theorem norm_qParam_one_pos (τ : ℍ) : 0 < ‖𝕢₁ τ‖ := by
  rw [qParam_one_eq]; exact norm_pos_iff.mpr (Complex.exp_ne_zero _)

theorem norm_qParam_one (z : ℂ) : ‖𝕢₁ z‖ = Real.exp (-2 * π * z.im) := by
  rw [Periodic.norm_qParam, div_one]

def PolyGrowth (a : ℕ → ℂ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ n, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ k

def IsQS (a : ℕ → ℂ) (f : ℍ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun n => a n * 𝕢₁ τ ^ n) (f τ)

theorem summable_succ_pow_mul_geometric {r : ℝ} (hr0 : 0 < r) (hr : r < 1) (k : ℕ) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k * r ^ n) := by
  have h0 : Summable fun n : ℕ => (n : ℝ) ^ k * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one k (by simpa [Real.norm_of_nonneg hr0.le] using hr)
  have h1 := (summable_nat_add_iff 1).mpr h0
  refine (h1.mul_left r⁻¹).congr fun n => ?_
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

theorem PolyGrowth.summable_norm_mul {a : ℕ → ℂ} (ha : PolyGrowth a) {r : ℝ} (hr0 : 0 < r)
    (hr : r < 1) : Summable fun n => ‖a n‖ * r ^ n := by
  obtain ⟨C, k, hC, h⟩ := ha
  refine Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => mul_le_mul_of_nonneg_right (h n) (by positivity)) ?_
  simpa [mul_assoc] using (summable_succ_pow_mul_geometric hr0 hr k).mul_left C

theorem PolyGrowth.summable_norm {a : ℕ → ℂ} (ha : PolyGrowth a) (τ : ℍ) :
    Summable fun n => ‖a n * 𝕢₁ τ ^ n‖ := by
  simpa [norm_mul, norm_pow] using
    ha.summable_norm_mul (norm_qParam_one_pos τ) (norm_qParam_one_lt_one τ)

theorem PolyGrowth.summable {a : ℕ → ℂ} (ha : PolyGrowth a) (τ : ℍ) :
    Summable fun n => a n * 𝕢₁ τ ^ n :=
  (ha.summable_norm τ).of_norm

theorem PolyGrowth.of_le {a : ℕ → ℂ} (C : ℝ) (k : ℕ) (hC : 0 ≤ C)
    (h : ∀ n, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ k) : PolyGrowth a := ⟨C, k, hC, h⟩

theorem PolyGrowth.theta {a : ℕ → ℂ} (ha : PolyGrowth a) : PolyGrowth fun n => (n : ℂ) * a n := by
  obtain ⟨C, k, hC, h⟩ := ha
  refine ⟨C, k + 1, hC, fun n => ?_⟩
  rw [norm_mul, Complex.norm_natCast, pow_succ]
  have h1 : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
  calc (n : ℝ) * ‖a n‖ ≤ ((n : ℝ) + 1) * (C * ((n : ℝ) + 1) ^ k) :=
        mul_le_mul h1 (h n) (norm_nonneg _) (by positivity)
      _ = C * (((n : ℝ) + 1) ^ k * ((n : ℝ) + 1)) := by ring

theorem sigma_le_succ_pow (k n : ℕ) : ((σ k n : ℕ) : ℝ) ≤ ((n : ℝ) + 1) ^ (k + 1) := by
  have h := ArithmeticFunction.sigma_le_pow_succ k n
  calc ((σ k n : ℕ) : ℝ) ≤ ((n ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast h
    _ = (n : ℝ) ^ (k + 1) := by push_cast; ring
    _ ≤ ((n : ℝ) + 1) ^ (k + 1) := by
        gcongr; linarith

theorem PolyGrowth.eisenstein (c : ℂ) (k : ℕ) :
    PolyGrowth fun n => if n = 0 then 1 else c * ((σ k n : ℕ) : ℂ) := by
  refine ⟨‖c‖ + 1, k + 1, by positivity, fun n => ?_⟩
  have hn1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ (k + 1) := one_le_pow₀ (by simp)
  dsimp only
  split_ifs with hn
  · simp only [norm_one]
    nlinarith [norm_nonneg c]
  · rw [norm_mul, Complex.norm_natCast]
    calc ‖c‖ * (σ k n : ℝ) ≤ ‖c‖ * ((n : ℝ) + 1) ^ (k + 1) := by
          gcongr; exact sigma_le_succ_pow k n
      _ ≤ (‖c‖ + 1) * ((n : ℝ) + 1) ^ (k + 1) := by
          gcongr; linarith

theorem IsQS.add {a b : ℕ → ℂ} {f g : ℍ → ℂ} (hf : IsQS a f) (hg : IsQS b g) :
    IsQS (fun n => a n + b n) (fun τ => f τ + g τ) := by
  intro τ
  simpa [add_mul] using (hf τ).add (hg τ)

theorem IsQS.sub {a b : ℕ → ℂ} {f g : ℍ → ℂ} (hf : IsQS a f) (hg : IsQS b g) :
    IsQS (fun n => a n - b n) (fun τ => f τ - g τ) := by
  intro τ
  simpa [sub_mul] using (hf τ).sub (hg τ)

theorem IsQS.const_mul {a : ℕ → ℂ} {f : ℍ → ℂ} (c : ℂ) (hf : IsQS a f) :
    IsQS (fun n => c * a n) (fun τ => c * f τ) := by
  intro τ
  simpa [mul_assoc] using (hf τ).mul_left c

theorem IsQS.mul {a b : ℕ → ℂ} {f g : ℍ → ℂ} (ha : PolyGrowth a) (hb : PolyGrowth b)
    (hf : IsQS a f) (hg : IsQS b g) :
    IsQS (fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * b p.2) (fun τ => f τ * g τ) := by
  intro τ
  beta_reduce
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (f := fun n => a n * 𝕢₁ τ ^ n) (g := fun n => b n * 𝕢₁ τ ^ n)
    (ha.summable_norm τ) (hb.summable_norm τ)
  have hs : Summable fun n => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      (a kl.1 * 𝕢₁ τ ^ kl.1) * (b kl.2 * 𝕢₁ τ ^ kl.2) :=
    summable_sum_mul_antidiagonal_of_summable_norm'
      (f := fun n => a n * 𝕢₁ τ ^ n) (g := fun n => b n * 𝕢₁ τ ^ n)
      (ha.summable_norm τ) (ha.summable τ) (hb.summable_norm τ) (hb.summable τ)
  rw [(hf τ).tsum_eq, (hg τ).tsum_eq] at hprod
  rw [hprod]
  convert hs.hasSum using 1
  funext n
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
  rw [← hkl, pow_add]
  ring

theorem IsQS.isBoundedAtImInfty {a : ℕ → ℂ} {f : ℍ → ℂ} (ha : PolyGrowth a) (hf : IsQS a f) :
    IsBoundedAtImInfty f := by
  rw [isBoundedAtImInfty_iff]
  set r : ℝ := Real.exp (-2 * π) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    have := Real.pi_pos
    linarith
  refine ⟨∑' n, ‖a n‖ * r ^ n, 1, fun z hz => ?_⟩
  refine (hf z).norm_le_of_bounded (ha.summable_norm_mul hr0 hr1).hasSum fun n => ?_
  rw [norm_mul, norm_pow]
  gcongr
  rw [norm_qParam_one, hr, Real.exp_le_exp, coe_im]
  have := Real.pi_pos
  nlinarith

theorem cuspFunction_one_zero : cuspFunction 1 (0 : ℍ → ℂ) = 0 := by
  simp [cuspFunction, Periodic.cuspFunction]
  exact Filter.Tendsto.limUnder_eq (tendsto_const_nhds.mono_left nhdsWithin_le_nhds)

theorem IsQS.eq_zero {c : ℕ → ℂ} (h : ∀ τ : ℍ, HasSum (fun n => c n * 𝕢₁ τ ^ n) 0) (n : ℕ) :
    c n = 0 := by
  have hana : AnalyticAt ℂ (cuspFunction 1 (0 : ℍ → ℂ)) 0 := by
    rw [cuspFunction_one_zero]; exact analyticAt_const
  have h' : ∀ τ : ℍ, HasSum (fun m => c m • 𝕢₁ τ ^ m) ((0 : ℍ → ℂ) τ) := by
    intro τ; simpa only [smul_eq_mul, Pi.zero_apply] using h τ
  have H := hasFPowerSeriesOnBall_cuspFunction one_pos hana h'
  rw [cuspFunction_one_zero] at H
  have hp := H.hasFPowerSeriesAt.eq_zero
  have := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) hp
  simpa [FormalMultilinearSeries.coeff_ofScalars, FormalMultilinearSeries.coeff_eq_zero.mpr
    (FormalMultilinearSeries.zero_apply (𝕜 := ℂ) (E := ℂ) (F := ℂ) n)] using this

theorem IsQS.unique {c : ℕ → ℂ} {f : ℍ → ℂ} (hf : IsQS c f) (h0 : ∀ τ, f τ = 0) (n : ℕ) :
    c n = 0 :=
  IsQS.eq_zero (fun τ => h0 τ ▸ hf τ) n

open Derivative in
theorem IsQS.theta {a : ℕ → ℂ} {f : ℍ → ℂ} (ha : PolyGrowth a) (hf : IsQS a f) :
    IsQS (fun n => (n : ℂ) * a n) (D f) := by
  intro τ

  set y : ℝ := τ.im / 2 with hy
  have hy0 : 0 < y := by have := τ.im_pos; positivity
  set U : Set ℂ := {w : ℂ | y < w.im} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hτU : (τ : ℂ) ∈ U := by
    show y < (τ : ℂ).im
    rw [coe_im]; have := τ.im_pos; linarith

  set F : ℕ → ℂ → ℂ := fun n w => a n * cexp (2 * π * I * w) ^ n with hF
  have hFq : ∀ (n : ℕ) (w : ℂ), F n w = a n * 𝕢₁ w ^ n := by
    intro n w; simp [hF, qParam_one_eq]
  have hFd : ∀ (n : ℕ) (w : ℂ), HasDerivAt (F n)
      (a n * (n * cexp (2 * π * I * w) ^ (n - 1) * (cexp (2 * π * I * w) * (2 * π * I)))) w := by
    intro n w
    have h1 : HasDerivAt (fun w : ℂ => 2 * π * I * w) (2 * π * I) w := by
      simpa using (hasDerivAt_id w).const_mul (2 * π * I)
    have h2 := h1.cexp
    have h3 := h2.pow n
    exact h3.const_mul (a n)
  have hFdiff : ∀ n, DifferentiableOn ℂ (F n) U :=
    fun n w _ => (hFd n w).differentiableAt.differentiableWithinAt

  set r : ℝ := Real.exp (-2 * π * y) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    have := Real.pi_pos
    nlinarith
  have hbound : ∀ (n : ℕ) (w : ℂ), w ∈ U → ‖F n w‖ ≤ ‖a n‖ * r ^ n := by
    intro n w hw
    rw [hFq, norm_mul, norm_pow]
    gcongr
    rw [norm_qParam_one, hr, Real.exp_le_exp]
    have := Real.pi_pos
    have hw' : y < w.im := hw
    nlinarith
  have hsum := Complex.hasSum_deriv_of_summable_norm (ha.summable_norm_mul hr0 hr1) hFdiff hUo
    hbound hτU

  have hev : (f ∘ ofComplex) =ᶠ[𝓝 (τ : ℂ)] fun w => ∑' n, F n w := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.2] with w hw
    rw [Function.comp_apply, ofComplex_apply_of_im_pos hw]
    have := (hf ⟨w, hw⟩).tsum_eq
    simp only [hFq]
    exact this.symm
  have hderiv : deriv (f ∘ ofComplex) τ = deriv (fun w => ∑' n, F n w) τ := hev.deriv_eq
  simp only [normalizedDerivOfComplex, hderiv]
  have h2 := hsum.mul_left (2 * π * I)⁻¹
  convert h2 using 1
  all_goals try rfl
  funext n
  rw [(hFd n τ).deriv, ← qParam_one_eq]
  have hpi : (2 * π * I : ℂ) ≠ 0 := two_pi_I_ne_zero
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    simp only [Nat.add_sub_cancel, pow_succ, Nat.cast_add, Nat.cast_one]
    field_simp

open Derivative

theorem det_coe_SL (γ : SL(2, ℤ)) : ((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  have := Matrix.SpecialLinearGroup.det_coe (γ.map (Int.castRingHom ℝ))
  simpa using this

theorem denom_SL (γ : SL(2, ℤ)) (z : ℂ) :
    denom (γ : GL (Fin 2) ℝ) z = ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) := by
  simp [denom]

theorem hasDerivAt_comp_smul {F : ℍ → ℂ} (hF : MDiff F) (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => F (γ • ofComplex z))
      (deriv (F ∘ ofComplex) ↑(γ • τ) * (1 / denom (γ : GL (Fin 2) ℝ) τ ^ 2)) τ := by
  have hs := (hasStrictDerivAt_smul (g := (γ : GL (Fin 2) ℝ))
    (by rw [det_coe_SL]; exact one_pos) τ).hasDerivAt
  have hF' : HasDerivAt (F ∘ ofComplex) (deriv (F ∘ ofComplex) ↑(γ • τ))
      ↑((γ : GL (Fin 2) ℝ) • ofComplex (τ : ℂ)) := by
    rw [ofComplex_apply]
    exact (mdifferentiableAt_iff.mp (hF _)).hasDerivAt
  have := hF'.comp (τ : ℂ) hs
  convert this using 1
  all_goals try rfl
  · ext z
    simp only [Function.comp_apply, ofComplex_apply]
    rfl
  · rw [det_coe_SL]; push_cast; ring

theorem hasDerivAt_denom_zpow (k : ℤ) (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => denom (γ : GL (Fin 2) ℝ) z ^ (-k))
      ((-k : ℂ) * denom (γ : GL (Fin 2) ℝ) τ ^ (-k - 1) * ((γ 1 0 : ℤ) : ℂ)) τ := by
  have hden : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  have hlin : HasDerivAt (fun z : ℂ => denom (γ : GL (Fin 2) ℝ) z) ((γ 1 0 : ℤ) : ℂ) τ := by
    simp_rw [denom_SL]
    simpa using ((hasDerivAt_id (τ : ℂ)).const_mul ((γ 1 0 : ℤ) : ℂ)).add_const ((γ 1 1 : ℤ) : ℂ)
  have hz := (hasDerivAt_zpow (-k) (denom (γ : GL (Fin 2) ℝ) τ) (Or.inl hden)).comp (τ : ℂ) hlin
  push_cast at hz
  exact hz

theorem D_apply_smul {F : ℍ → ℂ} (hF : MDiff F) (k : ℤ) (γ : SL(2, ℤ)) (τ : ℍ) :
    D F (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ (k + 2) * D (F ∣[k] γ) τ
        + k * (2 * π * I)⁻¹ * ((γ 1 0 : ℤ) : ℂ) * denom (γ : GL (Fin 2) ℝ) τ * F (γ • τ) := by
  have hden : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  have hprod := (hasDerivAt_comp_smul hF γ τ).mul (hasDerivAt_denom_zpow k γ τ)
  have hev : ((F ∣[k] γ) ∘ ofComplex) =ᶠ[𝓝 (τ : ℂ)]
      fun z : ℂ => F (γ • ofComplex z) * denom (γ : GL (Fin 2) ℝ) z ^ (-k) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.2] with z hz
    rw [Function.comp_apply, ModularForm.SL_slash_apply, ofComplex_apply_of_im_pos hz]
  have hD := hprod.congr_of_eventuallyEq hev
  simp only [Derivative.normalizedDerivOfComplex]
  rw [hD.deriv]
  have e1 : denom (γ : GL (Fin 2) ℝ) τ ^ (-k - 1) =
      (denom (γ : GL (Fin 2) ℝ) τ ^ k)⁻¹ * (denom (γ : GL (Fin 2) ℝ) τ)⁻¹ := by
    rw [sub_eq_add_neg, zpow_add₀ hden, zpow_neg_one, zpow_neg]
  have e2 : denom (γ : GL (Fin 2) ℝ) τ ^ (k + 2) =
      denom (γ : GL (Fin 2) ℝ) τ ^ k * denom (γ : GL (Fin 2) ℝ) τ ^ 2 := by
    rw [zpow_add₀ hden]; norm_cast
  have hk : denom (γ : GL (Fin 2) ℝ) τ ^ k ≠ 0 := zpow_ne_zero k hden
  rw [e1, e2, zpow_neg]
  simp only [ofComplex_apply, Function.comp_def]
  field_simp
  ring

theorem D_apply_smul_of_invariant {F : ℍ → ℂ} (hF : MDiff F) (k : ℕ) (γ : SL(2, ℤ))
    (hinv : F ∣[(k : ℤ)] γ = F) (τ : ℍ) :
    D F (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ (k + 2) * D F τ
        + k * (2 * π * I)⁻¹ * ((γ 1 0 : ℤ) : ℂ) * denom (γ : GL (Fin 2) ℝ) τ ^ (k + 1) * F τ := by
  have hden : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  have hFw : F (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ k * F τ := by
    have h := congrFun hinv τ
    rw [ModularForm.SL_slash_apply, zpow_neg, zpow_natCast] at h
    rw [← h]; field_simp
  have h := D_apply_smul hF k γ τ
  rw [hinv, hFw] at h
  rw [h, show ((k : ℤ) + 2 : ℤ) = ((k + 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  push_cast
  ring

theorem K_eq : (1 / (2 * riemannZeta 2) : ℂ) = -12 * ((2 * π * I)⁻¹) ^ 2 := by
  rw [riemannZeta_two]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring_nf
  rw [I_sq]
  ring

theorem E2_apply_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    E2 (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ 2 * E2 τ
      + 12 * (2 * π * I)⁻¹ * ((γ 1 0 : ℤ) : ℂ) * denom (γ : GL (Fin 2) ℝ) τ := by
  have hden : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := congrFun (E2_slash_action γ) τ
  rw [ModularForm.SL_slash_apply] at h
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, D2] at h
  rw [K_eq, zpow_neg, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast] at h
  have h2 : E2 (γ • τ) = (E2 τ - -12 * ((2 * π * I)⁻¹) ^ 2 *
      (2 * π * I * ((γ 1 0 : ℤ) : ℂ) / denom (γ : GL (Fin 2) ℝ) τ)) *
        denom (γ : GL (Fin 2) ℝ) τ ^ 2 := by
    rw [← h]; field_simp
  rw [h2]
  field_simp
  ring

theorem hasDerivAt_D2 (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (D2 γ ∘ ofComplex)
      (-(2 * π * I) * ((γ 1 0 : ℤ) : ℂ) ^ 2 / denom (γ : GL (Fin 2) ℝ) τ ^ 2) τ := by
  have hden : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  have hlin : HasDerivAt (fun z : ℂ => denom (γ : GL (Fin 2) ℝ) z) ((γ 1 0 : ℤ) : ℂ) τ := by
    simp_rw [denom_SL]
    simpa using ((hasDerivAt_id (τ : ℂ)).const_mul ((γ 1 0 : ℤ) : ℂ)).add_const ((γ 1 1 : ℤ) : ℂ)
  have h := (hlin.inv hden).const_mul (2 * π * I * ((γ 1 0 : ℤ) : ℂ))
  have hev : (fun z : ℂ => 2 * π * I * ((γ 1 0 : ℤ) : ℂ) * (denom (γ : GL (Fin 2) ℝ) z)⁻¹)
      =ᶠ[𝓝 (τ : ℂ)] (D2 γ ∘ ofComplex) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.2] with z hz
    simp only [Function.comp_apply, D2, ofComplex_apply_of_im_pos hz, div_eq_mul_inv]
  convert h.congr_of_eventuallyEq hev.symm using 1
  all_goals try rfl
  field_simp

theorem D_E2_slash (γ : SL(2, ℤ)) (τ : ℍ) :
    D (E2 ∣[(2 : ℤ)] γ) τ =
      D E2 τ + (1 / (2 * riemannZeta 2)) * ((γ 1 0 : ℤ) : ℂ) ^ 2 / denom (γ : GL (Fin 2) ℝ) τ ^ 2 := by
  have hden : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [E2_slash_action γ]
  have h1 : HasDerivAt (E2 ∘ ofComplex) (deriv (E2 ∘ ofComplex) τ) τ :=
    (mdifferentiableAt_iff.mp (E2_mdifferentiable τ)).hasDerivAt
  have h3 := h1.sub ((hasDerivAt_D2 γ τ).const_mul (1 / (2 * riemannZeta 2)))
  have hfun : ((E2 - (1 / (2 * riemannZeta 2)) • D2 γ) ∘ ofComplex) =
      (E2 ∘ ofComplex) - fun z => (1 / (2 * riemannZeta 2)) * (D2 γ ∘ ofComplex) z := by
    funext z; simp [smul_eq_mul]
  simp only [normalizedDerivOfComplex]
  rw [hfun, h3.deriv]
  field_simp
  ring

theorem D_E2_apply_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    D E2 (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ 4 * D E2 τ
      + 2 * (2 * π * I)⁻¹ * ((γ 1 0 : ℤ) : ℂ) * denom (γ : GL (Fin 2) ℝ) τ ^ 3 * E2 τ
      + 12 * ((2 * π * I)⁻¹) ^ 2 * ((γ 1 0 : ℤ) : ℂ) ^ 2 * denom (γ : GL (Fin 2) ℝ) τ ^ 2 := by
  have hden : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [D_apply_smul E2_mdifferentiable 2 γ τ, D_E2_slash, E2_apply_smul, K_eq,
    show ((2 : ℤ) + 2 : ℤ) = ((4 : ℕ) : ℤ) by rfl, zpow_natCast]
  push_cast
  field_simp
  ring

def A4 : ℍ → ℂ := (12 : ℂ) • D E2 - E2 * E2 + ⇑ModularForm.E₄

def B6 : ℍ → ℂ := (3 : ℂ) • D ⇑ModularForm.E₄ - E2 * ⇑ModularForm.E₄ + ⇑ModularForm.E₆

def C8 : ℍ → ℂ :=
  (2 : ℂ) • D ⇑ModularForm.E₆ - E2 * ⇑ModularForm.E₆ + ⇑ModularForm.E₄ * ⇑ModularForm.E₄

theorem A4_apply (τ : ℍ) : A4 τ = 12 * D E2 τ - E2 τ * E2 τ + ModularForm.E₄ τ := by
  simp [A4, smul_eq_mul]

theorem B6_apply (τ : ℍ) :
    B6 τ = 3 * D ⇑ModularForm.E₄ τ - E2 τ * ModularForm.E₄ τ + ModularForm.E₆ τ := by
  simp [B6, smul_eq_mul]

theorem C8_apply (τ : ℍ) : C8 τ =
    2 * D ⇑ModularForm.E₆ τ - E2 τ * ModularForm.E₆ τ + ModularForm.E₄ τ * ModularForm.E₄ τ := by
  simp [C8, smul_eq_mul]

theorem E_slash_eq {k : ℤ} (F : ModularForm 𝒮ℒ k) (γ : SL(2, ℤ)) : (⇑F) ∣[k] γ = ⇑F := by
  rw [ModularForm.SL_slash]
  exact SlashInvariantForm.slash_action_eqn F _ ⟨γ, rfl⟩

theorem E_apply_smul {k : ℕ} (F : ModularForm 𝒮ℒ k) (γ : SL(2, ℤ)) (τ : ℍ) :
    F (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ k * F τ := by
  have hden : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  have h := congrFun (E_slash_eq F γ) τ
  rw [ModularForm.SL_slash_apply, zpow_neg, zpow_natCast] at h
  rw [← h]; field_simp

theorem A4_apply_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    A4 (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ 4 * A4 τ := by
  have h4 := E_apply_smul (k := 4) ModularForm.E₄ γ τ
  rw [A4_apply, A4_apply, D_E2_apply_smul, E2_apply_smul, h4]
  ring

theorem B6_apply_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    B6 (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ 6 * B6 τ := by
  have h4 := E_apply_smul (k := 4) ModularForm.E₄ γ τ
  have h6 := E_apply_smul (k := 6) ModularForm.E₆ γ τ
  have hD := D_apply_smul_of_invariant (ModularFormClass.holo ModularForm.E₄) 4 γ
    (E_slash_eq (k := 4) ModularForm.E₄ γ) τ
  rw [B6_apply, B6_apply, hD, E2_apply_smul, h4, h6]
  push_cast
  ring

theorem C8_apply_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    C8 (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ 8 * C8 τ := by
  have h4 := E_apply_smul (k := 4) ModularForm.E₄ γ τ
  have h6 := E_apply_smul (k := 6) ModularForm.E₆ γ τ
  have hD := D_apply_smul_of_invariant (ModularFormClass.holo ModularForm.E₆) 6 γ
    (E_slash_eq (k := 6) ModularForm.E₆ γ) τ
  rw [C8_apply, C8_apply, hD, E2_apply_smul, h4, h6]
  push_cast
  ring

open PowerSeries

def e2c (n : ℕ) : ℂ := if n = 0 then 1 else -24 * ((σ 1 n : ℕ) : ℂ)

def e4c (n : ℕ) : ℂ := if n = 0 then 1 else 240 * ((σ 3 n : ℕ) : ℂ)

def e6c (n : ℕ) : ℂ := if n = 0 then 1 else -504 * ((σ 5 n : ℕ) : ℂ)

theorem polyGrowth_e2c : PolyGrowth e2c := PolyGrowth.eisenstein _ _
theorem polyGrowth_e4c : PolyGrowth e4c := PolyGrowth.eisenstein _ _
theorem polyGrowth_e6c : PolyGrowth e6c := PolyGrowth.eisenstein _ _

theorem isQS_E2 : IsQS e2c E2 := by
  intro τ
  have hσ : PolyGrowth fun n => ((σ 1 n : ℕ) : ℂ) :=
    ⟨1, 2, zero_le_one, fun n => by
      rw [Complex.norm_natCast, one_mul]; exact sigma_le_succ_pow 1 n⟩
  have hg := hσ.summable τ
  have h1 : ∑' n : ℕ+, ((σ 1 n : ℕ) : ℂ) * cexp (2 * π * I * τ) ^ (n : ℕ) =
      ∑' n : ℕ, ((σ 1 n : ℕ) : ℂ) * 𝕢₁ τ ^ n := by
    rw [← qParam_one_eq,
      tsum_pnat_eq_tsum_succ (f := fun n => ((σ 1 n : ℕ) : ℂ) * 𝕢₁ τ ^ n), hg.tsum_eq_zero_add]
    simp
  have hE : E2 τ = 1 + (-24) * ∑' n : ℕ, ((σ 1 n : ℕ) : ℂ) * 𝕢₁ τ ^ n := by
    rw [E2_eq_tsum_cexp, h1]; ring
  rw [hE]
  convert (hasSum_ite_eq 0 (1 : ℂ)).add (hg.hasSum.mul_left (-24)) using 1
  funext n
  simp only [e2c]
  split_ifs with hn
  · subst hn; simp
  · ring

scoped instance : Fact (IsCusp OnePoint.infty 𝒮ℒ) :=
  ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos one_mem_strictPeriods_SL⟩

theorem isQS_of_levelOne {k : ℤ} (F : ModularForm 𝒮ℒ k) :
    IsQS (fun n => coeff n (qExpansion 1 ⇑F)) ⇑F := by
  intro τ
  simpa only [smul_eq_mul] using hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex F one_mem_strictPeriods_SL)
    (ModularFormClass.holo F) (ModularFormClass.bdd_at_infty F) τ

theorem isQS_E4 : IsQS e4c ModularForm.E₄ := by
  have h := isQS_of_levelOne ModularForm.E₄
  convert h using 2 with n
  rw [E_qExpansion_coeff _ ⟨2, rfl⟩, show bernoulli 4 = -1 / 30 by decide +kernel]
  simp only [e4c]
  split_ifs
  · rfl
  · push_cast; ring

theorem isQS_E6 : IsQS e6c ModularForm.E₆ := by
  have h := isQS_of_levelOne ModularForm.E₆
  convert h using 2 with n
  rw [E_qExpansion_coeff _ ⟨3, rfl⟩, show bernoulli 6 = 1 / 42 by decide +kernel]
  simp only [e6c]
  split_ifs
  · rfl
  · push_cast; ring

def mkLevelOne (k : ℕ) (f : ℍ → ℂ)
    (hcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ k * f τ)
    (hmd : MDiff f) (hbd : IsBoundedAtImInfty f) : ModularForm 𝒮ℒ (k : ℤ) :=
  have hinv : ∀ γ : SL(2, ℤ), f ∣[(k : ℤ)] γ = f := fun γ => by
    funext τ
    rw [ModularForm.SL_slash_apply, hcov, zpow_neg, zpow_natCast]
    have := denom_ne_zero (γ : GL (Fin 2) ℝ) τ
    field_simp
  { toFun := f
    slash_action_eq' := fun A hA => by
      obtain ⟨γ, rfl⟩ := hA
      exact hinv γ
    holo' := hmd
    bdd_at_cusps' := fun {c} hc => by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
      rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
      intro γ _
      rw [hinv γ]
      exact hbd }

@[scoped simp] theorem mkLevelOne_apply (k : ℕ) (f : ℍ → ℂ) (hcov) (hmd) (hbd) (τ : ℍ) :
    mkLevelOne k f hcov hmd hbd τ = f τ := rfl

theorem coeff_eq_zero_of_covariant (k : ℕ) (hk : (k : ℤ) < 12) {a : ℕ → ℂ} {f : ℍ → ℂ}
    (hf : IsQS a f) (ha0 : a 0 = 0) (hmd : MDiff f) (hbd : IsBoundedAtImInfty f)
    (hcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ k * f τ)
    (n : ℕ) : a n = 0 := by
  set F : ModularForm 𝒮ℒ (k : ℤ) := mkLevelOne k f hcov hmd hbd with hFdef
  have hFq : ∀ m, a m = coeff m (qExpansion 1 ⇑F) := fun m =>
    ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_SL (f := F)
      (fun τ => by simpa only [smul_eq_mul, hFdef, mkLevelOne_apply] using hf τ) m
  have h0 : coeff 0 (qExpansion 1 ⇑F) = 0 := (hFq 0).symm.trans ha0
  have hG : F.toCuspForm h0 = 0 :=
    rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve hk) _
  have hf0 : ∀ τ, f τ = 0 := fun τ => by
    have := congrArg (fun G : CuspForm 𝒮ℒ (k : ℤ) => G τ) hG
    simpa [ModularForm.toCuspForm_apply, hFdef, mkLevelOne_apply] using this
  exact hf.unique hf0 n

def cauchy (a b : ℕ → ℂ) (n : ℕ) : ℂ := ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * b p.2

theorem mdiff_E4 : MDiff (⇑ModularForm.E₄ : ℍ → ℂ) := ModularFormClass.holo _
theorem mdiff_E6 : MDiff (⇑ModularForm.E₆ : ℍ → ℂ) := ModularFormClass.holo _
theorem mdiff_D_E2 : MDiff (D E2) := normalizedDerivOfComplex_mdifferentiable E2_mdifferentiable
theorem mdiff_D_E4 : MDiff (D ⇑ModularForm.E₄) := normalizedDerivOfComplex_mdifferentiable mdiff_E4
theorem mdiff_D_E6 : MDiff (D ⇑ModularForm.E₆) := normalizedDerivOfComplex_mdifferentiable mdiff_E6

theorem bdd_E2 : IsBoundedAtImInfty E2 := isQS_E2.isBoundedAtImInfty polyGrowth_e2c
theorem bdd_E4 : IsBoundedAtImInfty (⇑ModularForm.E₄ : ℍ → ℂ) :=
  isQS_E4.isBoundedAtImInfty polyGrowth_e4c
theorem bdd_E6 : IsBoundedAtImInfty (⇑ModularForm.E₆ : ℍ → ℂ) :=
  isQS_E6.isBoundedAtImInfty polyGrowth_e6c
theorem bdd_D_E2 : IsBoundedAtImInfty (D E2) :=
  (isQS_E2.theta polyGrowth_e2c).isBoundedAtImInfty polyGrowth_e2c.theta
theorem bdd_D_E4 : IsBoundedAtImInfty (D ⇑ModularForm.E₄) :=
  (isQS_E4.theta polyGrowth_e4c).isBoundedAtImInfty polyGrowth_e4c.theta
theorem bdd_D_E6 : IsBoundedAtImInfty (D ⇑ModularForm.E₆) :=
  (isQS_E6.theta polyGrowth_e6c).isBoundedAtImInfty polyGrowth_e6c.theta

theorem identity_A (n : ℕ) : 12 * ((n : ℂ) * e2c n) - (cauchy e2c e2c n - e4c n) = 0 := by
  refine coeff_eq_zero_of_covariant 4 (by norm_num)
    (a := fun n => 12 * ((n : ℂ) * e2c n) - (cauchy e2c e2c n - e4c n)) (f := A4) ?_ ?_ ?_ ?_
    A4_apply_smul n
  · intro τ
    have h := (((isQS_E2.theta polyGrowth_e2c).const_mul 12).sub
      ((isQS_E2.mul polyGrowth_e2c polyGrowth_e2c isQS_E2).sub isQS_E4)) τ
    have e : A4 τ = 12 * D E2 τ - (E2 τ * E2 τ - ModularForm.E₄ τ) := by rw [A4_apply]; ring
    rw [e]; exact h
  · simp [cauchy, e2c, e4c]
  · exact ((mdiff_D_E2.const_smul (12 : ℂ)).sub (E2_mdifferentiable.mul E2_mdifferentiable)).add
      mdiff_E4
  · exact Filter.BoundedAtFilter.add (Filter.BoundedAtFilter.add
      (Filter.BoundedAtFilter.smul (12 : ℂ) bdd_D_E2)
      (Filter.BoundedAtFilter.neg (Filter.BoundedAtFilter.mul bdd_E2 bdd_E2))) bdd_E4

theorem identity_B (n : ℕ) : 3 * ((n : ℂ) * e4c n) - (cauchy e2c e4c n - e6c n) = 0 := by
  refine coeff_eq_zero_of_covariant 6 (by norm_num)
    (a := fun n => 3 * ((n : ℂ) * e4c n) - (cauchy e2c e4c n - e6c n)) (f := B6) ?_ ?_ ?_ ?_
    B6_apply_smul n
  · intro τ
    have h := (((isQS_E4.theta polyGrowth_e4c).const_mul 3).sub
      ((isQS_E2.mul polyGrowth_e2c polyGrowth_e4c isQS_E4).sub isQS_E6)) τ
    have e : B6 τ = 3 * D ⇑ModularForm.E₄ τ - (E2 τ * ModularForm.E₄ τ - ModularForm.E₆ τ) := by
      rw [B6_apply]; ring
    rw [e]; exact h
  · simp [cauchy, e2c, e4c, e6c]
  · exact ((mdiff_D_E4.const_smul (3 : ℂ)).sub (E2_mdifferentiable.mul mdiff_E4)).add mdiff_E6
  · exact Filter.BoundedAtFilter.add (Filter.BoundedAtFilter.add
      (Filter.BoundedAtFilter.smul (3 : ℂ) bdd_D_E4)
      (Filter.BoundedAtFilter.neg (Filter.BoundedAtFilter.mul bdd_E2 bdd_E4))) bdd_E6

theorem identity_C (n : ℕ) :
    2 * ((n : ℂ) * e6c n) - (cauchy e2c e6c n - cauchy e4c e4c n) = 0 := by
  refine coeff_eq_zero_of_covariant 8 (by norm_num)
    (a := fun n => 2 * ((n : ℂ) * e6c n) - (cauchy e2c e6c n - cauchy e4c e4c n)) (f := C8)
    ?_ ?_ ?_ ?_ C8_apply_smul n
  · intro τ
    have h := (((isQS_E6.theta polyGrowth_e6c).const_mul 2).sub
      ((isQS_E2.mul polyGrowth_e2c polyGrowth_e6c isQS_E6).sub
        (isQS_E4.mul polyGrowth_e4c polyGrowth_e4c isQS_E4))) τ
    have e : C8 τ = 2 * D ⇑ModularForm.E₆ τ -
        (E2 τ * ModularForm.E₆ τ - ModularForm.E₄ τ * ModularForm.E₄ τ) := by
      rw [C8_apply]; ring
    rw [e]; exact h
  · simp [cauchy, e2c, e4c, e6c]
  · exact ((mdiff_D_E6.const_smul (2 : ℂ)).sub (E2_mdifferentiable.mul mdiff_E6)).add
      (mdiff_E4.mul mdiff_E4)
  · exact Filter.BoundedAtFilter.add (Filter.BoundedAtFilter.add
      (Filter.BoundedAtFilter.smul (2 : ℂ) bdd_D_E6)
      (Filter.BoundedAtFilter.neg (Filter.BoundedAtFilter.mul bdd_E2 bdd_E6)))
      (Filter.BoundedAtFilter.mul bdd_E4 bdd_E4)

theorem coeff_X_mul_derivative (φ : PowerSeries ℤ) (n : ℕ) :
    coeff n (X * derivative ℤ φ) = (n : ℤ) * coeff n φ := by
  cases n with
  | zero => simp [coeff_zero_X_mul]
  | succ m => rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

theorem coeff_ofNat_mul (c : ℕ) [c.AtLeastTwo] (φ : PowerSeries ℤ) (n : ℕ) :
    coeff n ((OfNat.ofNat c : PowerSeries ℤ) * φ) = (OfNat.ofNat c : ℤ) * coeff n φ := by
  rw [show (OfNat.ofNat c : PowerSeries ℤ) = C (OfNat.ofNat c : ℤ) from by simp, coeff_C_mul]

theorem cast_coeff_mul (φ ψ : PowerSeries ℤ) (n : ℕ) :
    ((coeff n (φ * ψ) : ℤ) : ℂ) =
      cauchy (fun m => ((coeff m φ : ℤ) : ℂ)) (fun m => ((coeff m ψ : ℤ) : ℂ)) n := by
  rw [PowerSeries.coeff_mul, cauchy]; push_cast; rfl

theorem cast_coeff_P (n : ℕ) :
    ((coeff n (PowerSeries.mk fun n => if n = 0 then 1 else -24 * ∑ d ∈ n.divisors, (d : ℤ)) : ℤ) :
      ℂ) = e2c n := by
  rw [coeff_mk, e2c, ArithmeticFunction.sigma_one_apply]
  split_ifs <;> push_cast <;> ring

theorem cast_coeff_Q (n : ℕ) :
    ((coeff n (PowerSeries.mk fun n => if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3) :
      ℤ) : ℂ) = e4c n := by
  rw [coeff_mk, e4c, ArithmeticFunction.sigma_apply]
  split_ifs <;> push_cast <;> ring

theorem cast_coeff_R (n : ℕ) :
    ((coeff n (PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5) :
      ℤ) : ℂ) = e6c n := by
  rw [coeff_mk, e6c, ArithmeticFunction.sigma_apply]
  split_ifs <;> push_cast <;> ring

end EisensteinSeries.RamanujanSystemInt
p2m_reactivate "P2MW.S_EisensteinSeries_ramanujan_system_qExpansion_int.EisensteinSeries P2MW.S_EisensteinSeries_ramanujan_system_qExpansion_int.EisensteinSeries.RamanujanSystemInt"
p2m_reactivate "P2MW.S_EisensteinSeries_ramanujan_system_qExpansion_int.EisensteinSeries"

end
p2m_reactivate "P2MW.S_EisensteinSeries_ramanujan_system_qExpansion_int.EisensteinSeries P2MW.S_EisensteinSeries_ramanujan_system_qExpansion_int.EisensteinSeries.RamanujanSystemInt"

open EisensteinSeries.RamanujanSystemInt PowerSeries in

theorem solution
    (P Q R : PowerSeries ℤ)
    (hP : P = PowerSeries.mk fun n => if n = 0 then 1 else -24 * ∑ d ∈ n.divisors, (d : ℤ))
    (hQ : Q = PowerSeries.mk fun n => if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3)
    (hR : R = PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5) :
    12 * (PowerSeries.X * PowerSeries.derivative ℤ P) = P ^ 2 - Q ∧
      3 * (PowerSeries.X * PowerSeries.derivative ℤ Q) = P * Q - R ∧
        2 * (PowerSeries.X * PowerSeries.derivative ℤ R) = P * R - Q ^ 2 := by
  have hPc : ∀ n, ((coeff n P : ℤ) : ℂ) = e2c n := fun n => hP ▸ cast_coeff_P n
  have hQc : ∀ n, ((coeff n Q : ℤ) : ℂ) = e4c n := fun n => hQ ▸ cast_coeff_Q n
  have hRc : ∀ n, ((coeff n R : ℤ) : ℂ) = e6c n := fun n => hR ▸ cast_coeff_R n
  have hPf : (fun n => ((coeff n P : ℤ) : ℂ)) = e2c := funext hPc
  have hQf : (fun n => ((coeff n Q : ℤ) : ℂ)) = e4c := funext hQc
  have hRf : (fun n => ((coeff n R : ℤ) : ℂ)) = e6c := funext hRc
  refine ⟨?_, ?_, ?_⟩
  · refine PowerSeries.ext fun n => Int.cast_injective (α := ℂ) ?_
    rw [coeff_ofNat_mul, coeff_X_mul_derivative, map_sub, sq, Int.cast_mul, Int.cast_mul,
      Int.cast_sub, cast_coeff_mul, hPf, hPc, hQc]
    push_cast
    linear_combination identity_A n
  · refine PowerSeries.ext fun n => Int.cast_injective (α := ℂ) ?_
    rw [coeff_ofNat_mul, coeff_X_mul_derivative, map_sub, Int.cast_mul, Int.cast_mul,
      Int.cast_sub, cast_coeff_mul, hPf, hQf, hQc, hRc]
    push_cast
    linear_combination identity_B n
  · refine PowerSeries.ext fun n => Int.cast_injective (α := ℂ) ?_
    rw [coeff_ofNat_mul, coeff_X_mul_derivative, map_sub, sq, Int.cast_mul, Int.cast_mul,
      Int.cast_sub, cast_coeff_mul, cast_coeff_mul, hPf, hQf, hRf, hRc]
    push_cast
    linear_combination identity_C n

end S_EisensteinSeries_ramanujan_system_qExpansion_int
end P2MW
export P2MW.S_EisensteinSeries_ramanujan_system_qExpansion_int (solution)
