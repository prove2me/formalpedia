-- Prove2me | solution 1 for CauchyRiemannIndex.gaussian_poincare_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T13:41:08.590291+00:00
-- url     : https://prove2.me/submissions/59adfb6b-5a6b-48e5-94c6-b3a3435bcaeb

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Exponential



/-! One-dimensional Gaussian-weighted Poincaré inequality on an interval starting at the centre. -/

namespace GPoin

open Real MeasureTheory intervalIntegral Set

lemma half_aux (σ : ℝ) (hσ : 0 < σ) (L : ℝ) (hL : 0 ≤ L) (F F' : ℝ → ℝ)
    (hF : ∀ s, HasDerivAt F (F' s) s) (hF' : Continuous F') (h0 : F 0 = 0) :
    ∫ s in (0:ℝ)..L, F s ^ 2 * exp (-σ * s ^ 2) ≤
      4 / σ * ∫ s in (0:ℝ)..L, F' s ^ 2 * exp (-σ * s ^ 2) := by
  obtain ⟨q, hqdef⟩ : ∃ q, q = sqrt σ := ⟨_, rfl⟩
  have hq : 0 < q := hqdef ▸ sqrt_pos.2 hσ
  have hqq : q * q = σ := hqdef ▸ mul_self_sqrt hσ.le
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun s => (hF s).continuousAt
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → ℝ, φ = fun s => exp (-σ * s ^ 2) := ⟨_, rfl⟩
  have hφc : Continuous φ := by rw [hφ]; fun_prop
  have hφp : ∀ x, 0 < φ x := fun x => by rw [hφ]; exact exp_pos _
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ → ℝ, ψ = fun s => φ s / (1 + q * s) := ⟨_, rfl⟩
  obtain ⟨ψ', hψ'⟩ : ∃ ψ' : ℝ → ℝ,
      ψ' = fun s => (-σ * (2 * s)) * φ s / (1 + q * s) - φ s * q / (1 + q * s) ^ 2 := ⟨_, rfl⟩
  have hden : ∀ x ∈ Icc (0:ℝ) L, 0 < 1 + q * x := fun x hx => by nlinarith [hx.1]
  have hden' : ∀ x ∈ uIcc (0:ℝ) L, 0 < 1 + q * x := fun x hx => by
    rw [uIcc_of_le hL] at hx; exact hden x hx
  have hφd : ∀ x, HasDerivAt φ ((-σ * (2 * x)) * φ x) x := by
    intro x
    rw [hφ]
    exact (((hasDerivAt_pow 2 x).const_mul (-σ)).exp).congr_deriv (by norm_num; ring)
  have hψd : ∀ x ∈ uIcc (0:ℝ) L, HasDerivAt ψ (ψ' x) x := by
    intro x hx
    have hd : HasDerivAt (fun s : ℝ => 1 + q * s) q x := by
      simpa using ((hasDerivAt_id x).const_mul q).const_add 1
    have hne := (hden' x hx).ne'
    have := (hφd x).div hd hne
    rw [hψ, hψ']
    refine this.congr_deriv ?_
    field_simp
  have hd : ∀ x ∈ uIcc (0:ℝ) L, HasDerivAt (fun s => F s ^ 2 * ψ s)
      (2 * F x * F' x * ψ x + F x ^ 2 * ψ' x) x := by
    intro x hx
    have h2 : HasDerivAt (fun s => F s ^ 2) (2 * F x * F' x) x :=
      ((hF x).pow 2).congr_deriv (by norm_num)
    exact h2.mul (hψd x hx)
  have hcont : ContinuousOn (fun x => 2 * F x * F' x * ψ x + F x ^ 2 * ψ' x) (uIcc 0 L) := by
    have hc1 : ContinuousOn (fun x => 1 + q * x) (uIcc 0 L) := by fun_prop
    rw [hψ, hψ']
    refine ContinuousOn.add ?_ ?_
    · refine (by fun_prop : ContinuousOn (fun x => 2 * F x * F' x) _).mul ?_
      exact hφc.continuousOn.div hc1 fun x hx => (hden' x hx).ne'
    · refine (by fun_prop : ContinuousOn (fun x => F x ^ 2) _).mul ?_
      refine ContinuousOn.sub ?_ ?_
      · exact (by fun_prop : ContinuousOn (fun x => (-σ * (2 * x)) * φ x) _).div hc1
          fun x hx => (hden' x hx).ne'
      · exact (by fun_prop : ContinuousOn (fun x => φ x * q) _).div (hc1.pow 2)
          fun x hx => pow_ne_zero 2 (hden' x hx).ne'
  have key := integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable)
  have hK : 0 ≤ ∫ x in (0:ℝ)..L, (2 * F x * F' x * ψ x + F x ^ 2 * ψ' x) := by
    rw [key, h0, hψ]
    have : 0 ≤ F L ^ 2 * (φ L / (1 + q * L)) :=
      mul_nonneg (sq_nonneg _) (div_nonneg (hφp L).le (hden L ⟨hL, le_rfl⟩).le)
    simpa using this
  -- pointwise bound
  have hpt : ∀ x ∈ Icc (0:ℝ) L, q * (F x ^ 2 * φ x) + (2 * F x * F' x * ψ x + F x ^ 2 * ψ' x) ≤
      q / 2 * (F x ^ 2 * φ x) + 2 / q * (F' x ^ 2 * φ x) := by
    intro x hx
    have hd0 := hden x hx
    have hφx := hφp x
    have hψ'le : ψ' x + q * φ x = -(q * φ x * (q * x) ^ 2 / (1 + q * x) ^ 2) := by
      rw [hψ', ← hqq]
      field_simp
      ring
    have h1 : F x ^ 2 * ψ' x ≤ -(q * (F x ^ 2 * φ x)) := by
      have hpos : 0 ≤ q * φ x * (q * x) ^ 2 / (1 + q * x) ^ 2 :=
        div_nonneg (mul_nonneg (mul_nonneg hq.le hφx.le) (sq_nonneg _)) (sq_nonneg _)
      have : ψ' x ≤ -(q * φ x) := by linarith
      nlinarith [sq_nonneg (F x)]
    have h2 : 2 * F x * F' x * ψ x ≤ 2 * |F x| * |F' x| * φ x := by
      have hψle : ψ x ≤ φ x := by
        rw [hψ]
        show φ x / (1 + q * x) ≤ φ x
        rw [div_le_iff₀ hd0]
        nlinarith [mul_nonneg (mul_nonneg hφx.le hq.le) hx.1]
      have hψ0 : 0 ≤ ψ x := by rw [hψ]; exact div_nonneg hφx.le hd0.le
      have : 2 * F x * F' x ≤ 2 * |F x| * |F' x| := by
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_left (by rw [← abs_mul]; exact le_abs_self _) (by norm_num)
      calc 2 * F x * F' x * ψ x ≤ 2 * |F x| * |F' x| * ψ x :=
            mul_le_mul_of_nonneg_right this hψ0
        _ ≤ 2 * |F x| * |F' x| * φ x :=
            mul_le_mul_of_nonneg_left hψle (by positivity)
    have h3 : 2 * |F x| * |F' x| * φ x ≤ q / 2 * (F x ^ 2 * φ x) + 2 / q * (F' x ^ 2 * φ x) := by
      have e1 : F x ^ 2 = |F x| ^ 2 := (sq_abs _).symm
      have e2 : F' x ^ 2 = |F' x| ^ 2 := (sq_abs _).symm
      rw [e1, e2]
      have : 2 * |F x| * |F' x| ≤ q / 2 * |F x| ^ 2 + 2 / q * |F' x| ^ 2 := by
        have hsq : 0 ≤ (q * |F x| - 2 * |F' x|) ^ 2 := sq_nonneg _
        have : q / 2 * |F x| ^ 2 + 2 / q * |F' x| ^ 2 - 2 * |F x| * |F' x| =
            (q * |F x| - 2 * |F' x|) ^ 2 / (2 * q) := by
          field_simp; ring
        have : 0 ≤ (q * |F x| - 2 * |F' x|) ^ 2 / (2 * q) := div_nonneg hsq (by positivity)
        linarith
      nlinarith
    linarith
  have hi1 : IntervalIntegrable (fun x => F x ^ 2 * φ x) volume 0 L :=
    (by fun_prop : Continuous fun x => F x ^ 2 * φ x).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x => F' x ^ 2 * φ x) volume 0 L :=
    (by fun_prop : Continuous fun x => F' x ^ 2 * φ x).intervalIntegrable _ _
  have hmono := integral_mono_on hL ((hi1.const_mul q).add hcont.intervalIntegrable)
    ((hi1.const_mul (q / 2)).add (hi2.const_mul (2 / q))) hpt
  rw [intervalIntegral.integral_add (hi1.const_mul q) hcont.intervalIntegrable,
    intervalIntegral.integral_add (hi1.const_mul (q / 2)) (hi2.const_mul (2 / q)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hmono
  have hX : ∫ s in (0:ℝ)..L, F s ^ 2 * exp (-σ * s ^ 2) = ∫ x in (0:ℝ)..L, F x ^ 2 * φ x := by
    rw [hφ]
  have hY : ∫ s in (0:ℝ)..L, F' s ^ 2 * exp (-σ * s ^ 2) = ∫ x in (0:ℝ)..L, F' x ^ 2 * φ x := by
    rw [hφ]
  rw [hX, hY]
  set X := ∫ x in (0:ℝ)..L, F x ^ 2 * φ x
  set Y := ∫ x in (0:ℝ)..L, F' x ^ 2 * φ x
  have : q / 2 * X ≤ 2 / q * Y := by linarith
  have h4 : 4 / σ = (2 / q) / (q / 2) := by rw [← hqq]; field_simp; ring
  rw [h4, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

/-- Centred one-dimensional Gaussian Poincaré inequality on `[a - L, a + L]`. -/
lemma centred (σ : ℝ) (hσ : 0 < σ) (a L : ℝ) (hL : 0 ≤ L) (f f' : ℝ → ℝ)
    (hf : ∀ s, HasDerivAt f (f' s) s) (hf' : Continuous f') :
    ∫ s in (a - L)..(a + L), (f s - f a) ^ 2 * exp (-σ * (s - a) ^ 2) ≤
      4 / σ * ∫ s in (a - L)..(a + L), f' s ^ 2 * exp (-σ * (s - a) ^ 2) := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun s => (hf s).continuousAt
  -- right half
  have hR := half_aux σ hσ L hL (fun u => f (a + u) - f a) (fun u => f' (a + u))
    (fun u => by
      have := (hf (a + u)).comp u ((hasDerivAt_id u).const_add a)
      exact (this.sub_const (f a)).congr_deriv (by simp))
    (hf'.comp (continuous_const.add continuous_id)) (by simp)
  have eR1 : ∫ u in (0:ℝ)..L, (f (a + u) - f a) ^ 2 * exp (-σ * u ^ 2) =
      ∫ s in a..(a + L), (f s - f a) ^ 2 * exp (-σ * (s - a) ^ 2) := by
    have := intervalIntegral.integral_comp_add_left
      (fun s => (f s - f a) ^ 2 * exp (-σ * (s - a) ^ 2)) (a := 0) (b := L) a
    simp only [add_zero, add_sub_cancel_left] at this
    exact this
  have eR2 : ∫ u in (0:ℝ)..L, f' (a + u) ^ 2 * exp (-σ * u ^ 2) =
      ∫ s in a..(a + L), f' s ^ 2 * exp (-σ * (s - a) ^ 2) := by
    have := intervalIntegral.integral_comp_add_left
      (fun s => f' s ^ 2 * exp (-σ * (s - a) ^ 2)) (a := 0) (b := L) a
    simp only [add_zero, add_sub_cancel_left] at this
    exact this
  -- left half
  have hLh := half_aux σ hσ L hL (fun u => f (a - u) - f a) (fun u => -f' (a - u))
    (fun u => by
      have := (hf (a - u)).comp u ((hasDerivAt_id u).const_sub a)
      exact (this.sub_const (f a)).congr_deriv (by simp))
    (hf'.comp (continuous_const.sub continuous_id)).neg (by simp)
  have eL1 : ∫ u in (0:ℝ)..L, (f (a - u) - f a) ^ 2 * exp (-σ * u ^ 2) =
      ∫ s in (a - L)..a, (f s - f a) ^ 2 * exp (-σ * (s - a) ^ 2) := by
    have := intervalIntegral.integral_comp_sub_left
      (fun s => (f s - f a) ^ 2 * exp (-σ * (s - a) ^ 2)) (a := 0) (b := L) a
    simp only [sub_zero, sub_sub_cancel_left, neg_sq] at this
    exact this
  have eL2 : ∫ u in (0:ℝ)..L, (-f' (a - u)) ^ 2 * exp (-σ * u ^ 2) =
      ∫ s in (a - L)..a, f' s ^ 2 * exp (-σ * (s - a) ^ 2) := by
    have := intervalIntegral.integral_comp_sub_left
      (fun s => f' s ^ 2 * exp (-σ * (s - a) ^ 2)) (a := 0) (b := L) a
    simp only [sub_zero, sub_sub_cancel_left, neg_sq] at this
    simpa only [neg_sq] using this
  rw [eR1, eR2] at hR
  rw [eL1, eL2] at hLh
  have hc1 : Continuous fun s => (f s - f a) ^ 2 * exp (-σ * (s - a) ^ 2) := by fun_prop
  have hc2 : Continuous fun s => f' s ^ 2 * exp (-σ * (s - a) ^ 2) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := a) (hc1.intervalIntegrable _ _)
      (hc1.intervalIntegrable _ _),
    ← intervalIntegral.integral_add_adjacent_intervals (b := a) (hc2.intervalIntegrable _ _)
      (hc2.intervalIntegrable _ _)]
  linarith

end GPoin

/-! Gaussian Poincaré inequality on a rectangle. -/

namespace GPoin

open Real MeasureTheory Set

section mean

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma sq_expand (h φ : α → ℝ) (hA : Integrable (fun s => h s ^ 2 * φ s) μ)
    (hB : Integrable (fun s => h s * φ s) μ) (hZ : Integrable φ μ) (c : ℝ) :
    ∫ s, (h s - c) ^ 2 * φ s ∂μ =
      ∫ s, h s ^ 2 * φ s ∂μ - 2 * c * ∫ s, h s * φ s ∂μ + c ^ 2 * ∫ s, φ s ∂μ := by
  have : (fun s => (h s - c) ^ 2 * φ s) =
      fun s => (h s ^ 2 * φ s - 2 * c * (h s * φ s)) + c ^ 2 * φ s := by funext s; ring
  rw [this, integral_add ?_ (hZ.const_mul _), integral_sub hA (hB.const_mul _),
    integral_const_mul, integral_const_mul]
  exact hA.sub (hB.const_mul _)

lemma mean_min (h φ : α → ℝ) (hA : Integrable (fun s => h s ^ 2 * φ s) μ)
    (hB : Integrable (fun s => h s * φ s) μ) (hZ : Integrable φ μ) (hZp : 0 < ∫ s, φ s ∂μ)
    (c : ℝ) :
    ∫ s, (h s - (∫ s, h s * φ s ∂μ) / ∫ s, φ s ∂μ) ^ 2 * φ s ∂μ ≤ ∫ s, (h s - c) ^ 2 * φ s ∂μ := by
  rw [sq_expand h φ hA hB hZ, sq_expand h φ hA hB hZ]
  set B := ∫ s, h s * φ s ∂μ
  set Z := ∫ s, φ s ∂μ
  have : (B / Z) ^ 2 * Z - 2 * (B / Z) * B ≤ c ^ 2 * Z - 2 * c * B := by
    have e : c ^ 2 * Z - 2 * c * B - ((B / Z) ^ 2 * Z - 2 * (B / Z) * B) = Z * (c - B / Z) ^ 2 := by
      field_simp; ring
    nlinarith [mul_nonneg hZp.le (sq_nonneg (c - B / Z))]
  linarith

lemma jensen (h φ : α → ℝ) (hφ : ∀ s, 0 ≤ φ s) (hA : Integrable (fun s => h s ^ 2 * φ s) μ)
    (hB : Integrable (fun s => h s * φ s) μ) (hZ : Integrable φ μ) (hZp : 0 < ∫ s, φ s ∂μ) :
    (∫ s, h s * φ s ∂μ) ^ 2 ≤ (∫ s, φ s ∂μ) * ∫ s, h s ^ 2 * φ s ∂μ := by
  have h0 : 0 ≤ ∫ s, (h s - (∫ s, h s * φ s ∂μ) / ∫ s, φ s ∂μ) ^ 2 * φ s ∂μ :=
    integral_nonneg fun s => mul_nonneg (sq_nonneg _) (hφ s)
  rw [sq_expand h φ hA hB hZ] at h0
  set B := ∫ s, h s * φ s ∂μ
  set Z := ∫ s, φ s ∂μ
  set A := ∫ s, h s ^ 2 * φ s ∂μ
  have e : A - 2 * (B / Z) * B + (B / Z) ^ 2 * Z = (Z * A - B ^ 2) / Z := by field_simp; ring
  rw [e] at h0
  have := (div_nonneg_iff.1 h0)
  rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
  · linarith
  · linarith

end mean

/-- The centred one-dimensional inequality as a set integral over `Icc`. -/
lemma centred_set (σ : ℝ) (hσ : 0 < σ) (a L : ℝ) (hL : 0 ≤ L) (f f' : ℝ → ℝ)
    (hf : ∀ s, HasDerivAt f (f' s) s) (hf' : Continuous f') :
    ∫ s in Icc (a - L) (a + L), (f s - f a) ^ 2 * exp (-σ * (s - a) ^ 2) ≤
      4 / σ * ∫ s in Icc (a - L) (a + L), f' s ^ 2 * exp (-σ * (s - a) ^ 2) := by
  have h := centred σ hσ a L hL f f' hf hf'
  rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith)]
    at h
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
  exact h

lemma cont_param_s {F : ℝ × ℝ → ℝ} (hF : Continuous F) (I : Set ℝ) (hI : IsCompact I) :
    Continuous fun t => ∫ s in I, F (s, t) :=
  continuous_parametric_integral_of_continuous (f := fun t s => F (s, t))
    (hF.comp (continuous_snd.prodMk continuous_fst)) hI

lemma cont_param_t {F : ℝ × ℝ → ℝ} (hF : Continuous F) (J : Set ℝ) (hJ : IsCompact J) :
    Continuous fun s => ∫ t in J, F (s, t) :=
  continuous_parametric_integral_of_continuous (f := fun s t => F (s, t)) hF hJ

lemma restrict_prod (I J : Set ℝ) :
    (volume : Measure (ℝ × ℝ)).restrict (I ×ˢ J) = (volume.restrict I).prod (volume.restrict J) := by
  rw [Measure.volume_eq_prod, Measure.prod_restrict]

lemma integrable_box {F : ℝ × ℝ → ℝ} (hF : Continuous F) (a b c d : ℝ) :
    Integrable F ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
  rw [← restrict_prod]
  exact hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

/-- Iterated form, `s` inside. -/
lemma iter_t {F : ℝ × ℝ → ℝ} (hF : Continuous F) (φ₁ φ₂ : ℝ → ℝ) (h1 : Continuous φ₁)
    (h2 : Continuous φ₂) (a b c d : ℝ) :
    ∫ x, F x * (φ₁ x.1 * φ₂ x.2) ∂((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) =
      ∫ t in Icc c d, φ₂ t * ∫ s in Icc a b, F (s, t) * φ₁ s := by
  rw [integral_prod_symm _ (integrable_box (by fun_prop) a b c d)]
  congr 1; funext t
  rw [← integral_const_mul]
  congr 1; funext s; ring

/-- Iterated form, `t` inside. -/
lemma iter_s {F : ℝ × ℝ → ℝ} (hF : Continuous F) (φ₁ φ₂ : ℝ → ℝ) (h1 : Continuous φ₁)
    (h2 : Continuous φ₂) (a b c d : ℝ) :
    ∫ x, F x * (φ₁ x.1 * φ₂ x.2) ∂((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) =
      ∫ s in Icc a b, φ₁ s * ∫ t in Icc c d, F (s, t) * φ₂ t := by
  rw [integral_prod _ (integrable_box (by fun_prop) a b c d)]
  congr 1; funext s
  rw [← integral_const_mul]
  congr 1; funext t; ring

lemma hasDerivAt_slice_s {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 1 g) (s t : ℝ) :
    HasDerivAt (fun s => g (s, t)) (fderiv ℝ g (s, t) (1, 0)) s := by
  have h1 : HasDerivAt (fun s : ℝ => (s, t)) ((1 : ℝ), (0 : ℝ)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s t)
  exact ((hg.differentiable (by simp)) (s, t)).hasFDerivAt.comp_hasDerivAt s h1

lemma hasDerivAt_slice_t {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 1 g) (s t : ℝ) :
    HasDerivAt (fun t => g (s, t)) (fderiv ℝ g (s, t) (0, 1)) t := by
  have h1 : HasDerivAt (fun t : ℝ => (s, t)) ((0 : ℝ), (1 : ℝ)) t :=
    (hasDerivAt_const t s).prodMk (hasDerivAt_id t)
  exact ((hg.differentiable (by simp)) (s, t)).hasFDerivAt.comp_hasDerivAt t h1

lemma integral_exp_Icc_pos (σ a L : ℝ) (hL : 0 < L) :
    0 < ∫ s in Icc (a - L) (a + L), exp (-σ * (s - a) ^ 2) := by
  have : NeZero (volume.restrict (Icc (a - L) (a + L))) := ⟨by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc]; simp; linarith⟩
  exact integral_exp_pos ((by fun_prop : Continuous fun s => exp (-σ * (s - a) ^ 2)).continuousOn
    |>.integrableOn_compact isCompact_Icc)

/-- Gaussian Poincaré inequality on a rectangle. -/
theorem rect (σ : ℝ) (hσ : 0 < σ) (a b L M : ℝ) (hL : 0 < L) (hM : 0 < M) (g : ℝ × ℝ → ℝ)
    (hg : ContDiff ℝ 1 g) :
    ∃ c : ℝ, ∫ x in Icc (a - L) (a + L) ×ˢ Icc (b - M) (b + M),
        (g x - c) ^ 2 * exp (-σ * ((x.1 - a) ^ 2 + (x.2 - b) ^ 2)) ≤
      8 / σ * ∫ x in Icc (a - L) (a + L) ×ˢ Icc (b - M) (b + M),
        ((fderiv ℝ g x (1, 0)) ^ 2 + (fderiv ℝ g x (0, 1)) ^ 2) *
          exp (-σ * ((x.1 - a) ^ 2 + (x.2 - b) ^ 2)) := by
  set I := Icc (a - L) (a + L) with hI
  set J := Icc (b - M) (b + M) with hJ
  set μ := volume.restrict I
  set ν := volume.restrict J
  set φ₁ : ℝ → ℝ := fun s => exp (-σ * (s - a) ^ 2) with hφ₁
  set φ₂ : ℝ → ℝ := fun t => exp (-σ * (t - b) ^ 2) with hφ₂
  have c1 : Continuous φ₁ := by fun_prop
  have c2 : Continuous φ₂ := by fun_prop
  have p1 : ∀ s, 0 ≤ φ₁ s := fun s => (exp_pos _).le
  have p2 : ∀ t, 0 ≤ φ₂ t := fun t => (exp_pos _).le
  have hw : ∀ x : ℝ × ℝ, exp (-σ * ((x.1 - a) ^ 2 + (x.2 - b) ^ 2)) = φ₁ x.1 * φ₂ x.2 := by
    intro x; simp only [hφ₁, hφ₂, ← Real.exp_add]; ring_nf
  have hg0 : Continuous g := hg.continuous
  set gs : ℝ × ℝ → ℝ := fun x => fderiv ℝ g x (1, 0) with hgs
  set gt : ℝ × ℝ → ℝ := fun x => fderiv ℝ g x (0, 1) with hgt
  have cgs : Continuous gs := (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have cgt : Continuous gt := (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have Z1p : 0 < ∫ s in I, φ₁ s := integral_exp_Icc_pos σ a L hL
  have Z2p : 0 < ∫ t in J, φ₂ t := integral_exp_Icc_pos σ b M hM
  set Z₁ := ∫ s in I, φ₁ s
  set Z₂ := ∫ t in J, φ₂ t
  have iI : ∀ {f : ℝ → ℝ}, Continuous f → Integrable f μ := fun hf =>
    hf.continuousOn.integrableOn_compact isCompact_Icc
  have iJ : ∀ {f : ℝ → ℝ}, Continuous f → Integrable f ν := fun hf =>
    hf.continuousOn.integrableOn_compact isCompact_Icc
  -- means
  set A : ℝ → ℝ := fun t => (∫ s in I, g (s, t) * φ₁ s) / Z₁ with hA
  set E : ℝ → ℝ := fun s => (∫ t in J, g (s, t) * φ₂ t) / Z₂ with hE
  have cA : Continuous A :=
    (cont_param_s (F := fun x => g x * φ₁ x.1) (by fun_prop) I isCompact_Icc).div_const _
  have cE : Continuous E :=
    (cont_param_t (F := fun x => g x * φ₂ x.2) (by fun_prop) J isCompact_Icc).div_const _
  set B : ℝ := (∫ s in I, E s * φ₁ s) / Z₁ with hB
  refine ⟨B, ?_⟩
  rw [restrict_prod]
  simp only [hw]
  -- step 0: pointwise splitting
  have hsplit : ∫ x, (g x - B) ^ 2 * (φ₁ x.1 * φ₂ x.2) ∂(μ.prod ν) ≤
      2 * ∫ x, (g x - A x.2) ^ 2 * (φ₁ x.1 * φ₂ x.2) ∂(μ.prod ν) +
        2 * ∫ x, (A x.2 - B) ^ 2 * (φ₁ x.1 * φ₂ x.2) ∂(μ.prod ν) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((integrable_box (by fun_prop) _ _ _ _).const_mul _)
        ((integrable_box (by fun_prop) _ _ _ _).const_mul _)]
    refine integral_mono (integrable_box (by fun_prop) _ _ _ _)
      (((integrable_box (by fun_prop) _ _ _ _).const_mul _).add
        ((integrable_box (by fun_prop) _ _ _ _).const_mul _)) fun x => ?_
    have hw0 : 0 ≤ φ₁ x.1 * φ₂ x.2 := mul_nonneg (p1 _) (p2 _)
    have : (g x - B) ^ 2 ≤ 2 * (g x - A x.2) ^ 2 + 2 * (A x.2 - B) ^ 2 := by
      nlinarith [sq_nonneg (g x - 2 * A x.2 + B)]
    nlinarith
  -- step 1: the `s`-direction
  have hT1 : ∫ x, (g x - A x.2) ^ 2 * (φ₁ x.1 * φ₂ x.2) ∂(μ.prod ν) ≤
      4 / σ * ∫ x, gs x ^ 2 * (φ₁ x.1 * φ₂ x.2) ∂(μ.prod ν) := by
    rw [iter_t (F := fun x => (g x - A x.2) ^ 2) (by fun_prop) φ₁ φ₂ c1 c2,
      iter_t (F := fun x => gs x ^ 2) (by fun_prop) φ₁ φ₂ c1 c2, ← integral_const_mul]
    refine integral_mono (iJ (c2.mul (cont_param_s (F := fun x => (g x - A x.2) ^ 2 * φ₁ x.1)
        (by fun_prop) I isCompact_Icc)))
      (iJ (continuous_const.mul (c2.mul (cont_param_s (F := fun x => gs x ^ 2 * φ₁ x.1)
        (by fun_prop) I isCompact_Icc)))) fun t => ?_
    have hmin := mean_min (μ := μ) (fun s => g (s, t)) φ₁ (iI (by fun_prop)) (iI (by fun_prop))
      (iI c1) Z1p (g (a, t))
    have h1 := centred_set σ hσ a L hL.le (fun s => g (s, t)) (fun s => gs (s, t))
      (fun s => hasDerivAt_slice_s hg s t) (by fun_prop)
    have : ∫ s in I, (g (s, t) - A t) ^ 2 * φ₁ s ≤ 4 / σ * ∫ s in I, gs (s, t) ^ 2 * φ₁ s :=
      hmin.trans h1
    calc φ₂ t * ∫ s in I, (g (s, t) - A t) ^ 2 * φ₁ s
        ≤ φ₂ t * (4 / σ * ∫ s in I, gs (s, t) ^ 2 * φ₁ s) :=
          mul_le_mul_of_nonneg_left this (p2 t)
      _ = 4 / σ * (φ₂ t * ∫ s in I, gs (s, t) ^ 2 * φ₁ s) := by ring
  -- step 2: the `t`-direction
  have hT2a : ∫ x, (A x.2 - B) ^ 2 * (φ₁ x.1 * φ₂ x.2) ∂(μ.prod ν) ≤
      ∫ x, (g x - E x.1) ^ 2 * (φ₁ x.1 * φ₂ x.2) ∂(μ.prod ν) := by
    rw [iter_t (F := fun x => (A x.2 - B) ^ 2) (by fun_prop) φ₁ φ₂ c1 c2,
      iter_t (F := fun x => (g x - E x.1) ^ 2) (by fun_prop) φ₁ φ₂ c1 c2]
    refine integral_mono (iJ (c2.mul (cont_param_s (F := fun x => (A x.2 - B) ^ 2 * φ₁ x.1)
        (by fun_prop) I isCompact_Icc)))
      (iJ (c2.mul (cont_param_s (F := fun x => (g x - E x.1) ^ 2 * φ₁ x.1)
        (by fun_prop) I isCompact_Icc))) fun t => ?_
    refine mul_le_mul_of_nonneg_left ?_ (p2 t)
    have hj := jensen (μ := μ) (fun s => g (s, t) - E s) φ₁ p1 (iI (by fun_prop))
      (iI (by fun_prop)) (iI c1) Z1p
    have hlin : ∫ s in I, (g (s, t) - E s) * φ₁ s = Z₁ * (A t - B) := by
      have : (fun s => (g (s, t) - E s) * φ₁ s) = fun s => g (s, t) * φ₁ s - E s * φ₁ s := by
        funext s; ring
      rw [this, integral_sub (iI (by fun_prop)) (iI (by fun_prop))]
      simp only [hA, hB]
      rw [mul_sub, mul_div_cancel₀ _ Z1p.ne', mul_div_cancel₀ _ Z1p.ne']
    have hconst : ∫ s in I, (A t - B) ^ 2 * φ₁ s = (A t - B) ^ 2 * Z₁ := by
      rw [integral_const_mul]
    rw [hconst]
    rw [hlin] at hj
    have : Z₁ * ((A t - B) ^ 2 * Z₁) ≤ Z₁ * ∫ s in I, (g (s, t) - E s) ^ 2 * φ₁ s := by
      nlinarith
    exact le_of_mul_le_mul_left this Z1p
  have hT2b : ∫ x, (g x - E x.1) ^ 2 * (φ₁ x.1 * φ₂ x.2) ∂(μ.prod ν) ≤
      4 / σ * ∫ x, gt x ^ 2 * (φ₁ x.1 * φ₂ x.2) ∂(μ.prod ν) := by
    rw [iter_s (F := fun x => (g x - E x.1) ^ 2) (by fun_prop) φ₁ φ₂ c1 c2,
      iter_s (F := fun x => gt x ^ 2) (by fun_prop) φ₁ φ₂ c1 c2, ← integral_const_mul]
    refine integral_mono (iI (c1.mul (cont_param_t (F := fun x => (g x - E x.1) ^ 2 * φ₂ x.2)
        (by fun_prop) J isCompact_Icc)))
      (iI (continuous_const.mul (c1.mul (cont_param_t (F := fun x => gt x ^ 2 * φ₂ x.2)
        (by fun_prop) J isCompact_Icc)))) fun s => ?_
    have hmin := mean_min (μ := ν) (fun t => g (s, t)) φ₂ (iJ (by fun_prop)) (iJ (by fun_prop))
      (iJ c2) Z2p (g (s, b))
    have h1 := centred_set σ hσ b M hM.le (fun t => g (s, t)) (fun t => gt (s, t))
      (fun t => hasDerivAt_slice_t hg s t) (by fun_prop)
    have : ∫ t in J, (g (s, t) - E s) ^ 2 * φ₂ t ≤ 4 / σ * ∫ t in J, gt (s, t) ^ 2 * φ₂ t :=
      hmin.trans h1
    calc φ₁ s * ∫ t in J, (g (s, t) - E s) ^ 2 * φ₂ t
        ≤ φ₁ s * (4 / σ * ∫ t in J, gt (s, t) ^ 2 * φ₂ t) :=
          mul_le_mul_of_nonneg_left this (p1 s)
      _ = 4 / σ * (φ₁ s * ∫ t in J, gt (s, t) ^ 2 * φ₂ t) := by ring
  have hsum : ∫ x, (gs x ^ 2 + gt x ^ 2) * (φ₁ x.1 * φ₂ x.2) ∂(μ.prod ν) =
      ∫ x, gs x ^ 2 * (φ₁ x.1 * φ₂ x.2) ∂(μ.prod ν) +
        ∫ x, gt x ^ 2 * (φ₁ x.1 * φ₂ x.2) ∂(μ.prod ν) := by
    rw [← integral_add (integrable_box (by fun_prop) _ _ _ _)
      (integrable_box (by fun_prop) _ _ _ _)]
    congr 1; funext x; ring
  show ∫ x, (g x - B) ^ 2 * (φ₁ x.1 * φ₂ x.2) ∂(μ.prod ν) ≤
    8 / σ * ∫ x, (gs x ^ 2 + gt x ^ 2) * (φ₁ x.1 * φ₂ x.2) ∂(μ.prod ν)
  rw [hsum]
  calc _ ≤ _ := hsplit
    _ ≤ 2 * (4 / σ * ∫ x, gs x ^ 2 * (φ₁ x.1 * φ₂ x.2) ∂(μ.prod ν)) +
        2 * (4 / σ * ∫ x, gt x ^ 2 * (φ₁ x.1 * φ₂ x.2) ∂(μ.prod ν)) := by
      have := hT2a.trans hT2b
      gcongr
    _ = _ := by ring

end GPoin

namespace CauchyRiemannIndex

open MeasureTheory Set Real

theorem gaussian_poincare_rectangle_aux (σ : ℝ) (hσ : 0 < σ) (a b L M : ℝ) (hL : 0 < L)
    (hM : 0 < M) (g : ℝ × ℝ → ℝ) (hg : ContDiff ℝ 1 g) :
    ∃ c : ℝ, ∫ x in Icc (a - L) (a + L) ×ˢ Icc (b - M) (b + M),
        (g x - c) ^ 2 * exp (-σ * ((x.1 - a) ^ 2 + (x.2 - b) ^ 2)) ≤
      8 / σ * ∫ x in Icc (a - L) (a + L) ×ˢ Icc (b - M) (b + M),
        ((fderiv ℝ g x (1, 0)) ^ 2 + (fderiv ℝ g x (0, 1)) ^ 2) *
          exp (-σ * ((x.1 - a) ^ 2 + (x.2 - b) ^ 2)) :=
  GPoin.rect σ hσ a b L M hL hM g hg

end CauchyRiemannIndex

open CauchyRiemannIndex

open MeasureTheory Set Real

theorem solution (σ : ℝ) (hσ : 0 < σ) (a b L M : ℝ) (hL : 0 < L) (hM : 0 < M)
    (g : ℝ × ℝ → ℝ) (hg : ContDiff ℝ 1 g) :
    ∃ c : ℝ, ∫ x in Icc (a - L) (a + L) ×ˢ Icc (b - M) (b + M),
        (g x - c) ^ 2 * exp (-σ * ((x.1 - a) ^ 2 + (x.2 - b) ^ 2)) ≤
      8 / σ * ∫ x in Icc (a - L) (a + L) ×ˢ Icc (b - M) (b + M),
        ((fderiv ℝ g x (1, 0)) ^ 2 + (fderiv ℝ g x (0, 1)) ^ 2) *
          exp (-σ * ((x.1 - a) ^ 2 + (x.2 - b) ^ 2)) :=
  gaussian_poincare_rectangle_aux σ hσ a b L M hL hM g hg
