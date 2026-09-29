-- Prove2me | solution 1 for FourExp.expPoly_zero_count_scaled
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-15T04:08:55.667594+00:00
-- url     : https://prove2.me/submissions/f34d8db7-d0c0-4900-ac61-dbfde6476938

import Mathlib
import Theorems.Thm_FourExp_cauchy_estimate_with_zeros
import Theorems.Thm_FourExp_expPoly_value_le_derivs
import Theorems.Thm_FourExp_expPoly_ne_zero

open Finset Polynomial

theorem solution
    {l : ℕ} (q : Fin l → ℕ) (ω : Fin l → ℂ) (hω : Function.Injective ω)
    (b : (j : Fin l) → Fin (q j) → ℂ) (hb : ∃ j i, b j i ≠ 0)
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ) (S : Finset ℂ) (hS : ∀ z ∈ S, ‖z - z₀‖ ≤ ρ)
    (hΩ : 0 < ⨆ j, ‖ω j‖) :
    ∀ R : ℝ, ρ * (⨆ j, ‖ω j‖) + 1 < R →
      (∑ z ∈ S, (analyticOrderNatAt (fun w : ℂ => ∑ j, ∑ i : Fin (q j), b j i * w ^ (i : ℕ) * Complex.exp (ω j * w)) z : ℝ))
          * Real.log ((R - ρ * (⨆ j, ‖ω j‖)) / (ρ * (⨆ j, ‖ω j‖) + 1))
        ≤ Real.log (((∑ j, q j).factorial : ℝ) * 2 ^ ((∑ j, q j) + 1) * R / (R - 1)) + 2 * R := by
  classical
  intro R hR
  set Ω : ℝ := ⨆ j, ‖ω j‖ with hΩdef
  set n : ℕ := ∑ j, q j with hndef
  set f : ℂ → ℂ := fun w : ℂ => ∑ j, ∑ i : Fin (q j), b j i * w ^ (i : ℕ) * Complex.exp (ω j * w)
    with hfdef
  set x : ℝ := ρ * Ω with hxdef
  have hx0 : 0 ≤ x := mul_nonneg hρ hΩ.le
  have hR1 : 1 < R := by linarith
  have hR0 : 0 < R := by linarith
  have hRx : x < R := by linarith
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ.ne'
  obtain ⟨j₀, i₀, hb₀⟩ := hb
  have hn1 : 1 ≤ n := by
    have h1 : 1 ≤ q j₀ := by have := i₀.isLt; omega
    exact h1.trans (Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ j₀))
  -- `f` is entire
  have hfdiff : Differentiable ℂ f := by rw [hfdef]; fun_prop
  -- the rescaled function `G y = f (z₀ + y / Ω)`, written as an exponential polynomial
  let w : Fin l → ℂ := fun j => ω j / Ω
  let P : Fin l → ℂ[X] := fun j =>
    ∑ i : Fin (q j), C (b j i * Complex.exp (ω j * z₀)) * (C z₀ + C ((Ω : ℂ)⁻¹) * X) ^ (i : ℕ)
  let G : ℂ → ℂ := fun y => ∑ j, (P j).eval y * Complex.exp (w j * y)
  have hG : ∀ y, G y = f (z₀ + y / Ω) := by
    intro y
    simp only [G, P, w, hfdef, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_add, eval_X,
      Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
    rw [show ω j * (z₀ + y / Ω) = ω j * z₀ + ω j / Ω * y by ring, Complex.exp_add]
    ring
  have hGdiff : Differentiable ℂ G := by
    have : G = fun y => f (z₀ + y / Ω) := funext hG
    rw [this]
    exact hfdiff.comp ((differentiable_id.div_const _).const_add z₀)
  -- hypotheses of the lower bound
  have hw : Function.Injective w := fun a c h => hω ((div_left_inj' hΩc).mp h)
  have hwle : ∀ j, ‖w j‖ ≤ 1 := by
    intro j
    have hj : ‖ω j‖ ≤ Ω := le_ciSup (f := fun j => ‖ω j‖) (Finite.bddAbove_range _) j
    simp only [w, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hΩ]
    exact (div_le_one hΩ).mpr hj
  have hP : ∀ j, P j = 0 ∨ (P j).natDegree < q j := by
    intro j
    by_cases hq : q j = 0
    · left
      exact Finset.sum_eq_zero (fun i _ => by have hi : (i : ℕ) < q j := i.isLt; omega)
    · right
      have hlin : (C z₀ + C ((Ω : ℂ)⁻¹) * X).natDegree ≤ 1 :=
        (natDegree_add_le _ _).trans (max_le (by simp) ((natDegree_C_mul_le _ _).trans (by simp)))
      have : (P j).natDegree ≤ q j - 1 := by
        apply natDegree_sum_le_of_forall_le
        intro i _
        refine (natDegree_C_mul_le _ _).trans ((natDegree_pow_le).trans ?_)
        have hi : (i : ℕ) < q j := i.isLt
        calc (i : ℕ) * (C z₀ + C ((Ω : ℂ)⁻¹) * X).natDegree ≤ (i : ℕ) * 1 :=
              Nat.mul_le_mul_left _ hlin
          _ ≤ q j - 1 := by omega
      omega
  -- orders transfer along `y ↦ z₀ + y / Ω`
  have hφd : ∀ y : ℂ, HasDerivAt (fun y : ℂ => z₀ + y / Ω) ((Ω : ℂ)⁻¹) y := by
    intro y
    simpa [div_eq_mul_inv] using ((hasDerivAt_id y).mul_const ((Ω : ℂ)⁻¹)).const_add z₀
  have hord : ∀ z, analyticOrderNatAt G ((Ω : ℂ) * (z - z₀)) = analyticOrderNatAt f z := by
    intro z
    have hcomp : G = f ∘ fun y : ℂ => z₀ + y / Ω := funext hG
    have han : AnalyticAt ℂ (fun y : ℂ => z₀ + y / Ω) ((Ω : ℂ) * (z - z₀)) :=
      ((differentiable_id.div_const _).const_add z₀).analyticAt _
    have := analyticOrderAt_comp_of_deriv_ne_zero (f := f) han
      (by rw [(hφd _).deriv]; exact inv_ne_zero hΩc)
    unfold analyticOrderNatAt
    rw [hcomp, this]
    congr 2
    field_simp
    ring
  let S' : Finset ℂ := S.image (fun z => (Ω : ℂ) * (z - z₀))
  have hinj : Set.InjOn (fun z => (Ω : ℂ) * (z - z₀)) ↑S := by
    intro a _ c _ h
    have := mul_left_cancel₀ hΩc h
    linear_combination this
  have hsum : ∑ z ∈ S', analyticOrderNatAt G z = ∑ z ∈ S, analyticOrderNatAt f z := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl (fun z _ => hord z)
  have hS' : ∀ z ∈ S', ‖z - 0‖ ≤ x := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    rw [sub_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hΩ, hxdef, mul_comm ρ]
    exact mul_le_mul_of_nonneg_left (hS y hy) hΩ.le
  -- the maximum of `|G|` on the circle of radius `R`
  obtain ⟨u₀, hu₀, hmax⟩ := (isCompact_sphere (0 : ℂ) R).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr hR0.le) hGdiff.continuous.norm.continuousOn
  set M : ℝ := ‖G u₀‖ with hMdef
  have hM : ∀ z : ℂ, ‖z - 0‖ = R → ‖G z‖ ≤ M := by
    intro z hz
    exact hmax (by simpa [mem_sphere_iff_norm] using hz)
  have hMpos : 0 < M := by
    by_contra hle
    push_neg at hle
    have hball : ∀ z ∈ Metric.ball (0 : ℂ) R, G z = 0 := by
      intro z hz
      have := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
        hGdiff.diffContOnCl (C := M)
        (fun y hy => hM y (by rw [frontier_ball _ hR0.ne'] at hy; simpa [mem_sphere_iff_norm] using hy))
        (subset_closure hz)
      exact norm_le_zero_iff.mp (this.trans hle)
    have hev : G =ᶠ[nhds 0] 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hR0] with z hz
      simpa using hball z hz
    have hzero := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (fun u _ => hGdiff.analyticAt u) isPreconnected_univ (Set.mem_univ 0) hev
    obtain ⟨v, hv⟩ := FourExp.expPoly_ne_zero q ω hω b ⟨j₀, i₀, hb₀⟩
    apply hv
    have h1 := hzero (Set.mem_univ ((Ω : ℂ) * (v - z₀)))
    rw [Pi.zero_apply, hG] at h1
    have : z₀ + (Ω : ℂ) * (v - z₀) / Ω = v := by field_simp; ring
    rw [this] at h1
    exact h1
  -- Cauchy with zeros, for each derivative of order below `n`
  set σ : ℕ := ∑ z ∈ S', analyticOrderNatAt G z with hσdef
  set r : ℝ := (x + 1) / (R - x) with hrdef
  have hrpos : 0 < r := div_pos (by linarith) (by linarith)
  have hRR : 0 < R / (R - 1) := div_pos hR0 (by linarith)
  set D : ℝ := ((n - 1).factorial : ℝ) * (R / (R - 1)) * r ^ σ * M with hDdef
  have hD : ∀ s : ℕ, s < n → ‖iteratedDeriv s G 0‖ ≤ D := by
    intro s hs
    have h1 := FourExp.cauchy_estimate_with_zeros G hGdiff 0 x R M hx0 (by linarith) S' hS' hM s
    have hfac : (s.factorial : ℝ) ≤ ((n - 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    calc ‖iteratedDeriv s G 0‖ ≤ (s.factorial : ℝ) * (R / (R - 1)) * r ^ σ * M := h1
      _ ≤ D := by
        rw [hDdef]
        gcongr
  -- the interpolation lower bound at the maximum point
  have h2 := FourExp.expPoly_value_le_derivs q w hw P hP 1 R D zero_le_one hwle hR0.le hD u₀
    (by simpa [mem_sphere_iff_norm] using hu₀.le)
  have h2' : M ≤ ((n.factorial : ℝ) * 2 ^ (n + 1) * (R / (R - 1)) * Real.exp (2 * R)) * r ^ σ * M := by
    have hnf : (n : ℝ) * ((n - 1).factorial : ℝ) = (n.factorial : ℝ) := by
      have : n * (n - 1).factorial = n.factorial := Nat.mul_factorial_pred (by omega)
      exact_mod_cast this
    calc M = ‖∑ j, (P j).eval u₀ * Complex.exp (w j * u₀)‖ := rfl
      _ ≤ ((∑ j, q j : ℕ) : ℝ) * (1 + 1) ^ ((∑ j, q j) + 1) * Real.exp (R * (1 + 1)) * D := h2
      _ = ((n : ℝ) * ((n - 1).factorial : ℝ)) * 2 ^ (n + 1) * (R / (R - 1)) * Real.exp (2 * R)
            * r ^ σ * M := by
          rw [hDdef, hndef]; ring_nf
      _ = _ := by rw [hnf]
  have hK : 1 ≤ ((n.factorial : ℝ) * 2 ^ (n + 1) * (R / (R - 1)) * Real.exp (2 * R)) * r ^ σ := by
    by_contra hlt
    push_neg at hlt
    have := mul_lt_mul_of_pos_right hlt hMpos
    linarith
  -- take logarithms
  have hfpos : (0 : ℝ) < (n.factorial : ℝ) * 2 ^ (n + 1) * R / (R - 1) := by
    have : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have : (0 : ℝ) < R - 1 := by linarith
    positivity
  have hlog := Real.log_le_log one_pos hK
  rw [Real.log_one, Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at hlog
  have hlr : Real.log r = - Real.log ((R - x) / (x + 1)) := by
    rw [hrdef, ← Real.log_inv, inv_div]
  have hsigma : (∑ z ∈ S, (analyticOrderNatAt f z : ℝ)) = (σ : ℝ) := by
    rw [hsum]; push_cast; rfl
  rw [hsigma]
  have hKeq : (n.factorial : ℝ) * 2 ^ (n + 1) * (R / (R - 1)) = (n.factorial : ℝ) * 2 ^ (n + 1) * R / (R - 1) := by
    ring
  rw [hKeq] at hlog
  rw [hlr] at hlog
  linarith
