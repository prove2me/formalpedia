-- Prove2me | solution 1 for FriedmannEquations.fluidEq_of_friedmann
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:43:35.848992+00:00
-- url     : https://prove2.me/submissions/996cfc7e-aa8a-4fb2-b19c-3b218cc0c3fd

import Definitions.Def_FriedmannEquations_Defs
set_option autoImplicit false
open FriedmannEquations Filter Topology

private noncomputable def curvatureFunction (G Λ : ℝ) (R ρ : ℝ → ℝ) (t : ℝ) : ℝ :=
  (8 * Real.pi * G * ρ t + Λ) / 3 * R t ^ 2 - deriv R t ^ 2

private theorem curvature_hasDerivAt (G Λ : ℝ) (R ρ : ℝ → ℝ) (t : ℝ)
    (hR : DifferentiableAt ℝ R t) (hD : DifferentiableAt ℝ (deriv R) t)
    (hρ : DifferentiableAt ℝ ρ t) :
    HasDerivAt (curvatureFunction G Λ R ρ)
      ((8 * Real.pi * G * deriv ρ t) / 3 * R t ^ 2 +
        (8 * Real.pi * G * ρ t + Λ) / 3 * (2 * R t * deriv R t) -
        2 * deriv R t * deriv (deriv R) t) t := by
  exact (((hρ.hasDerivAt.const_mul (8*Real.pi*G)).add_const Λ).div_const 3 |>.mul
    (hR.hasDerivAt.pow 2)).sub (hD.hasDerivAt.pow 2) |>.congr_deriv (by simp only [Pi.pow_apply]; ring)

theorem curvature_exists (G Λ : ℝ) (R ρ p : ℝ → ℝ) (I : Set ℝ)
    (hI_open : IsOpen I) (hI_conn : IsPreconnected I)
    (hR_pos : ∀ t ∈ I, 0 < R t) (hR : ContDiffOn ℝ 2 R I) (hρ : DifferentiableOn ℝ ρ I)
    (hfluid : ∀ t ∈ I, FluidEq R ρ p t)
    (h₂ : ∀ t ∈ I, SecondFriedmannEq G Λ R ρ p t) :
    ∃ k : ℝ, ∀ t ∈ I, FirstFriedmannEq G Λ k R ρ t := by
  have hzero (t : ℝ) (ht : t ∈ I) : HasDerivAt (curvatureFunction G Λ R ρ) 0 t := by
    have hRct := hR.contDiffAt (hI_open.mem_nhds ht)
    have hdR := hRct.differentiableAt (by norm_num)
    have hdD : DifferentiableAt ℝ (deriv R) t :=
      (hRct.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hdρ := (hρ t ht).differentiableAt (hI_open.mem_nhds ht)
    have hd := curvature_hasDerivAt G Λ R ρ t hdR hdD hdρ
    have hf := hfluid t ht
    unfold FluidEq hubble at hf
    have hs := h₂ t ht
    unfold SecondFriedmannEq at hs
    have hdd := (div_eq_iff (hR_pos t ht).ne').mp hs
    convert! hd using 1
    rw [hf, hdd]
    field_simp [(hR_pos t ht).ne']
    <;> ring
  obtain ⟨k, hk⟩ := hI_open.exists_is_const_of_deriv_eq_zero hI_conn
    (fun t ht => (hzero t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hzero t ht).deriv)
  refine ⟨k, ?_⟩
  intro t ht
  unfold FirstFriedmannEq hubble
  rw [← hk t ht]
  unfold curvatureFunction
  field_simp [(hR_pos t ht).ne']
  <;> ring

theorem solution (G Λ k : ℝ) (hG : 0 < G) (R ρ p : ℝ → ℝ)
    (I : Set ℝ) (hI_open : IsOpen I)
    (hR_pos : ∀ t ∈ I, 0 < R t) (hR : ContDiffOn ℝ 2 R I) (hρ : DifferentiableOn ℝ ρ I)
    (h₁ : ∀ t ∈ I, FirstFriedmannEq G Λ k R ρ t)
    (h₂ : ∀ t ∈ I, SecondFriedmannEq G Λ R ρ p t) :
    ∀ t ∈ I, FluidEq R ρ p t := by
  have hk (s : ℝ) (hs : s ∈ I) : curvatureFunction G Λ R ρ s = k := by
    have hf := h₁ s hs
    unfold FirstFriedmannEq hubble at hf
    unfold curvatureFunction
    field_simp [(hR_pos s hs).ne'] at hf ⊢
    nlinarith
  intro t ht
  have hRct := hR.contDiffAt (hI_open.mem_nhds ht)
  have hdR := hRct.differentiableAt (by norm_num)
  have hdD : DifferentiableAt ℝ (deriv R) t :=
    (hRct.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdρ := (hρ t ht).differentiableAt (hI_open.mem_nhds ht)
  have hd := curvature_hasDerivAt G Λ R ρ t hdR hdD hdρ
  have hevent : curvatureFunction G Λ R ρ =ᶠ[𝓝 t] fun _ => k := by
    filter_upwards [hI_open.mem_nhds ht] with s hs
    exact hk s hs
  have hz := hd.unique ((hasDerivAt_const t k).congr_of_eventuallyEq hevent)
  have hs := h₂ t ht
  unfold SecondFriedmannEq at hs
  have hdd := (div_eq_iff (hR_pos t ht).ne').mp hs
  rw [hdd] at hz
  have heq : (8 * Real.pi * G * R t ^ 2 / 3) *
      (deriv ρ t + 3 * (deriv R t / R t) * (ρ t + p t)) = 0 := by
    convert hz using 1
    field_simp [(hR_pos t ht).ne']
    <;> ring
  have hRt := hR_pos t ht
  have hcoeff : 8 * Real.pi * G * R t ^ 2 / 3 ≠ 0 := by positivity
  have hsum := (mul_eq_zero.mp heq).resolve_left hcoeff
  unfold FluidEq hubble
  nlinarith

