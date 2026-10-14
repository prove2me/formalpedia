-- Prove2me | solution 1 for DbarRegularity.integral_dbar_mul_inv_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T20:41:42.659351+00:00
-- url     : https://prove2.me/submissions/8905925d-518c-451f-840c-c64d3354f85d

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Theorems.Thm_DbarRegularity_integral_fderiv_annulus_complex



namespace DbarRegularity

open MeasureTheory Metric Set

/-- For `f ∈ C¹_c(ℝ²)`, `x ∈ ℝ²` and `ε > 0`, the integral of
`(∂₁f + i ∂₂f)(x - y) / (y₀ + i y₁)²` over `|y| ≥ ε` equals
`ε⁻¹ ∫_{S¹} f(x - ε ω) / (ω₀ + i ω₁) dσ(ω)`. -/
theorem integral_dbar_mul_inv_sq_eq_aux (f : EuclideanSpace ℝ (Fin 2) → ℂ) (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (x : EuclideanSpace ℝ (Fin 2)) (ε : ℝ) (hε : 0 < ε) :
    ∫ y in {y : EuclideanSpace ℝ (Fin 2) | ε ≤ ‖y‖},
        (fderiv ℝ f (x - y) (EuclideanSpace.single 0 1) +
          Complex.I * fderiv ℝ f (x - y) (EuclideanSpace.single 1 1)) *
        (1 / ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) ^ 2) =
      ((ε⁻¹ : ℝ) : ℂ) * ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
        f (x - ε • ω.1) / ((ω.1 0 : ℂ) + (ω.1 1 : ℂ) * Complex.I) ∂volume.toSphere := by
  set e := Complex.orthonormalBasisOneI.repr.symm with he_def
  have he : ∀ y, e y = (y 0 : ℂ) + (y 1 : ℂ) * Complex.I := fun y =>
    Complex.orthonormalBasisOneI_repr_symm_apply y
  have hne : ∀ y : EuclideanSpace ℝ (Fin 2), y ≠ 0 → e y ≠ 0 := fun y hy h =>
    hy (e.map_eq_zero_iff.1 h)
  set eL := e.toLinearIsometry.toContinuousLinearMap with heL
  set K : EuclideanSpace ℝ (Fin 2) → ℂ := fun y => (e y) ^ (-2 : ℤ) with hKdef
  have hK : ∀ y : EuclideanSpace ℝ (Fin 2),
      1 / ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) ^ 2 = K y := by
    intro y
    rw [hKdef]
    simp only
    rw [← he, zpow_neg, one_div]
    norm_cast
  have hK' : K = fun z => ((e z) ^ 2)⁻¹ := by
    funext z
    rw [hKdef]
    simp only
    rw [zpow_neg]
    norm_cast
  have hKder : ∀ y, y ≠ 0 →
      HasFDerivAt K (((-2 : ℤ) * (e y) ^ ((-2 : ℤ) - 1)) • eL) y := by
    intro y hy
    exact (hasDerivAt_zpow (-2) (e y) (Or.inl (hne y hy))).comp_hasFDerivAt y eL.hasFDerivAt
  set Fd : EuclideanSpace ℝ (Fin 2) → ℂ := fun z =>
    fderiv ℝ f z (EuclideanSpace.single 0 1) +
      Complex.I * fderiv ℝ f z (EuclideanSpace.single 1 1) with hFd
  set h : EuclideanSpace ℝ (Fin 2) → ℂ := fun y => f (x - y) * K y with hh
  have hfx : ∀ y, HasFDerivAt (fun y => f (x - y))
      ((fderiv ℝ f (x - y)).comp (-ContinuousLinearMap.id ℝ _)) y := by
    intro y
    have h1 := (hf.differentiable (by norm_num) (x - y)).hasFDerivAt
    have h2 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) => x - y)
        (-ContinuousLinearMap.id ℝ _) y := (hasFDerivAt_id y).const_sub x
    exact h1.comp y h2
  have hhder : ∀ y, y ≠ 0 → HasFDerivAt h
      (f (x - y) • (((-2 : ℤ) * (e y) ^ ((-2 : ℤ) - 1)) • eL) +
        K y • ((fderiv ℝ f (x - y)).comp (-ContinuousLinearMap.id ℝ _))) y :=
    fun y hy => (hfx y).mul (hKder y hy)
  have he0 : eL (EuclideanSpace.single 0 1) = 1 := by
    change e _ = _
    rw [he]
    simp
  have he1 : eL (EuclideanSpace.single 1 1) = Complex.I := by
    change e _ = _
    rw [he]
    simp
  have hdbar : ∀ y, y ≠ 0 →
      fderiv ℝ h y (EuclideanSpace.single 0 1) +
        Complex.I * fderiv ℝ h y (EuclideanSpace.single 1 1) = -(Fd (x - y) * K y) := by
    intro y hy
    rw [(hhder y hy).fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.id_apply, map_neg, smul_eq_mul, he0, he1, hFd]
    linear_combination (f (x - y) * (((-2 : ℤ) : ℂ) * (e y) ^ ((-2 : ℤ) - 1))) * Complex.I_sq
  have hhcd : ∀ y, y ≠ 0 → ContDiffAt ℝ 1 h y := by
    intro y hy
    have h1 : ContDiffAt ℝ 1 (fun y => f (x - y)) y :=
      hf.contDiffAt.comp y (contDiffAt_const.sub contDiffAt_id)
    have h2 : ContDiffAt ℝ 1 K y := by
      rw [hK']
      exact (e.contDiff.contDiffAt.pow 2).inv (pow_ne_zero 2 (hne y hy))
    exact h1.mul h2
  -- a radius beyond the support
  obtain ⟨R₀, hR₀⟩ : ∃ R₀, tsupport f ⊆ closedBall x R₀ :=
    hfc.isCompact.isBounded.subset_closedBall x
  set R := max R₀ ε + 1 with hR
  have hεR : ε < R := by linarith [le_max_right R₀ ε]
  have hzero : ∀ y : EuclideanSpace ℝ (Fin 2), R ≤ ‖y‖ →
      f (x - y) = 0 ∧ fderiv ℝ f (x - y) = 0 := by
    intro y hy
    have hn : x - y ∉ tsupport f := by
      intro hm
      have := hR₀ hm
      rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg] at this
      linarith [le_max_left R₀ ε]
    exact ⟨image_eq_zero_of_notMem_tsupport hn,
      image_eq_zero_of_notMem_tsupport (fun h' => hn (tsupport_fderiv_subset ℝ h'))⟩
  set A := ball (0 : EuclideanSpace ℝ (Fin 2)) R \ closedBall 0 ε with hAdef
  have hmeasA : MeasurableSet A := measurableSet_ball.diff measurableSet_closedBall
  have hA0 : ∀ y ∈ A, y ≠ 0 := by
    intro y hy h0
    rw [h0] at hy
    exact hy.2 (mem_closedBall_self hε.le)
  -- step 1: restrict to the annulus
  have h1 : ∫ y in {y : EuclideanSpace ℝ (Fin 2) | ε ≤ ‖y‖},
        Fd (x - y) * (1 / ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) ^ 2) =
      ∫ y in A, Fd (x - y) * K y := by
    simp_rw [hK]
    have hnull : volume (sphere (0 : EuclideanSpace ℝ (Fin 2)) ε) = 0 :=
      Measure.addHaar_sphere volume 0 ε
    have hae : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))),
        y ∉ sphere (0 : EuclideanSpace ℝ (Fin 2)) ε := by
      rw [ae_iff]
      simp only [not_not, setOf_mem_eq]
      exact hnull
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
      (measurableSet_le measurable_const measurable_norm).nullMeasurableSet ?_ ?_
    · intro y hy
      simp only [hAdef, mem_diff, mem_ball, mem_closedBall, dist_zero_right, not_le] at hy
      exact hy.2.le
    · filter_upwards [hae] with y hy hyd
      simp only [hAdef, mem_diff, mem_ball, mem_closedBall, dist_zero_right, not_le,
        mem_setOf_eq, not_and, mem_sphere_iff_norm, sub_zero] at hyd hy
      have hεy : ε < ‖y‖ := lt_of_le_of_ne hyd.1 (Ne.symm hy)
      have hRy : R ≤ ‖y‖ := by
        by_contra hc
        push_neg at hc
        have := hyd.2 hc
        linarith
      simp [hFd, (hzero y hRy).2]
  -- step 2: the integrand on the annulus
  have hint : ∀ v, IntegrableOn (fun y => fderiv ℝ h y v) A := by
    intro v
    have hKc : IsCompact (closedBall (0 : EuclideanSpace ℝ (Fin 2)) R \ ball 0 ε) :=
      (isCompact_closedBall _ R).diff isOpen_ball
    have hc : ContinuousOn (fun y => fderiv ℝ h y v)
        (closedBall (0 : EuclideanSpace ℝ (Fin 2)) R \ ball 0 ε) := by
      intro y hy
      have hy0 : y ≠ 0 := by
        rintro rfl
        exact hy.2 (mem_ball_self hε)
      have h1 := (hhcd y hy0).fderiv_right (m := 0) (by norm_num)
      exact (h1.continuousAt.clm_apply continuousAt_const).continuousWithinAt
    refine (hc.integrableOn_compact hKc).mono_set ?_
    intro y hy
    exact ⟨ball_subset_closedBall hy.1, fun h' => hy.2 (ball_subset_closedBall h')⟩
  have h2 : ∫ y in A, Fd (x - y) * K y =
      -((∫ y in A, fderiv ℝ h y (EuclideanSpace.single 0 1)) +
        Complex.I * ∫ y in A, fderiv ℝ h y (EuclideanSpace.single 1 1)) := by
    rw [setIntegral_congr_fun hmeasA (fun y hy => by
      rw [← neg_neg (Fd (x - y) * K y), ← hdbar y (hA0 y hy)])]
    rw [integral_neg, integral_add (hint _) ((hint _).const_mul _), integral_const_mul]
  -- step 3: the boundary formula
  have hcd : ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) R, y ≠ 0 → ContDiffAt ℝ 1 h y :=
    fun y _ hy => hhcd y hy
  have hb := fun v => integral_fderiv_annulus_complex (n := 2) (by norm_num) hε hεR hcd v
  have hRz : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, h (0 + R • ω.1) = 0 := by
    intro ω
    have hω : ‖ω.1‖ = 1 := by simpa using ω.2
    have : R ≤ ‖0 + R • ω.1‖ := by
      rw [zero_add, norm_smul, hω, mul_one, Real.norm_of_nonneg (by linarith)]
    simp only [hh, (hzero _ this).1, zero_mul]
  simp only [hRz, zero_mul, integral_zero, mul_zero, zero_sub] at hb
  -- integrability on the sphere
  have hsint : ∀ i : Fin 2, Integrable (fun ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 =>
      h (0 + ε • ω.1) * ((inner ℝ (EuclideanSpace.single i (1 : ℝ)) ω.1 : ℝ) : ℂ))
      volume.toSphere := by
    intro i
    have hc : Continuous (fun ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 =>
        h (0 + ε • ω.1) * ((inner ℝ (EuclideanSpace.single i (1 : ℝ)) ω.1 : ℝ) : ℂ)) := by
      refine Continuous.mul ?_ ?_
      · refine continuous_iff_continuousAt.2 fun ω => ?_
        have hω : ‖ω.1‖ = 1 := by simpa using ω.2
        have hne' : 0 + ε • ω.1 ≠ 0 := by
          intro h0
          have := congrArg norm h0
          rw [zero_add, norm_smul, hω, mul_one, Real.norm_of_nonneg hε.le, norm_zero] at this
          exact hε.ne' this
        have hg : Continuous (fun ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 =>
            (0 : EuclideanSpace ℝ (Fin 2)) + ε • ω.1) := by fun_prop
        exact ContinuousAt.comp (g := h) (hhcd _ hne').continuousAt hg.continuousAt
      · exact Complex.continuous_ofReal.comp (continuous_const.inner continuous_subtype_val)
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have key : ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
        f (x - ε • ω.1) / ((ω.1 0 : ℂ) + (ω.1 1 : ℂ) * Complex.I) ∂volume.toSphere =
      (ε : ℂ) ^ 2 * ((∫ ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
          h (0 + ε • ω.1) * ((inner ℝ (EuclideanSpace.single 0 (1 : ℝ)) ω.1 : ℝ) : ℂ)
            ∂volume.toSphere) +
        Complex.I * ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
          h (0 + ε • ω.1) * ((inner ℝ (EuclideanSpace.single 1 (1 : ℝ)) ω.1 : ℝ) : ℂ)
            ∂volume.toSphere) := by
    rw [← integral_const_mul Complex.I, ← integral_add (hsint 0) ((hsint 1).const_mul _),
      ← integral_const_mul]
    congr 1
    funext ω
    have hω : ‖ω.1‖ = 1 := by simpa using ω.2
    have hω0 : ω.1 ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hω; exact zero_ne_one hω
    have heω' : ((ω.1 0 : ℂ) + (ω.1 1 : ℂ) * Complex.I) ≠ 0 := by
      rw [← he]; exact hne _ hω0
    have hεc : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hε.ne'
    have hs : e (ε • ω.1) = (ε : ℂ) * ((ω.1 0 : ℂ) + (ω.1 1 : ℂ) * Complex.I) := by
      rw [map_smul, he, Complex.real_smul]
    simp only [hh, hKdef, zero_add, EuclideanSpace.inner_single_left, map_one, one_mul]
    rw [hs, mul_zpow, zpow_neg, zpow_neg, zpow_ofNat, zpow_ofNat]
    field_simp
  rw [h1, h2, hb, hb, key]
  have hεc : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hε.ne'
  push_cast
  field_simp
  ring

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric Set

theorem solution (f : EuclideanSpace ℝ (Fin 2) → ℂ) (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (x : EuclideanSpace ℝ (Fin 2)) (ε : ℝ) (hε : 0 < ε) :
    ∫ y in {y : EuclideanSpace ℝ (Fin 2) | ε ≤ ‖y‖},
        (fderiv ℝ f (x - y) (EuclideanSpace.single 0 1) +
          Complex.I * fderiv ℝ f (x - y) (EuclideanSpace.single 1 1)) *
        (1 / ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) ^ 2) =
      ((ε⁻¹ : ℝ) : ℂ) * ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
        f (x - ε • ω.1) / ((ω.1 0 : ℂ) + (ω.1 1 : ℂ) * Complex.I) ∂volume.toSphere :=
  integral_dbar_mul_inv_sq_eq_aux f hf hfc x ε hε
