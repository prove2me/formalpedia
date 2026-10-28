-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integral_mul_hessian_increment_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:03:09.269085+00:00
-- url     : https://prove2.me/submissions/e1701a7c-0490-4114-9f4d-e61432c52b2e

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_HessianIncrement
import Theorems.Thm_FunctionalInequalities_Analysis_ae_hessian_increment_le_generator_readable
import Theorems.Thm_FunctionalInequalities_Analysis_centeredDifference_contDiff_lipschitz_gradient_readable
import Theorems.Thm_FunctionalInequalities_Analysis_centeredDifference_nonneg_le_readable
import Theorems.Thm_FunctionalInequalities_Analysis_integrable_hessian_increment_energy_readable
import Theorems.Thm_FunctionalInequalities_Analysis_integrable_weak_generator_densities_readable
import Theorems.Thm_FunctionalInequalities_Analysis_integral_mul_generator_eq_neg_energy_readable
import Theorems.Thm_FunctionalInequalities_Analysis_integral_mul_generator_eq_neg_energy_prime_readable

noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Probability.Stein
/-- **Integrated energy of Hessian increments** (weak Letwin route; KLS500
`weak_moment_compact_hessian_increment_energy_bound`): for the `C^{1,1}` Monge–Ampère solution `u` with
`0 ≤ Δ²ₕu ≤ D‖h‖²`, every nonnegative `η ∈ C²_c` satisfies
`∫ η (‖H(x+h) − H(x)‖²_F + ‖H(x−h) − H(x)‖²_F) e^{−u} ≤ 2K² D ‖h‖² ∫ |η + Lη| e^{−u}`,
`Lη := tr(H⁻¹∇²η) − DV(∇u)(∇η)`. -/
theorem solution {n : ℕ} {u V η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (hconv : ConvexOn ℝ univ u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x))) {K : ℝ} (hK : 0 < K)
    (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosDef ∧
      Real.log (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = -u x + V (gradient u x) ∧
      (K • (1 : Matrix (Fin n) (Fin n) ℝ) - FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosSemidef)
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) (hη0 : ∀ x, 0 ≤ η x) {D : ℝ}
    (h : EuclideanSpace ℝ (Fin n)) (hw : ∀ x, u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2) :
    ∫ x, η x * ((∑ i, ∑ j, (FunctionalInequalities.Probability.Stein.hessianMatrix u (x + h) - FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j ^ 2) +
        ∑ i, ∑ j, (FunctionalInequalities.Probability.Stein.hessianMatrix u (x - h) - FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j ^ 2) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) ≤
      2 * K ^ 2 * (D * ‖h‖ ^ 2) *
        ∫ x, |η x + (((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix η x).trace -
          fderiv ℝ V (gradient u x) (gradient η x))| * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  let w : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => u (x + h) + u (x - h) - 2 * u x
  let C : ℝ := D * ‖h‖ ^ 2
  let q : ℝ := 2 * K ^ 2
  let ρ : EuclideanSpace ℝ (Fin n) → ℝ := fun x => Real.exp (-u x)
  let L : (EuclideanSpace ℝ (Fin n) → ℝ) → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun f x => ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix f x).trace -
      fderiv ℝ V (gradient u x) (gradient f x)
  let E : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    (∑ i, ∑ j, (FunctionalInequalities.Probability.Stein.hessianMatrix u (x + h) - FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j ^ 2) +
      ∑ i, ∑ j, (FunctionalInequalities.Probability.Stein.hessianMatrix u (x - h) - FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j ^ 2
  let e : EuclideanSpace ℝ (Fin n) → ℝ := fun x => η x * E x * ρ x
  let p : EuclideanSpace ℝ (Fin n) → ℝ := fun x => η x * L w x * ρ x
  let t : EuclideanSpace ℝ (Fin n) → ℝ := fun x => η x * w x * ρ x
  let s : EuclideanSpace ℝ (Fin n) → ℝ := fun x => w x * L η x * ρ x
  let b : EuclideanSpace ℝ (Fin n) → ℝ := fun x => |η x + L η x| * ρ x

  have hq : 0 < q := mul_pos (by norm_num) (pow_pos hK 2)
  have hρ : Continuous ρ := Real.continuous_exp.comp hu.continuous.neg
  have hρ0 (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ ρ x :=
    (Real.exp_pos (-u x)).le
  have hwreg : ContDiff ℝ 1 w ∧ LipschitzWith (4 * G) (gradient w) :=
    FunctionalInequalities.Analysis.centeredDifference_contDiff_lipschitz_gradient_readable hu hG h
  obtain ⟨hw1, hwG⟩ := hwreg
  have hbounds : (∀ x, 0 ≤ w x ∧ w x ≤ C) ∧ 0 ≤ C :=
    FunctionalInequalities.Analysis.centeredDifference_nonneg_le_readable hconv h hw

  have hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)) := by
    filter_upwards [hdata] with x hx
    rw [← hx.2.1, Real.exp_log hx.1.det_pos]

  have hie : Integrable e (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    FunctionalInequalities.Analysis.integrable_hessian_increment_energy_readable hu.continuous hG hη.continuous hηc h
  have higen :
      Integrable p (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      Integrable s (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      Integrable b (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    FunctionalInequalities.Analysis.integrable_weak_generator_densities_readable hu.continuous hG hV hF.continuous
      hdet hw1.continuous hwG hη hηc
  obtain ⟨hip, his, hib⟩ := higen
  have hit : Integrable t (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    ((hη.continuous.mul hw1.continuous).mul hρ).integrable_of_hasCompactSupport
      (hηc.mul_right.mul_right)

  have hswap : (∫ x, p x) = ∫ x, s x :=
    (FunctionalInequalities.Analysis.integral_mul_generator_eq_neg_energy_readable hu hG hV hF hdet hw1 hwG hη hηc).trans
      (FunctionalInequalities.Analysis.integral_mul_generator_eq_neg_energy_prime_readable hu hG hV hF hdet hw1 hwG hη hηc).symm
  have hsum : (∫ x, p x + t x) = ∫ x, t x + s x := by
    rw [integral_add hip hit, integral_add hit his, hswap]
    exact add_comm _ _

  have hcoerc := FunctionalInequalities.Analysis.ae_hessian_increment_le_generator_readable
    hu hG (hV.differentiable one_ne_zero) hVc hdata h
  have hpoint :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        e x ≤ q * (p x + t x) := by
    filter_upwards [hcoerc] with x hx
    have hxdiv : E x / q ≤ L w x + w x := hx
    have hxmul : E x ≤ (L w x + w x) * q :=
      (div_le_iff₀ hq).mp hxdiv
    calc
      e x = (η x * ρ x) * E x := by
        dsimp only [e]
        ring
      _ ≤ (η x * ρ x) * ((L w x + w x) * q) :=
        mul_le_mul_of_nonneg_left hxmul (mul_nonneg (hη0 x) (hρ0 x))
      _ = q * (p x + t x) := by
        dsimp only [p, t]
        ring

  have hbound : (∫ x, t x + s x) ≤ C * ∫ x, b x := by
    calc
      (∫ x, t x + s x) ≤ ∫ x, C * b x := by
        apply integral_mono_ae (hit.add his) (hib.const_mul C)
        apply Filter.Eventually.of_forall
        intro x
        have hscalar : w x * (η x + L η x) ≤ C * |η x + L η x| :=
          (mul_le_mul_of_nonneg_left (le_abs_self (η x + L η x))
            (hbounds.1 x).1).trans
            (mul_le_mul_of_nonneg_right (hbounds.1 x).2
              (abs_nonneg (η x + L η x)))
        calc
          t x + s x = (w x * (η x + L η x)) * ρ x := by
            dsimp only [t, s]
            ring
          _ ≤ (C * |η x + L η x|) * ρ x :=
            mul_le_mul_of_nonneg_right hscalar (hρ0 x)
          _ = C * b x := by
            dsimp only [b]
            ring
      _ = C * ∫ x, b x := integral_const_mul C b

  change (∫ x, e x) ≤ q * C * ∫ x, b x
  calc
    (∫ x, e x) ≤ ∫ x, q * (p x + t x) :=
      integral_mono_ae hie ((hip.add hit).const_mul q) hpoint
    _ = q * ∫ x, p x + t x :=
      integral_const_mul q (fun x => p x + t x)
    _ = q * ∫ x, t x + s x := congrArg (fun z : ℝ => q * z) hsum
    _ ≤ q * (C * ∫ x, b x) :=
      mul_le_mul_of_nonneg_left hbound hq.le
    _ = q * C * ∫ x, b x := by ring
