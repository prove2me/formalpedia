-- Prove2me | solution 1 for FiniteEnergyPlane.hadamard_integral_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-30T11:10:50.375509+00:00
-- url     : https://prove2.me/submissions/bc9f62b8-1689-4747-bfc4-3bb02856aa60

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_ContWeatherall_contDiff_parametric_intervalIntegral

open scoped ContDiff

namespace FiniteEnergyPlane

theorem hadamard_integral_fderiv_aux {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (f : X × E → F) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : X × E => ∫ θ in (0 : ℝ)..1, fderiv ℝ (fun a => f (p.1, a)) (θ • p.2)) ∧
      ∀ p : X × E, f p = f (p.1, 0) +
        (∫ θ in (0 : ℝ)..1, fderiv ℝ (fun a => f (p.1, a)) (θ • p.2)) p.2 := by
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hD2 : ∀ (x : X) (a : E), fderiv ℝ (fun a => f (x, a)) a =
      (fderiv ℝ f (x, a)).comp (ContinuousLinearMap.inr ℝ X E) := by
    intro x a
    exact ((hfd (x, a)).hasFDerivAt.comp a (hasFDerivAt_prodMk_right x a)).fderiv
  have hF : ContDiff ℝ ∞ (Function.uncurry
      (fun (p : X × E) (θ : ℝ) => fderiv ℝ (fun a => f (p.1, a)) (θ • p.2))) := by
    have e : Function.uncurry (fun (p : X × E) (θ : ℝ) => fderiv ℝ (fun a => f (p.1, a)) (θ • p.2))
        = fun q : (X × E) × ℝ =>
          (fderiv ℝ f (q.1.1, q.2 • q.1.2)).comp (ContinuousLinearMap.inr ℝ X E) := by
      funext q; exact hD2 _ _
    rw [e]
    exact ((hf.fderiv_right (by simp)).comp
      (contDiff_fst.fst.prodMk (contDiff_snd.smul contDiff_fst.snd))).clm_comp contDiff_const
  refine ⟨ContWeatherall.contDiff_parametric_intervalIntegral hF 0 1, fun p => ?_⟩
  obtain ⟨x, a⟩ := p
  have hderiv : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => f (x, θ • a))
      (fderiv ℝ (fun a => f (x, a)) (θ • a) a) θ := by
    intro θ
    have h1 : HasDerivAt (fun θ : ℝ => θ • a) a θ := by
      simpa using (hasDerivAt_id θ).smul_const a
    have hg : DifferentiableAt ℝ (fun b => f (x, b)) (θ • a) :=
      (hfd _).comp _ (differentiableAt_const _ |>.prodMk differentiableAt_id)
    exact hg.hasFDerivAt.comp_hasDerivAt θ h1
  have hcont : Continuous (fun θ : ℝ => fderiv ℝ (fun a => f (x, a)) (θ • a)) :=
    hF.continuous.comp ((continuous_const : Continuous fun _ : ℝ => (x, a)).prodMk continuous_id)
  have hint : IntervalIntegrable (fun θ : ℝ => fderiv ℝ (fun a => f (x, a)) (θ • a))
      MeasureTheory.volume 0 1 := hcont.intervalIntegrable 0 1
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hderiv θ)
    ((hcont.clm_apply continuous_const).intervalIntegrable 0 1)
  simp only
  rw [ContinuousLinearMap.intervalIntegral_apply hint, hI]
  simp

end FiniteEnergyPlane

open FiniteEnergyPlane

open scoped ContDiff

theorem solution {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (f : X × E → F) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : X × E => ∫ θ in (0 : ℝ)..1, fderiv ℝ (fun a => f (p.1, a)) (θ • p.2)) ∧
      ∀ p : X × E, f p = f (p.1, 0) +
        (∫ θ in (0 : ℝ)..1, fderiv ℝ (fun a => f (p.1, a)) (θ • p.2)) p.2 :=
  hadamard_integral_fderiv_aux f hf
