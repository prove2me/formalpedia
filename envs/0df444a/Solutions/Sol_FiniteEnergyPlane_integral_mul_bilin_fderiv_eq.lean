-- Prove2me | solution 1 for FiniteEnergyPlane.integral_mul_bilin_fderiv_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-23T16:07:42.53429+00:00
-- url     : https://prove2.me/submissions/d3a086f7-6e66-4556-a1f9-19bd2cb1326c

import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff

/-- Let `σ` be an antisymmetric continuous bilinear form on `F`, `u` a `C²` map on an open set
`U ⊆ ℂ`, `q ∈ F`, and `ψ` a real `C¹` function with compact support in `U`. Writing
`∂ₛ = D(·) 1`, `∂ₜ = D(·) i`,
`∫ ψ σ(∂ₛu, ∂ₜu) = -½ ∫ (∂ₛψ σ(u - q, ∂ₜu) - ∂ₜψ σ(u - q, ∂ₛu))`. -/
theorem integral_mul_bilin_fderiv_eq_aux {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (σ : F →L[ℝ] F →L[ℝ] ℝ) (hσ : ∀ v w, σ v w = -σ w v) {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ → F} (hu : ContDiffOn ℝ 2 u U) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) (q : F) :
    ∫ z, ψ z * σ (fderiv ℝ u z 1) (fderiv ℝ u z Complex.I) =
      -(1 / 2) * ∫ z, (fderiv ℝ ψ z 1 * σ (u z - q) (fderiv ℝ u z Complex.I) -
        fderiv ℝ ψ z Complex.I * σ (u z - q) (fderiv ℝ u z 1)) := by
  -- integrability of `χ * G` for `χ` supported in `tsupport ψ` and `G` continuous on `U`
  have hint : ∀ χ G : ℂ → ℝ, Continuous χ → tsupport χ ⊆ tsupport ψ → ContinuousOn G U →
      Integrable (fun z => χ z * G z) := by
    intro χ G hχ hχs hG
    have hcont : Continuous (fun z => χ z * G z) := by
      rw [continuous_iff_continuousAt]
      intro z
      by_cases hz : z ∈ U
      · exact hχ.continuousAt.mul (hG.continuousAt (hU.mem_nhds hz))
      · have hz' : z ∉ tsupport χ := fun h => hz (hψU (hχs h))
        have h0 : χ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 hz'
        have h1 : (fun z => χ z * G z) =ᶠ[𝓝 z] fun _ => 0 := by
          filter_upwards [h0] with y hy
          simp [hy]
        exact (continuousAt_congr h1).2 continuousAt_const
    have hcs : HasCompactSupport χ := hψc.mono' (subset_tsupport χ |>.trans hχs)
    exact hcont.integrable_of_hasCompactSupport (hcs.mul_right)
  have hψ' : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv one_ne_zero
  have hψs : ∀ v : ℂ, tsupport (fun z => fderiv ℝ ψ z v) ⊆ tsupport ψ := by
    intro v
    refine (closure_mono ?_).trans (tsupport_fderiv_subset (𝕜 := ℝ) (f := ψ))
    intro z hz
    contrapose! hz
    simp only [Function.notMem_support] at hz ⊢
    simp [hz]
  -- the auxiliary functions `G v z = σ (u z - q) (∂ᵥ u z)`
  set G : ℂ → ℂ → ℝ := fun v z => σ (u z - q) (fderiv ℝ u z v) with hGdef
  have hu1 : ContDiffOn ℝ 1 (fderiv ℝ u) U := hu.fderiv_of_isOpen hU (by norm_num)
  have hGc : ∀ v, ContDiffOn ℝ 1 (G v) U := by
    intro v
    have h1 : ContDiffOn ℝ 1 (fun z => σ (u z - q)) U :=
      σ.contDiff.comp_contDiffOn ((hu.of_le (by norm_num)).sub contDiffOn_const)
    have h2 : ContDiffOn ℝ 1 (fun z => fderiv ℝ u z v) U := hu1.clm_apply contDiffOn_const
    exact h1.clm_apply h2
  have hGd : ∀ v, ∀ z ∈ U, HasFDerivAt (G v) (fderiv ℝ (G v) z) z := fun v z hz =>
    (((hGc v).differentiableOn one_ne_zero) z hz |>.differentiableAt (hU.mem_nhds hz)).hasFDerivAt
  have hGcont : ∀ v, ContinuousOn (G v) U := fun v => (hGc v).continuousOn
  have hG'cont : ∀ v w, ContinuousOn (fun z => fderiv ℝ (G v) z w) U := fun v w =>
    ((hGc v).continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  -- integration by parts in the directions `1` and `i`
  have ibp : ∀ v w : ℂ, ∫ z, ψ z * fderiv ℝ (G v) z w = -∫ z, fderiv ℝ ψ z w * G v z := by
    intro v w
    have := integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable
      (μ := volume) (f := ψ) (f' := fderiv ℝ ψ) (g := G v) (g' := fun z => fderiv ℝ (G v) z)
      (v := w) (B := ContinuousLinearMap.mul ℝ ℝ)
      (hint _ _ (hψ'.clm_apply continuous_const) (hψs w) (hGcont v))
      (hint _ _ hψ.continuous subset_rfl (hG'cont v w))
      (hint _ _ hψ.continuous subset_rfl (hGcont v))
      (fun x _ => (hψ.differentiable one_ne_zero x).hasFDerivAt)
      (fun x hx => hGd v x (hψU hx))
    simpa using this
  -- the pointwise identity `∂ₛ G i - ∂ₜ G 1 = 2 σ(∂ₛu, ∂ₜu)` on `U`
  have hpt : ∀ z ∈ U, fderiv ℝ (G Complex.I) z 1 - fderiv ℝ (G 1) z Complex.I =
      2 * σ (fderiv ℝ u z 1) (fderiv ℝ u z Complex.I) := by
    intro z hz
    have hz2 : ContDiffAt ℝ 2 u z := hu.contDiffAt (hU.mem_nhds hz)
    have hDu : HasFDerivAt u (fderiv ℝ u z) z :=
      (hz2.differentiableAt (by norm_num)).hasFDerivAt
    have hD2 : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) z) z :=
      ((hz2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
    have hsymm : IsSymmSndFDerivAt ℝ u z := hz2.isSymmSndFDerivAt (by simp)
    have hc : HasFDerivAt (fun y => σ (u y - q)) (σ.comp (fderiv ℝ u z)) z :=
      σ.hasFDerivAt.comp z (hDu.sub_const q)
    have hdI : HasFDerivAt (G Complex.I) _ z :=
      hc.clm_apply (hD2.clm_apply (hasFDerivAt_const Complex.I z))
    have hd1 : HasFDerivAt (G 1) _ z := hc.clm_apply (hD2.clm_apply (hasFDerivAt_const 1 z))
    rw [hdI.fderiv, hd1.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply, map_zero, zero_add]
    rw [hsymm 1 Complex.I, hσ (fderiv ℝ u z Complex.I) (fderiv ℝ u z 1)]
    ring
  -- assemble
  have hL : (fun z => ψ z * σ (fderiv ℝ u z 1) (fderiv ℝ u z Complex.I)) =
      fun z => (1 / 2) * (ψ z * fderiv ℝ (G Complex.I) z 1 - ψ z * fderiv ℝ (G 1) z Complex.I) := by
    funext z
    by_cases hz : z ∈ U
    · rw [← mul_sub, hpt z hz]; ring
    · have hz' : ψ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hψU h))
      simp [hz']
  rw [hL, integral_const_mul, integral_sub (hint _ _ hψ.continuous subset_rfl (hG'cont _ _))
    (hint _ _ hψ.continuous subset_rfl (hG'cont _ _)), ibp, ibp,
    integral_sub (hint _ _ (hψ'.clm_apply continuous_const) (hψs 1) (hGcont _))
      (hint _ _ (hψ'.clm_apply continuous_const) (hψs Complex.I) (hGcont _))]
  ring

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff

theorem solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (σ : F →L[ℝ] F →L[ℝ] ℝ) (hσ : ∀ v w, σ v w = -σ w v) {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ → F} (hu : ContDiffOn ℝ 2 u U) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) (q : F) :
    ∫ z, ψ z * σ (fderiv ℝ u z 1) (fderiv ℝ u z Complex.I) =
      -(1 / 2) * ∫ z, (fderiv ℝ ψ z 1 * σ (u z - q) (fderiv ℝ u z Complex.I) -
        fderiv ℝ ψ z Complex.I * σ (u z - q) (fderiv ℝ u z 1)) :=
  integral_mul_bilin_fderiv_eq_aux σ hσ hU hu hψ hψc hψU q
