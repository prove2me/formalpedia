-- Prove2me | solution 1 for FunctionalInequalities.Probability.Diffusion.IsDiffusion.dynkin_transport_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:29:09.44888+00:00
-- url     : https://prove2.me/submissions/ae9646e4-dcb5-4b17-981c-d268a181ee81

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Transport
import Theorems.Thm_FunctionalInequalities_Probability_Diffusion_IsDiffusion_dynkin_readable
import Theorems.Thm_FunctionalInequalities_Probability_Diffusion_diffusionGenerator_transport_readable

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Diffusion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito
section Transport
variable {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {N d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ}
section DynkinTransport
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
/-- **Dynkin's identity in a finite-dimensional state space**: if the coordinates `Φ ∘ Y` of a `V`-valued process
form a diffusion with the transported coefficients, the coefficients on `V` being continuous with compact support,
then for every `C²` `F : V → ℝ`, `F(Y_T)` is integrable and `E F(Y_T) − F(x₀) = E ∫₀ᵀ 𝓛F(Y_s) ds` with the
coordinate-free generator on `V`. -/
theorem solution (Φ : V ≃L[ℝ] (Fin N → ℝ))
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {b : V → V} {σ : V → Fin d → V} {x₀ : V}
    (hbc : Continuous b) (hσc : ∀ k, Continuous fun x => σ x k)
    (hbs : HasCompactSupport b) (hσs : ∀ k, HasCompactSupport fun x => σ x k)
    {Y : ℝ → Ω → V}
    (h : FunctionalInequalities.Probability.Diffusion.IsDiffusion W ℱ hW (FunctionalInequalities.Probability.Diffusion.transportDrift Φ b) (FunctionalInequalities.Probability.Diffusion.transportNoise Φ σ) (Φ x₀) (fun t ω => Φ (Y t ω)))
    {F : V → ℝ} (hF : ContDiff ℝ 2 F) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun ω => F (Y T ω)) P ∧
      ∫ ω, F (Y T ω) ∂P - F x₀ =
        ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, FunctionalInequalities.Probability.Diffusion.diffusionGenerator b σ F (Y s ω) ∂volume ∂P := by
  classical
  have hbc' : Continuous (FunctionalInequalities.Probability.Diffusion.transportDrift Φ b) := by
    change Continuous (fun y => Φ (b (Φ.symm y)))
    exact Φ.continuous.comp (hbc.comp Φ.symm.continuous)
  have hσc' : ∀ k, Continuous fun y => FunctionalInequalities.Probability.Diffusion.transportNoise Φ σ y k := by
    intro k
    change Continuous (fun y => Φ (σ (Φ.symm y) k))
    exact Φ.continuous.comp ((hσc k).comp Φ.symm.continuous)
  have hbs' : HasCompactSupport (FunctionalInequalities.Probability.Diffusion.transportDrift Φ b) := by
    change HasCompactSupport (fun y => Φ (b (Φ.symm y)))
    have h₁ : HasCompactSupport (Φ ∘ b) :=
      hbs.comp_left (g := Φ) Φ.map_zero
    have h₂ := h₁.comp_homeomorph Φ.symm.toHomeomorph
    have he :
        ((Φ ∘ b) ∘ ⇑Φ.symm.toHomeomorph) =
          (fun y => Φ (b (Φ.symm y))) := by
      funext y
      rfl
    rw [he] at h₂
    exact h₂
  have hσs' : ∀ k, HasCompactSupport fun y => FunctionalInequalities.Probability.Diffusion.transportNoise Φ σ y k := by
    intro k
    change HasCompactSupport (fun y => Φ (σ (Φ.symm y) k))
    have h₁ : HasCompactSupport (Φ ∘ fun x => σ x k) :=
      (hσs k).comp_left (g := Φ) Φ.map_zero
    have h₂ := h₁.comp_homeomorph Φ.symm.toHomeomorph
    have he :
        ((Φ ∘ fun x => σ x k) ∘ ⇑Φ.symm.toHomeomorph) =
          (fun y => Φ (σ (Φ.symm y) k)) := by
      funext y
      rfl
    rw [he] at h₂
    exact h₂
  have hF' : ContDiff ℝ 2 (F ∘ Φ.symm) :=
    hF.comp (ContinuousLinearEquiv.contDiff Φ.symm)
  obtain ⟨hInt, hEq⟩ :=
    FunctionalInequalities.Probability.Diffusion.IsDiffusion.dynkin_readable hℱ0 hnull hbc' hσc' hbs' hσs' h hF' hT
  refine ⟨?_, ?_⟩
  · simpa only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] using hInt
  · calc
      ∫ ω, F (Y T ω) ∂P - F x₀ =
          ∫ ω, (F ∘ Φ.symm) ((fun t ω => Φ (Y t ω)) T ω) ∂P -
            (F ∘ Φ.symm) (Φ x₀) := by
              simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
      _ = ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T,
          FunctionalInequalities.Probability.Diffusion.diffusionGenerator (FunctionalInequalities.Probability.Diffusion.transportDrift Φ b) (FunctionalInequalities.Probability.Diffusion.transportNoise Φ σ)
            (F ∘ Φ.symm) ((fun t ω => Φ (Y t ω)) s ω) ∂volume ∂P := hEq
      _ = ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T,
          FunctionalInequalities.Probability.Diffusion.diffusionGenerator b σ F (Y s ω) ∂volume ∂P := by
            apply integral_congr_ae
            filter_upwards [] with ω
            apply integral_congr_ae
            filter_upwards [] with s
            simpa only [Function.comp_apply] using
              (FunctionalInequalities.Probability.Diffusion.diffusionGenerator_transport_readable Φ b σ F (Y s ω))
