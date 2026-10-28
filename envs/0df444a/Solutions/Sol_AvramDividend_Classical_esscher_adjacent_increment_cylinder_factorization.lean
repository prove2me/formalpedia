-- Prove2me | solution 1 for AvramDividend.Classical.esscher_adjacent_increment_cylinder_factorization
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T14:59:50.850017+00:00
-- url     : https://prove2.me/submissions/720413de-5085-43e2-ab80-b606d2498ae8

import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Process.Filtration
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Tilted adjacent increment cylinders factor by the original Lévy independence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (s u : ℝ≥0)
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕 s) A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X (s + u) ω -
        (s + u : ℝ) * X.ψ θ))))
      (A ∩ (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ)))) A *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
      ((X.X u) ⁻¹' B) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : Ω → ℝ := fun ω => X.X (s + u) ω - X.X s ω
  let Ms : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal
    (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ))
  let K : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal
    (Real.exp (θ * x - (u : ℝ) * X.ψ θ))
  let F : Ω → ℝ≥0∞ := A.indicator Ms
  let R : ℝ → ℝ≥0∞ := B.indicator K
  have hst : s ≤ s + u :=
    le_add_of_nonneg_right (show 0 ≤ u from zero_le)
  have hAm : MeasurableSet A := 𝓕.le s _ hA
  have hXs : Measurable (X.X s) := (X.adapted s).mono (𝓕.le s) le_rfl
  have hXt : Measurable (X.X (s + u)) := (X.adapted (s + u)).mono (𝓕.le (s + u)) le_rfl
  have hXu : Measurable (X.X u) := (X.adapted u).mono (𝓕.le u) le_rfl
  have hY : Measurable Y := by
    dsimp [Y]
    exact hXt.sub hXs
  have hMsFil : Measurable[𝓕 s] Ms := by
    dsimp [Ms]
    exact ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        ((measurable_const.mul (X.adapted s)).sub measurable_const))
  have hFFil : Measurable[𝓕 s] F := hMsFil.indicator hA
  have hF : Measurable F := hFFil.mono (𝓕.le s) le_rfl
  have hK : Measurable K := by
    dsimp [K]
    exact ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        ((measurable_const.mul measurable_id).sub measurable_const))
  have hR : Measurable R := hK.indicator hB
  have hIndep0 : Indep
      (MeasurableSpace.comap Y inferInstance) (𝓕 s) P := by
    simpa only [Y] using X.indepIncrements s (s + u) hst
  have hSmall : MeasurableSpace.comap F inferInstance ≤ 𝓕 s :=
    hFFil.comap_le
  have hPair : IndepFun F Y P :=
    (IndepFun_iff_Indep F Y P).2
      ((indep_of_indep_of_le_right hIndep0 hSmall).symm)
  have hIndep : IndepFun F (R ∘ Y) P :=
    hPair.comp measurable_id hR
  have hFactor :
      (∫⁻ ω, F ω * R (Y ω) ∂P) =
        (∫⁻ ω, F ω ∂P) * (∫⁻ ω, R (Y ω) ∂P) := by
    simpa only [Pi.mul_apply, Function.comp_apply] using
      (lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
        hF (hR.comp hY) hIndep)
  have hYLaw : Measure.map Y P = Measure.map (X.X u) P := by
    simpa [Y] using (X.stationaryIncrements s (s + u) hst).map_eq
  have hRLaw :
      (∫⁻ ω, R (Y ω) ∂P) =
        (∫⁻ ω, R (X.X u ω) ∂P) := by
    rw [← lintegral_map hR hY, ← lintegral_map hR hXu, hYLaw]
  have hBu : MeasurableSet ((X.X u) ⁻¹' B) := hB.preimage hXu
  have hFmeasure : (∫⁻ ω, F ω ∂P) = (P.withDensity Ms) A := by
    rw [withDensity_apply _ hAm]
    exact lintegral_indicator hAm Ms
  have hRpoint : (fun ω => R (X.X u ω)) =
      ((X.X u) ⁻¹' B).indicator (fun ω => K (X.X u ω)) := by
    funext ω
    by_cases hb : X.X u ω ∈ B
    · simp [R, Set.indicator, hb]
    · simp [R, Set.indicator, hb]
  have hGmeasure :
      (∫⁻ ω, R (Y ω) ∂P) =
        (P.withDensity (fun ω => K (X.X u ω))) ((X.X u) ⁻¹' B) := by
    calc
      (∫⁻ ω, R (Y ω) ∂P) =
          (∫⁻ ω, R (X.X u ω) ∂P) := hRLaw
      _ = (∫⁻ ω, ((X.X u) ⁻¹' B).indicator
          (fun ω => K (X.X u ω)) ω ∂P) := by
            rw [← hRpoint]
      _ = (∫⁻ ω in ((X.X u) ⁻¹' B), K (X.X u ω) ∂P) :=
            lintegral_indicator hBu _
      _ = (P.withDensity (fun ω => K (X.X u ω))) ((X.X u) ⁻¹' B) :=
            (withDensity_apply _ hBu).symm
  have hWeight (ω : Ω) :
      ENNReal.ofReal (Real.exp (θ * X.X (s + u) ω -
        (s + u : ℝ) * X.ψ θ)) = Ms ω * K (Y ω) := by
    have hsplit :
        Real.exp (θ * X.X (s + u) ω - (s + u : ℝ) * X.ψ θ) =
        Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ) *
        Real.exp (θ * (Y ω) - (u : ℝ) * X.ψ θ) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      dsimp [Y]
      ring
    rw [hsplit]
    exact ENNReal.ofReal_mul (Real.exp_nonneg _)
  have hEvent : MeasurableSet (A ∩ Y ⁻¹' B) :=
    hAm.inter (hB.preimage hY)
  have hPoint (ω : Ω) :
      (A ∩ Y ⁻¹' B).indicator
        (fun ω => ENNReal.ofReal (Real.exp
          (θ * X.X (s + u) ω - (s + u : ℝ) * X.ψ θ))) ω =
        F ω * R (Y ω) := by
    by_cases ha : ω ∈ A
    · by_cases hb : Y ω ∈ B
      · simp [F, R, Set.indicator, ha, hb, hWeight ω]
      · simp [F, R, Set.indicator, ha, hb]
    · simp [F, R, Set.indicator, ha]
  calc
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X (s + u) ω - (s + u : ℝ) * X.ψ θ))))
        (A ∩ Y ⁻¹' B) =
        (∫⁻ ω, (A ∩ Y ⁻¹' B).indicator
          (fun ω => ENNReal.ofReal (Real.exp
            (θ * X.X (s + u) ω - (s + u : ℝ) * X.ψ θ))) ω ∂P) := by
      rw [withDensity_apply _ hEvent]
      exact (lintegral_indicator hEvent _).symm
    _ = (∫⁻ ω, F ω * R (Y ω) ∂P) := by
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall hPoint
    _ = (∫⁻ ω, F ω ∂P) * (∫⁻ ω, R (Y ω) ∂P) := hFactor
    _ = (P.withDensity Ms) A *
        (P.withDensity (fun ω => K (X.X u ω))) ((X.X u) ⁻¹' B) := by
      rw [hFmeasure, hGmeasure]
