-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_bv_stochastic_core_universal_refuted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:40:31.692203+00:00
-- url     : https://prove2.me/submissions/a12b9a98-1db0-400f-8a09-9411b12d5a74

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a06_bv_finite_activity_standing_source_exists
import Theorems.Thm_AvramDividend_Classical_avram_a06_bv_original_assumptions_counterexample
set_option pp.explicit true
set_option pp.fullNames true

set_option pp.universes true
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
universe u
theorem solution : ¬ (∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (T : ℝ) (hT : 0 ≤ T), (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T, ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x)) := by
  classical
  intro hUniversal
  obtain ⟨P0, F0, X0, hStand0, hBV0, hFinite0⟩ :=
    avram_a06_bv_finite_activity_standing_source_exists
  let ΩU := ULift.{u} ((ℕ → ℝ) × (ℕ → ℝ))
  let PU : Measure ΩU := Measure.map ULift.up P0
  letI : IsProbabilityMeasure P0 := X0.isProbability
  letI : IsProbabilityMeasure PU := Measure.isProbabilityMeasure_map measurable_up.aemeasurable
  have hMap : Measure.map (ULift.down : ΩU → ((ℕ → ℝ) × (ℕ → ℝ))) PU = P0 := by
    rw [show PU = Measure.map ULift.up P0 from rfl, Measure.map_map measurable_down measurable_up]
    change Measure.map id P0 = P0
    exact Measure.map_id
  let FU : Filtration ℝ≥0 (inferInstance : MeasurableSpace ΩU) :=
    ⟨fun t => MeasurableSpace.comap (ULift.down : ΩU → ((ℕ → ℝ) × (ℕ → ℝ))) (F0 t),
      (by intro s t hst; exact MeasurableSpace.comap_mono (F0.mono hst)),
      (by
        intro t
        have hc : MeasurableSpace.comap (ULift.down : ΩU → ((ℕ → ℝ) × (ℕ → ℝ))) (F0 t) ≤ MeasurableSpace.comap (ULift.down : ΩU → ((ℕ → ℝ) × (ℕ → ℝ))) (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))) := MeasurableSpace.comap_mono (F0.le t)
        exact hc.trans (measurable_iff_comap_le.mp measurable_down))⟩
  have hMeas0 (t : ℝ≥0) : Measurable (X0.X t) := (X0.adapted t).mono (F0.le t) le_rfl
  have hMeasU (t : ℝ≥0) : Measurable (fun ω : ΩU => X0.X t ω.down) := (hMeas0 t).comp measurable_down
  have hMass (S : Set ((ℕ → ℝ) × (ℕ → ℝ))) (hS : MeasurableSet S) : PU ((ULift.down : ΩU → ((ℕ → ℝ) × (ℕ → ℝ))) ⁻¹' S) = P0 S :=
    (Measure.map_apply measurable_down hS).symm.trans
      (congrArg (fun m : Measure ((ℕ → ℝ) × (ℕ → ℝ)) => m S) hMap)
  have hLaw (f : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ) (hf : Measurable f) : Measure.map (fun ω : ΩU => f ω.down) PU = Measure.map f P0 :=
    (Measure.map_map hf measurable_down).symm.trans
      (congrArg (fun m : Measure ((ℕ → ℝ) × (ℕ → ℝ)) => Measure.map f m) hMap)
  have hAdapt : Adapted FU (fun t (ω : ΩU) => X0.X t ω.down) :=
    fun t => (X0.adapted t).comp (measurable_iff_comap_le.mpr le_rfl)
  have hIndep (s t : ℝ≥0) (hst : s ≤ t) : Indep (MeasurableSpace.comap (fun ω : ΩU => X0.X t ω.down - X0.X s ω.down) inferInstance) (FU s) PU := by
    have hp : Indep (MeasurableSpace.comap ULift.down (MeasurableSpace.comap (fun ω : ((ℕ → ℝ) × (ℕ → ℝ)) => X0.X t ω - X0.X s ω) inferInstance)) (MeasurableSpace.comap ULift.down (F0 s)) PU := by
      apply (Indep_iff _ _ PU).2
      intro A B hA hB
      obtain ⟨A0, hA0, rfl⟩ := (MeasurableSpace.measurableSet_comap).1 hA
      obtain ⟨B0, hB0, rfl⟩ := (MeasurableSpace.measurableSet_comap).1 hB
      have h0' := (Indep_iff _ _ P0).1 (X0.indepIncrements s t hst) A0 B0 hA0 hB0
      have hA0' : MeasurableSet A0 := (measurable_iff_comap_le.mp ((hMeas0 t).sub (hMeas0 s))) A0 hA0
      have hB0' : MeasurableSet B0 := (F0.le s) B0 hB0
      change PU (ULift.down ⁻¹' (A0 ∩ B0)) = PU (ULift.down ⁻¹' A0) * PU (ULift.down ⁻¹' B0)
      rw [hMass (A0 ∩ B0) (hA0'.inter hB0'), hMass A0 hA0', hMass B0 hB0']
      exact h0'
    simpa only [MeasurableSpace.comap_comp, Function.comp_def] using hp
  have hStat (s t : ℝ≥0) (hst : s ≤ t) :
      IdentDistrib (fun ω : ΩU => X0.X t ω.down - X0.X s ω.down)
        (fun ω : ΩU => X0.X (t - s) ω.down) PU PU :=
    ⟨((hMeasU t).sub (hMeasU s)).aemeasurable,
      (hMeasU (t - s)).aemeasurable,
      ((hLaw (fun ω0 : ((ℕ → ℝ) × (ℕ → ℝ)) => X0.X t ω0 - X0.X s ω0)
        ((hMeas0 t).sub (hMeas0 s))).trans
        ((X0.stationaryIncrements s t hst).map_eq)).trans
        (hLaw (X0.X (t - s)) (hMeas0 (t - s))).symm⟩
  have hLap (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) : Integrable (fun ω : ΩU => Real.exp (θ * X0.X t ω.down)) PU ∧ (∫ ω : ΩU, Real.exp (θ * X0.X t ω.down) ∂PU) = Real.exp ((t : ℝ) * laplaceExponent X0.c X0.σ X0.ν θ) := by
    obtain ⟨hI, hE⟩ := X0.laplace t θ hθ
    have hsm : AEStronglyMeasurable (fun ω0 : ((ℕ → ℝ) × (ℕ → ℝ)) => Real.exp (θ * X0.X t ω0)) (Measure.map ULift.down PU) := by simpa [hMap] using hI.aestronglyMeasurable
    refine ⟨(integrable_map_measure hsm measurable_down.aemeasurable).mp
      (by simpa [hMap] using hI), ?_⟩
    calc
      (∫ ω : ΩU, Real.exp (θ * X0.X t ω.down) ∂PU) =
        ∫ ω0 : ((ℕ → ℝ) × (ℕ → ℝ)), Real.exp (θ * X0.X t ω0) ∂(Measure.map ULift.down PU) := (integral_map measurable_down.aemeasurable hsm).symm
      _ = _ := by rw [hMap]; exact hE
  let XU : SpectrallyNegativeLevy PU FU := {
    X := fun t ω => X0.X t ω.down
    c := X0.c, σ := X0.σ, ν := X0.ν
    isProbability := inferInstance, σ_nonneg := X0.σ_nonneg
    ν_Ici := X0.ν_Ici, ν_integrable := X0.ν_integrable
    X_zero := fun ω => X0.X_zero ω.down, rightCont := fun ω t => X0.rightCont ω.down t
    leftLim := fun ω t ht => X0.leftLim ω.down t ht
    noPosJumps := fun ω t l ht hl => X0.noPosJumps ω.down t l ht hl
    adapted := hAdapt, indepIncrements := hIndep, stationaryIncrements := hStat, laplace := hLap }
  have hBVU : XU.BoundedVariation := hBV0
  have hFiniteU : XU.ν (Iio (0 : ℝ)) < ⊤ := hFinite0
  have hIntU : Integrable (XU.X 1) PU :=
    (integrable_map_measure (by simpa [hMap] using hStand0.2.1.aestronglyMeasurable)
      measurable_down.aemeasurable).mp (by simpa [hMap] using hStand0.2.1)
  have hStandU : XU.Standing := ⟨fun hMonoU => hStand0.1 hMonoU, hIntU, hStand0.2.2⟩
  obtain ⟨w, C, x, D, T, hCont, hNeg, hSmooth, hGen, hGrad,
      hxc, hD, hNN, hJump, hT, hBad⟩ :=
    avram_a06_bv_original_assumptions_counterexample
      XU hStandU hBVU hFiniteU 1 (by norm_num)
  exact hBad (hUniversal (Ω := ΩU) (P := PU) (𝓕 := FU)
    XU hStandU hBVU 1 (by norm_num) w C
    hCont hNeg hSmooth hGen hGrad x hxc D hD hNN hJump T hT)
